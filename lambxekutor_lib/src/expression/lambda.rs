use std::{collections::HashMap, fmt::Display};

use crate::expression::{rlambda, Identifier, RawLambda};

/// AST of desugarred lamda expression
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Lambda {
    Variable { name: usize },
    Abstraction { argument: usize, body: Box<Self> },
    Application { left: Box<Self>, right: Box<Self> },
}

impl Lambda {
    pub fn highest_arg(&self) -> usize {
        match self {
            Lambda::Variable { name } => *name,
            Lambda::Abstraction { argument, body } => (*argument).max(Lambda::highest_arg(body)),
            Lambda::Application { left, right } => Lambda::highest_arg(left).max(Lambda::highest_arg(right)),
        }
    }

    /// Desugars a [`RawLambda`] into a [`Lambda`] and its corresponding [`NamingContext`].
    pub fn desugar(raw_lambda: &RawLambda) -> (Self, NamingContext) {
        fn desugar_inner(raw_lambda: &RawLambda, context: &mut NamingContext) -> Lambda {
            match raw_lambda {
                RawLambda::Variable { name } => Lambda::Variable {
                    name: context.insert(name),
                },
                RawLambda::Abstraction { arguments, body } => {
                    let mut current = desugar_inner(body, context);
                    for argument in arguments.into_iter().rev() {
                        current = Lambda::Abstraction {
                            argument: context.insert(argument),
                            body: Box::new(current),
                        };
                    }
                    current
                }
                RawLambda::Application { left, right } => Lambda::Application {
                    left: Box::new(desugar_inner(left, context)),
                    right: Box::new(desugar_inner(right, context)),
                },
                RawLambda::ChurchNumber { value } => {
                    let f = context.insert(&Identifier::try_new("f").expect("'f' should be a valid identifier"));
                    let x = context.insert(&Identifier::try_new("x").expect("'x' should be a valid identifier"));

                    let mut body = Lambda::Variable { name: x };
                    for _ in 0..*value {
                        body = Lambda::Application {
                            left: Box::new(Lambda::Variable { name: f }),
                            right: Box::new(body),
                        };
                    }

                    Lambda::Abstraction {
                        argument: f,
                        body: Box::new(Lambda::Abstraction {
                            argument: x,
                            body: Box::new(body),
                        }),
                    }
                }
                RawLambda::YCombinator => {
                    // Y = λf. (λx. f (x x)) (λx. f (x x))
                    let f = context.insert(&Identifier::try_new("f").unwrap());
                    let x = context.insert(&Identifier::try_new("x").unwrap());

                    let inner = Lambda::Abstraction {
                        argument: x,
                        body: Box::new(Lambda::Application {
                            left: Box::new(Lambda::Variable { name: f }),
                            right: Box::new(Lambda::Application {
                                left: Box::new(Lambda::Variable { name: x }),
                                right: Box::new(Lambda::Variable { name: x }),
                            }),
                        }),
                    };

                    Lambda::Abstraction {
                        argument: f,
                        body: Box::new(Lambda::Application {
                            left: Box::new(inner.clone()),
                            right: Box::new(inner),
                        }),
                    }
                }
                RawLambda::True => desugar_inner(&rlambda!(lam, t f, rlambda!(var, t)), context),
                RawLambda::False => desugar_inner(&rlambda!(lam, t f, rlambda!(var, f)), context),
                RawLambda::And => desugar_inner(
                    &rlambda!(lam, x y, rlambda!(app, rlambda!(app, rlambda!(var, x), rlambda!(var, y)), rlambda!(var, x))),
                    context,
                ),
                RawLambda::Or => desugar_inner(
                    &rlambda!(lam, x y, rlambda!(app, rlambda!(app, rlambda!(var, x), rlambda!(T)), rlambda!(var, y))),
                    context,
                ),
                RawLambda::Not => desugar_inner(
                    &rlambda!(lam, x t f, rlambda!(app, rlambda!(app, rlambda!(var, x), rlambda!(var, f)), rlambda!(var, t))),
                    context,
                ),
                RawLambda::Zero => desugar_inner(
                    &rlambda!(
                        lam,
                        n,
                        rlambda!(
                            app,
                            rlambda!(app, rlambda!(var, n), rlambda!(lam, x, rlambda!(F))),
                            rlambda!(T)
                        )
                    ),
                    context,
                ),
                RawLambda::Suc => desugar_inner(
                    &rlambda!(lam, n s z, rlambda!(app, rlambda!(var, s), rlambda!(app, rlambda!(app, rlambda!(var, n), rlambda!(var, s)), rlambda!(var, z)))),
                    context,
                ),
                RawLambda::Plus => desugar_inner(
                    &rlambda!(lam, x y s z, rlambda!(app, rlambda!(app, rlambda!(var, x), rlambda!(var, s)), rlambda!(app, rlambda!(app, rlambda!(var, y), rlambda!(var, s)), rlambda!(var, z)))),
                    context,
                ),
                RawLambda::Pred => desugar_inner(
                    &rlambda!(lam, x s z, rlambda!(app, rlambda!(app, rlambda!(app, rlambda!(var, x), rlambda!(lam, f g, rlambda!(app, rlambda!(var, g), rlambda!(app, rlambda!(var, f), rlambda!(var, s))))), rlambda!(lam, g, rlambda!(var, z))), rlambda!(lam, u, rlambda!(var, u)))),
                    context,
                ),
                RawLambda::Minus => desugar_inner(
                    &rlambda!(lam, m n, rlambda!(app, rlambda!(app, rlambda!(var, n), rlambda!(PRED)), rlambda!(var, m))),
                    context,
                ),
                RawLambda::Times => desugar_inner(
                    &rlambda!(lam, x y s, rlambda!(app, rlambda!(var, x), rlambda!(app, rlambda!(var, y), rlambda!(var, s)))),
                    context,
                ),
                RawLambda::Pow => desugar_inner(
                    &rlambda!(lam, x y, rlambda!(app, rlambda!(var, y), rlambda!(var, x))),
                    context,
                ),
                RawLambda::Delta => desugar_inner(
                    &rlambda!(lam, m n, rlambda!(app, rlambda!(app, rlambda!(+), rlambda!(app, rlambda!(app, rlambda!(-), rlambda!(var, m)), rlambda!(var, n))), rlambda!(app, rlambda!(app, rlambda!(-), rlambda!(var, n)), rlambda!(var, m)))),
                    context,
                ),
                RawLambda::Equals => desugar_inner(
                    &rlambda!(lam, m n, rlambda!(app, rlambda!(ZERO), rlambda!(app, rlambda!(app, rlambda!(DELTA), rlambda!(var, m)), rlambda!(var, n)))),
                    context,
                ),
                RawLambda::GreaterThan => desugar_inner(
                    &rlambda!(lam, m n, rlambda!(app, rlambda!(NOT), rlambda!(app, rlambda!(ZERO), rlambda!(app, rlambda!(app, rlambda!(-), rlambda!(var, m)), rlambda!(var, n))))),
                    context,
                ),
                RawLambda::LessThan => desugar_inner(
                    &rlambda!(lam, m n, rlambda!(app, rlambda!(app, rlambda!(>), rlambda!(var, n)), rlambda!(var, m))),
                    context,
                ),
                RawLambda::GreaterEqual => desugar_inner(
                    &rlambda!(lam, m n, rlambda!(app, rlambda!(ZERO), rlambda!(app, rlambda!(app, rlambda!(-), rlambda!(var, n)), rlambda!(var, m)))),
                    context,
                ),
                RawLambda::LessEqual => desugar_inner(
                    &rlambda!(lam, m n, rlambda!(app, rlambda!(ZERO), rlambda!(app, rlambda!(app, rlambda!(-), rlambda!(var, m)), rlambda!(var, n)))),
                    context,
                ),
                RawLambda::Divide => desugar_inner(
                    &rlambda!(
                        lam,
                        n,
                        rlambda!(
                            app,
                            rlambda!(Y),
                            rlambda!(lam, c n m f x,
                                rlambda!(app,
                                    rlambda!(app,
                                        rlambda!(app,
                                            rlambda!(ZERO),
                                            rlambda!(var, d)
                                        ),
                                        rlambda!(app, rlambda!(app, rlambda!(num, 0), rlambda!(var, f)), rlambda!(var, x))
                                    ),
                                    rlambda!(app, rlambda!(var, f), rlambda!(app, rlambda!(app, rlambda!(app, rlambda!(app, rlambda!(var, c), rlambda!(var, d)), rlambda!(var, m)), rlambda!(var, f)), rlambda!(var, x)))
                                )
                            )
                        )
                    ),
                    context,
                ),
            }
        }

        let mut context = NamingContext::empty();
        (desugar_inner(raw_lambda, &mut context), context)
    }
}

impl Default for Lambda {
    fn default() -> Self {
        Self::Variable { name: 0 }
    }
}

/// Helper macro for constructing [`Lambda`]s
#[allow(unused)]
macro_rules! lambda {
    (var, $id:expr) => {
        $crate::expression::Lambda::Variable { name: $id }
    };
    (lam, $id:expr, $body:expr) => {
        $crate::expression::Lambda::Abstraction {
            argument: $id,
            body: Box::new($body),
        }
    };
    (app, $left:expr, $right:expr) => {
        $crate::expression::Lambda::Application {
            left: Box::new($left),
            right: Box::new($right),
        }
    };
}
pub(crate) use lambda;

/// Stores the mapping between variable [`Identifier`]s and `usize` IDs
#[derive(Clone, Debug)]
pub struct NamingContext {
    id_to_identifier: HashMap<usize, Identifier>,
    identifier_to_id: HashMap<Identifier, usize>,
}

impl NamingContext {
    fn empty() -> Self {
        Self {
            id_to_identifier: HashMap::default(),
            identifier_to_id: HashMap::default(),
        }
    }

    fn insert(&mut self, identifier: &Identifier) -> usize {
        if let Some(&id) = self.identifier_to_id.get(&identifier) {
            id
        } else {
            let id = self.id_to_identifier.len();

            self.identifier_to_id.insert(identifier.clone(), id);
            self.id_to_identifier.insert(id, identifier.clone());

            id
        }
    }

    fn get_identifier(&self, id: usize) -> &Identifier {
        self.id_to_identifier
            .get(&id)
            .expect("Identifier should have been pre-filled by bind()")
    }

    fn fill_identifier(&mut self, id: usize) {
        if self.id_to_identifier.contains_key(&id) {
            return;
        }

        let mut attempt_id = id;
        loop {
            let identifier = self.generate_identifier(attempt_id);

            if !self.identifier_to_id.contains_key(&identifier) {
                self.identifier_to_id.insert(identifier.clone(), id);
                self.id_to_identifier.insert(id, identifier.clone());
                return;
            } else {
                attempt_id += 1;
            }
        }
    }

    fn generate_identifier(&self, mut n: usize) -> Identifier {
        let mut result = String::new();
        loop {
            let rem = n % 26;
            result.push(((rem as u8) + b'a') as char);
            if n < 26 {
                break;
            }
            n = (n / 26) - 1;
        }
        Identifier::try_new(result.chars().rev().collect::<String>()).expect("Should be a valid identifier")
    }

    /// Binds a [`Lambda`] term to this context for pretty-printing
    pub fn bind<'a>(&'a mut self, lambda: &'a Lambda) -> NamedLambda<'a> {
        for var in 0..=lambda.highest_arg() {
            self.fill_identifier(var);
        }

        NamedLambda { lambda, context: self }
    }

    fn bind_read<'a>(&'a self, lambda: &'a Lambda) -> NamedLambda<'a> {
        NamedLambda { lambda, context: self }
    }
}

/// A wrapper for [`Lambda`] that implements [`Display`] using a [`NamingContext`]
pub struct NamedLambda<'a> {
    lambda: &'a Lambda,
    context: &'a NamingContext,
}

impl<'a> Display for NamedLambda<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.lambda {
            Lambda::Variable { name } => {
                write!(f, "{}", self.context.get_identifier(*name))
            }
            Lambda::Abstraction { argument, body } => {
                write!(
                    f,
                    "λ{}.{}",
                    self.context.get_identifier(*argument),
                    self.context.bind_read(body),
                )
            }
            Lambda::Application { left, right } => {
                if matches!(**left, Lambda::Abstraction { .. }) {
                    write!(f, "({})", self.context.bind_read(left))?;
                } else {
                    write!(f, "{}", self.context.bind_read(left))?;
                }
                write!(f, " ")?;
                if matches!(**right, Lambda::Application { .. } | Lambda::Abstraction { .. }) {
                    write!(f, "({})", self.context.bind_read(right))
                } else {
                    write!(f, "{}", self.context.bind_read(right))
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expression::rlambda;

    fn assert_round_trip(original_raw: &RawLambda) {
        let (lambda_1, mut context_1) = Lambda::desugar(original_raw);
        let display_1 = context_1.bind(&lambda_1).to_string();

        // Re-parse the display string
        let re_parsed_raw =
            RawLambda::try_from(display_1.as_ref()).expect(&format!("Failed to re-parse: {}", display_1));

        // Redesugar
        let (lambda_2, _) = Lambda::desugar(&re_parsed_raw);

        assert_eq!(
            lambda_1, lambda_2,
            "Structural mismatch after round-trip for: {}",
            display_1
        );
    }

    mod naming_context {
        use super::*;

        #[test]
        fn test_consistency() {
            let mut context = NamingContext::empty();
            let ident = Identifier::try_new("myVar").unwrap();
            let id = context.insert(&ident);

            assert_eq!(context.get_identifier(id), &ident);
            assert_eq!(context.insert(&ident), id);
        }

        #[test]
        fn test_alphabetical_id_generation() {
            let mut context = NamingContext::empty();
            context.fill_identifier(0);
            assert_eq!(context.get_identifier(0).to_string(), "a");
            context.fill_identifier(25);
            assert_eq!(context.get_identifier(25).to_string(), "z");
            context.fill_identifier(26);
            assert_eq!(context.get_identifier(26).to_string(), "aa");
        }
    }

    mod desugarring {
        use super::*;

        #[test]
        fn test_church_zero_and_one() {
            let (zero_lambda, mut context_zero) = Lambda::desugar(&RawLambda::ChurchNumber { value: 0 });
            assert_eq!(context_zero.bind(&zero_lambda).to_string(), "λf.λx.x");
            // assert_round_trip(&RawLambda::ChurchNumber { value: 0 });

            let (one_lambda, mut context_one) = Lambda::desugar(&RawLambda::ChurchNumber { value: 1 });
            assert_eq!(context_one.bind(&one_lambda).to_string(), "λf.λx.f x");

            let f = context_one
                .identifier_to_id
                .get(&Identifier::try_new("f").unwrap())
                .unwrap();
            let x = context_one
                .identifier_to_id
                .get(&Identifier::try_new("x").unwrap())
                .unwrap();
            let expected = lambda!(
                lam,
                *f,
                lambda!(lam, *x, lambda!(app, lambda!(var, *f), lambda!(var, *x)))
            );
            assert_eq!(one_lambda, expected);
            assert_round_trip(&RawLambda::ChurchNumber { value: 1 });
        }

        #[test]
        fn test_nested_abstractions() {
            // λa b. a (λc. c)
            let raw = rlambda!(lam, a b, rlambda!(app, rlambda!(var, a), rlambda!(lam, c, rlambda!(var, c))));
            let (lambda, mut context) = Lambda::desugar(&raw);

            assert_eq!(context.bind(&lambda).to_string(), "λa.λb.a (λc.c)");
            assert_round_trip(&raw);
        }

        #[test]
        fn test_desugar_booleans() {
            let (t_lam, mut context_t) = Lambda::desugar(&RawLambda::True);
            assert_eq!(context_t.bind(&t_lam).to_string(), "λt.λf.t");

            let (f_lam, mut context_f) = Lambda::desugar(&RawLambda::False);
            assert_eq!(context_f.bind(&f_lam).to_string(), "λt.λf.f");
        }

        #[test]
        fn test_desugar_suc() {
            let raw = rlambda!(app, rlambda!(SUC), rlambda!(num, 0));
            let (lambda, mut context) = Lambda::desugar(&raw);
            let display = context.bind(&lambda).to_string();

            assert!(display.contains("λn.λs.λz.s (n s z)"));
        }

        #[test]
        fn test_desugar_plus() {
            let (lambda, mut context) = Lambda::desugar(&RawLambda::Plus);
            let display = context.bind(&lambda).to_string();
            assert_eq!(display, "λx.λy.λs.λz.x s (y s z)");
        }

        #[test]
        fn test_desugar_logic_and() {
            let (lambda, mut context) = Lambda::desugar(&RawLambda::And);
            let display = context.bind(&lambda).to_string();
            assert_eq!(display, "λx.λy.x y x");
        }

        #[test]
        fn test_comparison_resolution() {
            let (lambda, mut context) = Lambda::desugar(&RawLambda::GreaterEqual);
            let display = context.bind(&lambda).to_string();

            assert!(display.contains("λm.λn."));
            assert!(display.contains("λx.λt.λf.f")); // The 'F' inside ZERO
        }
    }

    mod pretty_printing {
        use super::*;

        #[test]
        fn test_complex_nested_display() {
            let (lambda, mut context) = Lambda::desugar(&rlambda!(app, rlambda!(num, 1), rlambda!(var, arg)));
            assert_eq!(context.bind(&lambda).to_string(), "(λf.λx.f x) arg");
            assert_round_trip(&rlambda!(app, rlambda!(num, 1), rlambda!(var, arg)));
        }

        #[test]
        fn test_application_associativity() {
            // (a b) c vs a (b c)
            let raw_left = rlambda!(app, rlambda!(app, rlambda!(var, a), rlambda!(var, b)), rlambda!(var, c));
            let (lambda_left, mut context_left) = Lambda::desugar(&raw_left);
            assert_eq!(context_left.bind(&lambda_left).to_string(), "a b c");
            assert_round_trip(&raw_left);

            let raw_right = rlambda!(app, rlambda!(var, a), rlambda!(app, rlambda!(var, b), rlambda!(var, c)));
            let (lambda_right, mut context_right) = Lambda::desugar(&raw_right);
            assert_eq!(context_right.bind(&lambda_right).to_string(), "a (b c)");
            assert_round_trip(&raw_right);
        }

        #[test]
        fn test_y_combinator_round_trip() {
            let (lambda, mut context) = Lambda::desugar(&RawLambda::YCombinator);
            let display = context.bind(&lambda).to_string();
            // Y = λf.(λx.f (x x)) (λx.f (x x))
            assert!(display.contains("λf"));
            assert_round_trip(&RawLambda::YCombinator);
        }

        #[test]
        fn test_deep_recursion_display() {
            // λx. x x x x
            let raw = rlambda!(
                lam,
                x,
                rlambda!(
                    app,
                    rlambda!(app, rlambda!(app, rlambda!(var, x), rlambda!(var, x)), rlambda!(var, x)),
                    rlambda!(var, x)
                )
            );
            let (lambda, mut context) = Lambda::desugar(&raw);
            assert_eq!(context.bind(&lambda).to_string(), "λx.x x x x");
            assert_round_trip(&raw);
        }
    }
}
