use std::fmt::Display;

use chumsky::{
    error::Rich,
    extra,
    prelude::{choice, just, recursive},
    text::{self, keyword},
    IterParser, Parser,
};

use crate::expression::Identifier;

/// AST for a non-desugared lambda expression
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawLambda {
    Variable {
        name: Identifier,
    },
    Abstraction {
        arguments: Vec<Identifier>,
        body: Box<Self>,
    },
    Application {
        left: Box<Self>,
        right: Box<Self>,
    },
    ChurchNumber {
        value: usize,
    },
    And,
    Delta,
    Divide,
    Equals,
    False,
    GreaterEqual,
    GreaterThan,
    LessEqual,
    LessThan,
    Minus,
    Not,
    Or,
    Plus,
    Pow,
    Pred,
    Suc,
    Times,
    True,
    YCombinator,
    Zero,
}

/// Helper macro for constructing [`RawLambda`]s
#[allow(unused)]
macro_rules! rlambda {
    (var, $name:ident) => {
        $crate::expression::RawLambda::Variable {
            name: $crate::expression::Identifier::try_new(stringify!($name)).unwrap(),
        }
    };
    (lam, $($arg:ident)+, $body:expr) => {
        $crate::expression::RawLambda::Abstraction {
            arguments: vec![$( $crate::expression::Identifier::try_new(stringify!($arg)).unwrap() ),+],
            body: Box::new($body),
        }
    };
    (app, $left:expr, $right:expr) => {
        $crate::expression::RawLambda::Application {
            left: Box::new($left),
            right: Box::new($right),
        }
    };
    (num, $value:expr) => { $crate::expression::RawLambda::ChurchNumber { value: $value } };
    (/) => { $crate::expression::RawLambda::Divide };
    (=) => { $crate::expression::RawLambda::Equals };
    (>=) => { $crate::expression::RawLambda::GreaterEqual };
    (>) => { $crate::expression::RawLambda::GreaterThan };
    (<=) => { $crate::expression::RawLambda::LessEqual };
    (<) => { $crate::expression::RawLambda::LessThan };
    (-) => { $crate::expression::RawLambda::Minus };
    (+) => { $crate::expression::RawLambda::Plus };
    (^) => { $crate::expression::RawLambda::Pow };
    (*) => { $crate::expression::RawLambda::Times };
    (AND) => { $crate::expression::RawLambda::And };
    (DELTA) => { $crate::expression::RawLambda::Delta };
    (F) => { $crate::expression::RawLambda::False };
    (NOT) => { $crate::expression::RawLambda::Not };
    (OR) => { $crate::expression::RawLambda::Or };
    (PRED) => { $crate::expression::RawLambda::Pred };
    (SUC) => { $crate::expression::RawLambda::Suc };
    (T) => { $crate::expression::RawLambda::True };
    (Y) => { $crate::expression::RawLambda::YCombinator };
    (ZERO) => { $crate::expression::RawLambda::Zero };
}
pub(crate) use rlambda;

impl Display for RawLambda {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Variable { name } => write!(f, "{name:}"),
            Self::Abstraction { arguments, body } => {
                write!(f, "λ")?;
                {
                    let mut first = true;
                    for argument in arguments {
                        if first {
                            first = false;
                        } else {
                            write!(f, " ")?;
                        }
                        write!(f, "{argument}")?;
                    }
                }
                write!(f, ".{body}")
            }
            Self::Application { left, right } => {
                if matches!(**left, Self::Abstraction { .. }) {
                    write!(f, "({left})")?;
                } else {
                    write!(f, "{left}")?;
                }

                write!(f, " ")?;
                if matches!(**right, Self::Application { .. } | Self::Abstraction { .. }) {
                    write!(f, "({right})")
                } else {
                    write!(f, "{right}")
                }
            }
            Self::ChurchNumber { value } => write!(f, "{value}"),
            Self::And => write!(f, "AND"),
            Self::Delta => write!(f, "DELTA"),
            Self::Divide => write!(f, "/"),
            Self::Equals => write!(f, "="),
            Self::False => write!(f, "F"),
            Self::GreaterEqual => write!(f, ">="),
            Self::GreaterThan => write!(f, ">"),
            Self::LessEqual => write!(f, "<="),
            Self::LessThan => write!(f, "<"),
            Self::Minus => write!(f, "-"),
            Self::Not => write!(f, "NOT"),
            Self::Or => write!(f, "OR"),
            Self::Plus => write!(f, "+"),
            Self::Pow => write!(f, "^"),
            Self::Pred => write!(f, "PRED"),
            Self::Suc => write!(f, "SUC"),
            Self::Times => write!(f, "*"),
            Self::True => write!(f, "T"),
            Self::YCombinator => write!(f, "Y"),
            Self::Zero => write!(f, "ZERO"),
        }
    }
}

impl<'a> TryFrom<&'a str> for RawLambda {
    type Error = Vec<Rich<'a, char>>;

    fn try_from(value: &'a str) -> Result<Self, Self::Error> {
        fn parser<'src>() -> impl Parser<'src, &'src str, RawLambda, extra::Full<Rich<'src, char>, (), ()>> {
            let church_number = text::int(10)
                .try_map(|s: &str, span| s.parse::<usize>().map_err(|e| Rich::custom(span, e.to_string())))
                .map(|value| RawLambda::ChurchNumber { value })
                .padded();

            let makro = choice((
                just(">=").to(RawLambda::GreaterEqual),
                just("<=").to(RawLambda::LessEqual),
                just('/').to(RawLambda::Divide),
                just('=').to(RawLambda::Equals),
                just('>').to(RawLambda::GreaterThan),
                just('<').to(RawLambda::LessThan),
                just('-').to(RawLambda::Minus),
                just('+').to(RawLambda::Plus),
                just('^').to(RawLambda::Pow),
                just('*').to(RawLambda::Times),
                just('Y').to(RawLambda::YCombinator),
                keyword("AND").to(RawLambda::And),
                keyword("DELTA").to(RawLambda::Delta),
                keyword("F").to(RawLambda::False),
                keyword("NOT").to(RawLambda::Not),
                keyword("OR").to(RawLambda::Or),
                keyword("PRED").to(RawLambda::Pred),
                keyword("SUC").to(RawLambda::Suc),
                keyword("T").to(RawLambda::True),
                keyword("ZERO").to(RawLambda::Zero),
            ))
            .padded();

            let identifier = text::ascii::ident()
                .try_map(|s: &str, span| Identifier::try_new(s).map_err(|e| Rich::custom(span, e)))
                .padded();

            recursive(|expr| {
                let atom = choice((
                    makro,
                    identifier.map(|name| RawLambda::Variable { name }),
                    church_number,
                    expr.clone().delimited_by(just('('), just(')')),
                ))
                .padded();

                let application = (atom.clone()).foldl(atom.repeated(), |left, right| RawLambda::Application {
                    left: Box::new(left),
                    right: Box::new(right),
                });

                let abstraction = choice((just('\\'), just('λ')))
                    .ignore_then(identifier.clone().repeated().at_least(1).collect::<Vec<_>>())
                    .then_ignore(just('.'))
                    .then(expr)
                    .map(|(arguments, body)| RawLambda::Abstraction {
                        arguments,
                        body: Box::new(body),
                    })
                    .padded();

                choice((abstraction, application))
            })
        }

        parser().parse(value).into_result()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(input: &str, expected_ast: RawLambda, expected_display: &str) {
        let parsed = RawLambda::try_from(input).expect("Parse failed");

        // Structure check
        assert_eq!(parsed, expected_ast, "AST mismatch for input: {}", input);

        // Display check
        let display_out = parsed.to_string();
        assert_eq!(display_out, expected_display, "Display mismatch for input: {}", input);

        // Display output should parse back to same AST
        let round_trip = RawLambda::try_from(display_out.as_str()).expect("Round-trip parse failed");
        assert_eq!(round_trip, expected_ast, "Round-trip AST mismatch");
    }

    #[test]
    fn test_basics() {
        check("x", rlambda!(var, x), "x");
        check("Y", rlambda!(Y), "Y");
        check("42", rlambda!(num, 42), "42");
    }

    #[test]
    fn test_abstractions() {
        check("λx. x", rlambda!(lam, x, rlambda!(var, x)), "λx.x");
        check("λx y z. x", rlambda!(lam, x y z, rlambda!(var, x)), "λx y z.x");
        check(
            "λx. λy. x",
            rlambda!(lam, x, rlambda!(lam, y, rlambda!(var, x))),
            "λx.λy.x",
        );
    }

    #[test]
    fn test_applications() {
        check(
            "x y z",
            rlambda!(app, rlambda!(app, rlambda!(var, x), rlambda!(var, y)), rlambda!(var, z)),
            "x y z",
        );

        check(
            "x (y z)",
            rlambda!(app, rlambda!(var, x), rlambda!(app, rlambda!(var, y), rlambda!(var, z))),
            "x (y z)",
        );
    }

    #[test]
    fn test_mixed_precedence() {
        check(
            "(λx. x) y",
            rlambda!(app, rlambda!(lam, x, rlambda!(var, x)), rlambda!(var, y)),
            "(λx.x) y",
        );

        check(
            "x (λy. y)",
            rlambda!(app, rlambda!(var, x), rlambda!(lam, y, rlambda!(var, y))),
            "x (λy.y)",
        );
    }

    #[test]
    fn test_combinators() {
        let s_ast = rlambda!(lam, x y z,
            rlambda!(app,
                rlambda!(app, rlambda!(var, x), rlambda!(var, z)),
                rlambda!(app, rlambda!(var, y), rlambda!(var, z))
            )
        );
        check("λx y z. x z (y z)", s_ast, "λx y z.x z (y z)");

        let omega_inner = rlambda!(lam, x, rlambda!(app, rlambda!(var, x), rlambda!(var, x)));
        let omega_ast = rlambda!(app, omega_inner.clone(), omega_inner);
        check("(λx. x x) (λx. x x)", omega_ast, "(λx.x x) (λx.x x)");
    }

    #[test]
    fn test_whitespace() {
        check(
            "  \\ x   y  .  x  y  ",
            rlambda!(lam, x y, rlambda!(app, rlambda!(var, x), rlambda!(var, y))),
            "λx y.x y",
        );
    }

    #[test]
    fn test_arithmetic_macros() {
        check(
            "λn. n SUC ZERO",
            rlambda!(
                lam,
                n,
                rlambda!(app, rlambda!(app, rlambda!(var, n), rlambda!(SUC)), rlambda!(ZERO))
            ),
            "λn.n SUC ZERO",
        );

        check(
            "x + y",
            rlambda!(app, rlambda!(app, rlambda!(var, x), rlambda!(+)), rlambda!(var, y)),
            "x + y",
        );

        check(
            "x >= y",
            rlambda!(app, rlambda!(app, rlambda!(var, x), rlambda!(>=)), rlambda!(var, y)),
            "x >= y",
        );
    }

    #[test]
    fn test_logical_macros() {
        check(
            "AND T F",
            rlambda!(app, rlambda!(app, rlambda!(AND), rlambda!(T)), rlambda!(F)),
            "AND T F",
        );
    }

    #[test]
    fn test_complex_definitions() {
        check(
            "λm n. ZERO (DELTA m n)",
            rlambda!(lam, m n,
                rlambda!(app,
                    rlambda!(ZERO),
                    rlambda!(app, rlambda!(app, rlambda!(DELTA), rlambda!(var, m)), rlambda!(var, n))
                )
            ),
            "λm n.ZERO (DELTA m n)",
        );
    }

    #[test]
    fn test_errors() {
        assert!(RawLambda::try_from("λ. x").is_err());
        assert!(RawLambda::try_from("λx").is_err());
        assert!(RawLambda::try_from("(x y").is_err());
    }
}
