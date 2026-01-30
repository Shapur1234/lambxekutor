use std::mem;

use crate::{
    evaluation::{
        shared::{is_free, substitute},
        Evaluation,
    },
    expression::Lambda,
};

/// Evaluates lambda in normal order
#[derive(Clone, Debug)]
pub struct NormalEvaluation {
    current: Lambda,
    highest_arg: usize,
}

impl Evaluation for NormalEvaluation {
    fn evaluate(lambda: &mut Lambda) {
        let mut highest_arg = lambda.highest_arg();
        while do_evaluate(lambda, &mut highest_arg) {}
    }
}

impl From<Lambda> for NormalEvaluation {
    fn from(value: Lambda) -> Self {
        Self {
            highest_arg: value.highest_arg(),
            current: value,
        }
    }
}

/// Iterates over reduction steps in normal evaluation order
impl Iterator for NormalEvaluation {
    type Item = Lambda;

    fn next(&mut self) -> Option<Self::Item> {
        if do_evaluate(&mut self.current, &mut self.highest_arg) {
            Some(self.current.clone())
        } else {
            None
        }
    }
}

fn do_evaluate(lambda: &mut Lambda, highest_arg: &mut usize) -> bool {
    match lambda {
        Lambda::Application { left, right } => {
            // Beta Reduction
            if let Lambda::Abstraction { argument, body } = &mut **left {
                // Appease borrowchecker
                let mut body_tmp = mem::replace(body, Box::new(Lambda::default()));
                substitute(&mut body_tmp, *argument, right, highest_arg);
                *lambda = *body_tmp;

                return true;
            }

            // Leftmost first
            if do_evaluate(left, highest_arg) {
                return true;
            }

            // Then Right
            if do_evaluate(right, highest_arg) {
                return true;
            }

            false
        }
        Lambda::Abstraction { argument, body } => {
            // Eta Reduction
            if let Lambda::Application {
                left: child_body,
                right: child_argument,
            } = &mut **body
            {
                if let Lambda::Variable {
                    name: child_argument_name,
                } = &**child_argument
                {
                    if *child_argument_name == *argument && !is_free(child_body, *argument) {
                        // Appease borrowchecker
                        let child_body_tmp = mem::replace(child_body, Box::new(Lambda::default()));
                        *lambda = *child_body_tmp;

                        return true;
                    }
                }
            }

            // Evaluate abstraction body
            if do_evaluate(body, highest_arg) {
                return true;
            }

            false
        }
        Lambda::Variable { .. } => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expression::{lambda, RawLambda};

    fn run(input: &str) -> String {
        let raw = RawLambda::try_from(input).unwrap();
        let (mut lambda, mut context) = Lambda::desugar(&raw);
        NormalEvaluation::evaluate(&mut lambda);

        context.bind(&lambda).to_string()
    }

    #[test]
    fn test_beta() {
        // (λx. x) y  =>  y
        let mut expr = lambda!(app, lambda!(lam, 0, lambda!(var, 0)), lambda!(var, 1));
        NormalEvaluation::evaluate(&mut expr);
        assert_eq!(expr, lambda!(var, 1));
    }

    #[test]
    fn test_eta() {
        // λx. f x  =>  f
        let mut expr = lambda!(lam, 0, lambda!(app, lambda!(var, 1), lambda!(var, 0)));
        NormalEvaluation::evaluate(&mut expr);
        assert_eq!(expr, lambda!(var, 1));
    }

    #[test]
    fn test_iterator() {
        // (λx. x) ((λy. y) z)
        // ((λy. y) z)
        // z
        let expr = lambda!(
            app,
            lambda!(lam, 0, lambda!(var, 0)),
            lambda!(app, lambda!(lam, 1, lambda!(var, 1)), lambda!(var, 2))
        );
        let mut eval = NormalEvaluation::from(expr);

        let step1 = eval.next().unwrap();
        assert_eq!(step1, lambda!(app, lambda!(lam, 1, lambda!(var, 1)), lambda!(var, 2)));

        let step2 = eval.next().unwrap();
        assert_eq!(step2, lambda!(var, 2));

        assert!(eval.next().is_none());
    }

    #[test]
    fn test_nested() {
        assert_eq!(run("(λx y. y x) z a"), "a z");
    }

    #[test]
    fn test_booleans() {
        assert_eq!(run("AND T F"), "λt.λf.f");
        assert_eq!(run("NOT F"), "λd.λg.d");
    }

    #[test]
    fn test_arithmetic() {
        assert_eq!(run("SUC 1"), "λg.λi.g (g i)");
        assert_eq!(run("+ 1 1"), "λn.λp.n (n p)");
    }

    #[test]
    fn test_comparison() {
        assert_eq!(run("ZERO 0"), "λt.λf.t");
        assert_eq!(run("ZERO 1"), "λt.λf.f");
    }
    #[test]
    fn test_factorial() {
        let factorial = "Y (λf n. (ZERO n) 1 (* n (f (PRED n))))";

        assert_eq!(run(&format!("{} 0", factorial)), "λf.f");
        assert_eq!(run(&format!("{} 1", factorial)), "λf.f");
        assert_eq!(run(&format!("{} 2", factorial)), "λr.λv.r (r v)");
        assert_eq!(run(&format!("{} 3", factorial)), "λr.λv.r (r (r (r (r (r v)))))");
    }
}
