use std::mem;

use crate::{
    evaluation::{
        shared::{is_free, substitute},
        Evaluation,
    },
    expression::Lambda,
};

/// Evaluates lambda in applicative order
#[derive(Clone, Debug)]
pub struct ApplicativeEvaluation {
    current: Lambda,
    highest_arg: usize,
}

impl Evaluation for ApplicativeEvaluation {
    fn evaluate(lambda: &mut Lambda) {
        let mut highest_arg = lambda.highest_arg();
        while do_evaluate(lambda, &mut highest_arg) {}
    }
}

impl From<Lambda> for ApplicativeEvaluation {
    fn from(value: Lambda) -> Self {
        Self {
            highest_arg: value.highest_arg(),
            current: value,
        }
    }
}

impl Iterator for ApplicativeEvaluation {
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
            // Leftmost first
            if do_evaluate(left, highest_arg) {
                return true;
            }

            // Then Right
            if do_evaluate(right, highest_arg) {
                return true;
            }

            // Beta Reduction
            if let Lambda::Abstraction { argument, body } = &mut **left {
                // Appease borrowchecker
                let mut body_tmp = mem::replace(body, Box::new(Lambda::default()));
                substitute(&mut body_tmp, *argument, right, highest_arg);
                *lambda = *body_tmp;

                return true;
            }

            false
        }
        Lambda::Abstraction { argument, body } => {
            // Evaluate abstraction body
            if do_evaluate(body, highest_arg) {
                return true;
            }

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

            false
        }
        Lambda::Variable { .. } => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expression::lambda;

    #[test]
    fn test_iterator() {
        // (λx. z) ((λy. y) w)
        // (λx. z) w
        // z
        let expr = lambda!(
            app,
            lambda!(lam, 0, lambda!(var, 0)),
            lambda!(app, lambda!(lam, 1, lambda!(var, 1)), lambda!(var, 2))
        );
        let mut eval = ApplicativeEvaluation::from(expr);

        let step1 = eval.next().unwrap();
        assert_eq!(step1, lambda!(app, lambda!(lam, 0, lambda!(var, 0)), lambda!(var, 2)));

        let step2 = eval.next().unwrap();
        assert_eq!(step2, lambda!(var, 2));

        assert!(eval.next().is_none());
    }
}
