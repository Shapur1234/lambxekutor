use crate::expression::Lambda;

pub fn is_free(lambda: &Lambda, var: usize) -> bool {
    match lambda {
        Lambda::Variable { name } => var == *name,
        Lambda::Abstraction { argument, body } => var != *argument && is_free(body, var),
        Lambda::Application { left, right } => is_free(left, var) || is_free(right, var),
    }
}

pub fn substitute(lambda: &mut Lambda, var: usize, with: &Lambda, highest_arg: &mut usize) {
    match lambda {
        Lambda::Variable { name } => {
            if *name == var {
                *lambda = with.clone();
            }
        }
        Lambda::Abstraction { argument, body } => {
            if *argument == var {
                return;
            }

            // Alpha reduction
            if is_free(body, var) {
                *highest_arg += 1;
                let new_argument = *highest_arg;
                let new_argument_node = Lambda::Variable { name: new_argument };

                substitute(body, *argument, &new_argument_node, highest_arg);
                *argument = new_argument;
            }

            substitute(body, var, with, highest_arg);
        }
        Lambda::Application { left, right } => {
            substitute(left, var, with, highest_arg);
            substitute(right, var, with, highest_arg);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expression::lambda;

    #[test]
    fn test_is_free() {
        assert!(is_free(&lambda!(var, 0), 0));
        assert!(!is_free(&lambda!(lam, 0, lambda!(var, 0)), 0));
        assert!(is_free(&lambda!(lam, 0, lambda!(var, 1)), 1));
        assert!(is_free(
            &lambda!(app, lambda!(lam, 1, lambda!(var, 1)), lambda!(var, 0)),
            0
        ));
    }

    #[test]
    fn test_simple_substitution() {
        let mut lambda = lambda!(var, 0);
        let mut highest = 1;
        substitute(&mut lambda, 0, &lambda!(var, 1), &mut highest);

        assert_eq!(lambda, lambda!(var, 1));
        assert_eq!(highest, 1);
    }

    #[test]
    fn test_substitution_shadowing() {
        let mut lambda = lambda!(lam, 0, lambda!(var, 0));
        let mut highest = 1;
        substitute(&mut lambda, 0, &lambda!(var, 1), &mut highest);

        assert_eq!(lambda, lambda!(lam, 0, lambda!(var, 0)));
        assert_eq!(highest, 1);
    }
    #[test]
    fn test_substitution_rename() {
        let mut lambda = lambda!(lam, 1, lambda!(var, 0));
        let mut highest = 1;
        substitute(&mut lambda, 0, &lambda!(var, 1), &mut highest);

        assert_eq!(lambda, lambda!(lam, 2, lambda!(var, 1)));
        assert_eq!(highest, 2);
    }
}
