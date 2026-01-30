mod applicative;
mod normal;
mod shared;

pub use applicative::ApplicativeEvaluation;
pub use normal::NormalEvaluation;

use crate::expression::Lambda;

pub trait Evaluation: Iterator<Item = Lambda> + From<Lambda> {
    /// Evaluates lambda without intermediate clones
    /// Can get stuck in infinite loop
    fn evaluate(lambda: &mut Lambda);
}
