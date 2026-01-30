use nutype::nutype;
use std::fmt::Display;

#[nutype(
    sanitize(trim, lowercase),
    validate(
        not_empty,
        predicate= |s :&str| { s.chars().all(|x| x.is_alphabetic())
    }),
    derive(AsRef, Debug, Clone, Eq, Hash, PartialEq)
)]
pub struct Identifier(String);

impl Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:}", self.as_ref())
    }
}
