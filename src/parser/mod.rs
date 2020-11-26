pub mod recdec;
pub mod scanner;
pub mod token;

pub use recdec::Parser;
pub use scanner::Scanner;
pub use token::Token;

#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord)]
pub struct Position(pub u32, pub u32);

#[derive(Clone, Copy, PartialEq)]
pub struct Span(pub Position, pub Position);

impl Span {
    pub fn encompass(self, other: Span) -> Span {
        Self(self.0.min(other.0), self.1.max(other.1))
    }
}

impl<T: Copy> Copy for Spanned<T> {}

#[derive(Clone, Debug)]
pub struct Spanned<T>(pub T, pub Span);

impl std::fmt::Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "Span [{}:{}, {}:{}]",
            self.0 .0, self.0 .1, self.1 .0, self.1 .1
        ))
    }
}

use std::ops::{Deref, DerefMut};

impl<T> Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for Spanned<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
