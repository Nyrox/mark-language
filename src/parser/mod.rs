pub mod recdec;
pub mod scanner;
pub mod token;

pub use recdec::Parser;
pub use scanner::Scanner;
pub use token::Token;

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Position(pub u32, pub u32);

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Span(pub Position, pub Position);

impl<T: Copy> Copy for Spanned<T> {}

#[derive(Clone)]
pub struct Spanned<T>(T, Span);

impl<T> std::fmt::Debug for Spanned<T>
where
    T: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "Span [{}:{}, {}:{}], Item: {:?}",
            self.1 .0 .0, self.1 .0 .1, self.1 .1 .0, self.1 .1 .1, self.0
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
