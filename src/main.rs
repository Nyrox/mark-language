#![feature(box_syntax)]
#![feature(let_chains)]

pub mod parser;
use std::{cell::RefCell, collections::HashMap, rc::Rc};

use parser::Scanner;

pub mod ast;
use ast::typed::*;
use ast::untyped::{self, *};

pub mod interpret;
pub mod typecheck;

fn main() {
    let file = std::fs::read_to_string("basic.ml").unwrap();

    let tokens = Scanner::new(file.chars()).scan_all().unwrap();

    let ast = parser::Parser::new(&tokens).parse().unwrap();

    // dbg!(&ast);

    let typechecked = typecheck::typecheck(ast);

    interpret::interpret(typechecked.unwrap());
}
