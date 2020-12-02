#![feature(box_syntax)]
#![feature(let_chains)]
#![feature(iterator_fold_self)]

pub mod parser;

use parser::Scanner;

pub mod ast;

pub mod interpret;
pub mod typecheck;

fn main() {
    let file = std::fs::read_to_string("examples/aoc2020/day2/main.ml").unwrap();

    std::env::set_current_dir("examples/aoc2020/day2").unwrap();

    let tokens = Scanner::new(file.chars()).scan_all().unwrap();

    let ast = parser::Parser::new(&tokens).parse().unwrap();

    // dbg!(&ast);

    let typechecked = match typecheck::typecheck(ast) {
        Ok(t) => t,
        Err(errs) => {
            dbg!(errs);
            return;
        }
    };
}
