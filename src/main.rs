#![feature(box_syntax)]
#![feature(let_chains)]
#![feature(iterator_fold_self)]
#![feature(try_trait)]

pub mod parser;

use parser::Scanner;

pub mod ast;

pub mod interpret;
pub mod typecheck;

fn main() {
    // let file = std::fs::read_to_string("examples/aoc2020/day3/main.ml").unwrap();
    // std::env::set_current_dir("examples/aoc2020/day3").unwrap();

    let file = std::fs::read_to_string("min.ml").unwrap();

    let thread = std::thread::Builder::new().stack_size(32 * 1024 * 1024);

    let runner = thread
        .spawn(move || {
            let tokens = Scanner::new(file.chars()).scan_all().unwrap();

            let ast = parser::Parser::new(&tokens).parse().unwrap();

            std::fs::write("ast.ron", format!("{:#?}", &ast)).ok();

            let typechecked = match typecheck::typecheck(ast) {
                Ok(t) => t,
                Err(errs) => {
                    dbg!(errs);
                    return;
                }
            };

            std::fs::write("typed_ast.ron", format!("{:#?}", &typechecked)).ok();

            interpret::interpret(typechecked);
        })
        .unwrap();

    runner.join().unwrap()
}
