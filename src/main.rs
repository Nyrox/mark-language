#![feature(box_syntax)]
#![feature(let_chains)]
#![feature(iterator_fold_self)]
#![feature(try_trait_v2)]

pub mod parser;

use parser::Scanner;
pub mod ast;

pub mod interpret;
pub mod typecheck;

use std::{error::Error, borrow::Borrow};

use linefeed::{Interface, ReadResult};

use crate::{
    ast::untyped::Declaration,
    parser::{Span, Spanned},
};

fn repl() -> Result<(), Box<dyn Error>> {
    let mut reader = Interface::new("my-application")?;

    reader.set_prompt("mark-lang> ")?;

    let mut inputString = String::new();
    while let ReadResult::Input(input) = reader.read_line()? {
        inputString.push_str(&input);
        inputString.push('\n');
        if !input.contains(';') { continue; }
        let (input, _) = inputString.split_at(inputString.find(';').unwrap());
        let mut readLine = || -> Result<(), Box<dyn Error>> {


            match input {
                "quit" | "exit" => std::process::exit(0),
                _ if input.starts_with("eval ") => {
                    let tokens = Scanner::new(input.chars().skip(5)).scan_all()?;
                    let ast = parser::Parser::new(&tokens).parse_expr()?;
                    let ast = ast::untyped::Untyped {
                        declarations: vec![Declaration::Binding(
                            Spanned("main".into(), Span::empty()),
                            ast::untyped::Expr::Lambda(Spanned("()".into(), Span::empty()), box ast),
                        )],
                    };
                    let typechecked = typecheck::typecheck(ast)?;

                    println!("{:?}", (*typechecked.environment).borrow().root_scope.bindings.get("main").unwrap().1);
                    interpret::interpret(typechecked);
                }
                _ => {
                    let tokens = Scanner::new(input.chars()).scan_all()?;
                    let ast = parser::Parser::new(&tokens).parse_all()?;

                    let _typechecked = typecheck::typecheck(ast)?;
                }
            }

            Ok(())
        };

        println!("{:?}", readLine());
        inputString.clear();
    }

    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    let thread = std::thread::Builder::new().stack_size(32 * 1024 * 1024);

    let runner = thread.spawn(move || repl().unwrap()).unwrap();

    Ok(runner.join().unwrap())
}
