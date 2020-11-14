pub mod parser;
use parser::Scanner;

pub mod ast;

fn main() {
	let file = std::fs::read_to_string("basic.ml").unwrap();

	let tokens = Scanner::new(file.chars()).scan_all().unwrap();

	dbg!(tokens);
}
