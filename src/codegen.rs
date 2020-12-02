use std::{collections::HashMap, fmt::Debug, rc::Rc};

use crate::{ast::typed::TypedExpr, ast::typed::*, typecheck::TypeChecked};


#[derive(Debug, Clone)]
pub enum Instruction {

}


#[derive(Debug, Clone)]
pub struct CompiledProgram {
	pub instructions: Vec<Instruction>,
}



pub fn codegen(ast: TypeChecked) -> CompiledProgram {
	let mut program = CompiledProgram {
		instructions: Vec::new(),
	};

	for (label, binding) in ast.bindings.iter() {
		// TODO: Implement constants

		codegen_expr(&mut program, binding);

	}

	program
}

fn codegen_expr(program: &mut CompiledProgram, expr: &TypedExpr) {

	match expr {
		ExprT::Lambda(binding, body) => {

		}
		_ => unimplemented!("{:?}", expr)
	}
}
