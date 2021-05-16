use crate::ast::{typed, untyped};
use crate::ast::typed::{Type, Kind};

use std::collections::HashMap;

pub type Substitutions = Vec<(String, Type)>;

pub struct Context {
    pub symbols: HashMap<String, Kind>,
}



pub fn infer(ctx: &mut Context, expr: untyped::Expr) -> (typed::TypedExpr, Substitutions) {


    ()
}


pub fn typecheck(ast: untyped::Untyped) {



}



