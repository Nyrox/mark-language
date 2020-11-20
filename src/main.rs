#![feature(box_syntax)]

pub mod parser;
use std::{cell::RefCell, collections::HashMap, rc::Rc};

use parser::Scanner;

pub mod ast;
use ast::untyped::{self, *};

mod typed {
    pub struct ClosedTypeClass {}

    pub struct RecordType {
        c_typeclass: Option<Rc<ClosedTypeClass>>,
    }

    pub enum ResolvedType {
        Record(RecordType),
        Function(Box<ResolvedType>, Box<ResolvedType>),
    }
}

use typed::*;

struct GlobalSymbols {
    c_typeclass_instances: HashMap<String, Rc<typed::ClosedTypeClass>>,
    type_aliases: HashMap<String, ResolvedType>,
}

impl GlobalSymbols {
    pub fn new() -> Self {
        Self {
            c_typeclass_instances: HashMap::new(),
            type_aliases: HashMap::new(),
        }
    }
}

struct Context<'a> {
    symbols: HashMap<String, Ty>,
    parent: Option<&'a Context<'a>>,
    global: Rc<RefCell<GlobalSymbols>>,
}

impl<'a> Context<'a> {
    pub fn branch(&'a self) -> Context<'a> {
        Context {
            symbols: HashMap::new(),
            parent: Some(self),
            global: self.global.clone(),
        }
    }

    pub fn branch_with(&'a self, (k, v): (String, Ty)) -> Context<'a> {
        let mut symbols = HashMap::new();
        symbols.insert(k, v);
        Context {
            symbols,
            parent: Some(self),
            global: self.global.clone(),
        }
    }
}

fn check_type(context: &Context, expr: &Expr, ty: &Ty) -> bool {
    use Expr::*;

    match expr {
        Lambda(p, e) => match ty {
            Ty::Func(a, b) => check_type(&context.branch_with((p.0.clone(), *a.clone())), e, b),
            _ => false,
        },
        Record(record) => {}
        _ => false,
    }
}

fn infer_type(context: &Context, expr: &Expr) -> Option<Ty> {
    match expr {
        _ => None,
    }
}

fn generate_c_typeclass_variant(
    symbols: Rc<RefCell<GlobalSymbols>>,
    class: &untyped::ClosedTypeClass,
    variant: Option<String>,
) {

    
}

fn typecheck(ast: Untyped) {
    let global_symbols = Rc::new(RefCell::new(GlobalSymbols::new()));
    let mut context = Context {
        symbols: HashMap::new(),
        parent: None,
        global: global_symbols.clone(),
    };

    for d in ast.declarations.into_iter() {
        match d {
            Declaration::Type(mut ty) => {
                ty.ty
                    .visit::<_, ()>(&mut |t| match t {
                        _ => Ok(()),
                    })
                    .unwrap();
                context.symbols.insert(ty.ident.0, ty.ty);
            }
            Declaration::TypeAnnotation(ident, ty) => {
                context.symbols.insert(ident.0, ty);
            }
            Declaration::ClosedTypeClass(tc) => {
                if let Some((_, variants)) = tc.value_param {
                    for v in variants {
                        generate_c_typeclass_variant(global_symbols.clone(), &tc, Some(v));
                    }
                } else {
                    generate_c_typeclass_variant(global_symbols.clone(), &tc, None);
                }
            }
            Declaration::Binding(ident, expr) => {
                let child_context = context.branch();
                if let Some(expected) = context.symbols.get(&ident.0) {
                    if !check_type(&context, &expr, &expected) {
                        eprintln!("Typecheck failed: ");
                        dbg!(expected, expr);
                    }
                } else {
                    if let Some(ty) = infer_type(&context, &expr) {
                        context.symbols.insert(ident.0, ty);
                    } else {
                        eprintln!(
                            "Needed to infer type for top level binding: {}, but failed.",
                            ident.0
                        );
                    }
                }
            }
        }
    }
}

fn main() {
    let file = std::fs::read_to_string("basic.ml").unwrap();

    let tokens = Scanner::new(file.chars()).scan_all().unwrap();

    let ast = parser::Parser::new(&tokens).parse().unwrap();

    // dbg!(&ast);

    let typechecked = typecheck(ast);

    dbg!(typechecked);
}
