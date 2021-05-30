use crate::ast::{
    typed::{self, TypeEnvironment},
    untyped,
};
use crate::ast::{
    typed::{Kind, Type},
    untyped::{Declaration, Ty},
};

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

pub type Substitutions = Vec<(String, Type)>;

#[derive(Clone, Debug)]
pub enum TypeCheckingError {}

#[derive(Clone, Debug)]
pub enum TContext {
    Binding {
        name: String,
        kind: Kind,
        cons: Box<TContext>,
    },
    Empty,
}

impl TContext {
    pub fn binding(name: String, kind: Kind, cons: Box<TContext>) -> Self {
        TContext::Binding { name, kind, cons }
    }

    pub fn lookup(&self, symbol: &str) -> Option<Kind> {
        match self {
            TContext::Empty => None,
            TContext::Binding { name, kind, cons } => {
                if name == symbol {
                    Some(kind.clone())
                } else {
                    cons.lookup(symbol)
                }
            }
        }
    }
}

pub struct TypeChecker {
    pub global_context: TContext,
    pub next_tvar: usize,
    pub environment: TypeEnvironment,
}

impl TypeChecker {
    pub fn new() -> TypeChecker {
        TypeChecker {
            global_context: TContext::Empty,
            next_tvar: 1,
            environment: Default::default(),
        }
    }

    pub fn lookup_in_context(&self, ctx: TContext, symbol: &str) -> Option<Kind> {
        ctx.lookup(symbol).or_else(|| {
            self.environment
                .root_scope
                .bindings
                .get(symbol)
                .map(|(e, t)| t.clone())
        })
    }

    pub fn typecheck(
        &mut self,
        ast: untyped::Untyped,
    ) -> Result<TypeChecked, Vec<TypeCheckingError>> {
        for d in ast.declarations.iter() {
            match d {
                Declaration::TypeAnnotation(sym, ty) => {
                    let nc = TContext::binding(
                        sym.to_string(),
                        dbg!(self.resolve_type(ty)),
                        Box::new(std::mem::replace(&mut self.global_context, TContext::Empty)),
                    );
                    self.global_context = nc;
                }
                Declaration::Binding(name, expr) => {
                    
                }
                _ => panic!("{:#?}", d),
            }
        }

        Ok(TypeChecked {
            environment: self.environment.clone(),
        })
    }

    pub fn resolve_type(&mut self, ty: &untyped::Ty) -> Kind {
        fn resolve_inner(
            this: &mut TypeChecker,
            type_vars: &mut Vec<String>,
            ty: &untyped::Ty,
        ) -> Type {
            match ty {
                Ty::Tuple(tys) => Type::tuple(
                    tys.iter()
                        .map(|t| resolve_inner(this, type_vars, t))
                        .collect(),
                ),
                Ty::Func(from, to) => Type::function(
                    resolve_inner(this, type_vars, from),
                    resolve_inner(this, type_vars, to),
                ),
                Ty::TypeVariable(tv) => {
                    if let Some((i, e)) = type_vars
                        .iter()
                        .enumerate()
                        .find(|(i, e)| e.as_str() == tv.0.as_str())
                    {
                        Type::TypeVariable(i as u32)
                    } else {
                        type_vars.push(tv.0.clone());
                        Type::TypeVariable(type_vars.len() as u32)
                    }
                }
                _ => panic!("{:#?}", ty),
            }
        }

        let mut type_vars = Vec::new();
        let tt = resolve_inner(self, &mut type_vars, ty);
        Kind::TypeSchema(type_vars, tt)
    }

    pub fn infer(&mut self, expr: untyped::Expr) -> (typed::TypedExpr, Substitutions) {
        match expr {
            _ => unimplemented!(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct TypeChecked {
    pub environment: TypeEnvironment,
}

impl TypeChecked {
    pub fn new() -> Self {
        TypeChecked {
            environment: TypeEnvironment::default(),
        }
    }
}

pub fn typecheck(ast: untyped::Untyped) -> Result<TypeChecked, Vec<TypeCheckingError>> {
    let mut type_checker = TypeChecker::new();

    type_checker.typecheck(ast)
}
