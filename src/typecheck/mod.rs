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

pub enum TypeCheckingError {}

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
                .map(|(e, t)| t)
        })
    }

    pub fn typecheck(
        &mut self,
        ast: untyped::Untyped,
    ) -> Result<TypeChecked, Vec<TypeCheckingError>> {
        for d in ast.declarations.iter() {
            match d {
                Declaration::TypeAnnotation(sym, ty) => {
                    self.global_context = TContext::binding(
                        sym.to_string(),
                        self.resolve_type(ty),
                        box self.global_context,
                    );
                }

                _ => panic!(),
            }
        }

        Ok(TypeChecked {
            environment: self.environment,
        })
    }

    pub fn resolve_type(&mut self, ty: &untyped::Ty) -> Kind {
        fn resolve_inner(this: &mut Self, type_vars: &mut Vec<String>, ty: &untyped::Ty) -> Kind {
            match ty {
                Ty::Tuple(tys) => Kind::Type(Type::tuple(
                    tys.iter()
                        .map(|t| this.resolve_inner(type_vars, t))
                        .collect(),
                )),
                _ => panic!(),
            }
        }
    }

    pub fn infer(&mut self, expr: untyped::Expr) -> (typed::TypedExpr, Substitutions) {
        match expr {
            _ => unimplemented!(),
        }
    }
}

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
