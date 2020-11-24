use crate::{
    ast::untyped::{Expr, TypeDeclaration},
    ast::{
        typed::*,
        untyped::{self, Declaration, Ty},
    },
    parser::Spanned,
};

use std::cell::RefCell;
use std::{collections::HashMap, rc::Rc};

#[derive(Debug, Clone)]
pub enum TypeCheckingError {
    UnknownType(Spanned<String>),
    MissingTypeAnnotation(Spanned<String>),
    TypeMismatch(Spanned<String>, ResolvedType),
    IllegalFieldAccess(Spanned<String>, String),
}

#[derive(Debug, Clone)]
pub struct TypecheckingContext {
    pub environment: Rc<RefCell<TypeEnvironment>>,
    pub symbols: HashMap<String, ResolvedType>,
    pub errors: Vec<TypeCheckingError>,
    variant: Option<String>,
}

impl TypecheckingContext {
    pub fn insert_type_def(&self, td: TypeDefinition) -> TypeHandle {
        let th = TypeHandle {
            qualified_name: td.qualified_name(),
            index: self.environment.borrow().types.len(),
            environment: self.environment.clone(),
        };

        self.environment.borrow_mut().type_aliases.insert(
            td.qualified_name().to_string(),
            ResolvedType::TypeHandle(th.clone()),
        );
        self.environment.borrow_mut().types.push(td);
        return th;
    }
}

#[derive(Debug, Clone)]
pub struct TypeChecked {
    pub environment: Rc<RefCell<TypeEnvironment>>,
    pub bindings: HashMap<String, TypedExpr>,
}

fn check_type(
    ctx: &mut TypecheckingContext,
    expr: &untyped::Expr,
    ty: &ResolvedType,
) -> Option<TypedExpr> {
    match expr {
        Expr::Lambda(p, e) => match ty {
            ResolvedType::Function(a, b) => {
                ctx.symbols.insert(p.0.clone(), *a.clone());
                let rhs = check_type(ctx, e, b)?;
                ctx.symbols.remove(&p.0);
                Some((ExprT::Lambda(p.0.clone(), box rhs), ty.clone()))
            }
            _ => None,
        },
        Expr::Record(rc) => match ty {
            ResolvedType::TypeHandle(i) => {
                let t = ctx.environment.borrow().types[i.index].clone();
                match t {
                    TypeDefinition::ClosedTypeClassInstance { members, .. } => {
                        'records: for td in members.iter() {
                            let t = ctx.environment.borrow().types[td.index].clone();
                            if let TypeDefinition::Record { fields, .. } = t {
                                let mut sorted_fields = Vec::new();
                                for field in fields.iter() {
                                    if let Some(f) = rc.iter().find(|(name, e)| &name.0 == &field.0)
                                    {
                                        if let Some(e) = check_type(ctx, &f.1, &field.1) {
                                            sorted_fields.push(e);
                                        } else {
											continue 'records;
                                        }
                                    } else {
										continue 'records;
                                    }
                                }

                                return Some((ExprT::Record(sorted_fields), ty.clone()));
                            }
                        }

                        None
                    }
                    _ => None,
                }
            }
            _ => None,
        },
        Expr::FieldAccess(_, _) => {
            let (e, t) = infer_type(ctx, expr)?;
            if &t == ty {
                Some((e, t))
            } else {
                None
            }
        }
        Expr::StringLiteral(s) => match ty {
            ResolvedType::String => Some((ExprT::StringLiteral(s.0.clone()), ty.clone())),
            _ => None,
        },
        Expr::ListConstructor() => match ty {
            ResolvedType::List(_) => Some((ExprT::ListConstructor(), ty.clone())),
            _ => None,
        },
        _ => None,
    }
}

fn infer_type(ctx: &mut TypecheckingContext, expr: &untyped::Expr) -> Option<TypedExpr> {
    match expr {
        Expr::FieldAccess(e, f) => {
            if let Expr::Symbol(s) = &**e {
                let th = ctx.environment.borrow().type_aliases.get(&s.0).cloned();
                if let Some(ResolvedType::TypeHandle(th)) = th.clone() {
                    match ctx.environment.borrow().types[th.index].clone() {
                        TypeDefinition::Sum { variants, .. } => {
                            if let Some((i, v)) = variants
                                .iter()
                                .enumerate()
                                .find(|(i, (vn, _))| &vn == &&f.0)
                            {
                                return Some((
                                    ExprT::VariantConstructor(th.clone(), i),
                                    match &v.1 {
                                        ResolvedType::Unit => ResolvedType::TypeHandle(th.clone()),
                                        t => ResolvedType::Function(
                                            box t.clone(),
                                            box ResolvedType::TypeHandle(th.clone()),
                                        ),
                                    },
                                ));
                            } else {
                                ctx.errors.push(TypeCheckingError::IllegalFieldAccess(
                                    s.clone(),
                                    f.0.clone(),
                                ));
                                return None;
                            }
                        }
                        _ => {
                            ctx.errors.push(TypeCheckingError::IllegalFieldAccess(
                                s.clone(),
                                f.0.clone(),
                            ));
                            return None;
                        }
                    }
                }
            }

            None
        }
        _ => None,
    }
}

fn resolve_type(ctx: &mut TypecheckingContext, ty: &untyped::Ty) -> ResolvedType {
    match ty {
        Ty::Tuple(tys) => ResolvedType::Tuple(tys.iter().map(|t| resolve_type(ctx, t)).collect()),
        Ty::Func(a, b) => {
            ResolvedType::Function(box resolve_type(ctx, &a), box resolve_type(ctx, &b))
        }
        Ty::TypeRef(n, p) => {
            let typename = match p {
                None => n.0.clone(),
                Some(ref p) => format!("{}_p_{}", &n.0, &p.0),
            };

            if let Some(t) = ctx.symbols.get(&typename) {
                return t.clone();
            } else if let Some(t) = ctx.environment.borrow().type_aliases.get(&typename) {
                return t.clone();
            } else {
                ctx.errors.push(TypeCheckingError::UnknownType(n.clone()));
                return ResolvedType::ErrType;
            }
        }
        Ty::List(t) => ResolvedType::List(box resolve_type(ctx, t)),
        Ty::Unit => ResolvedType::Unit,
        Ty::Int => ResolvedType::Int,
        Ty::Float => ResolvedType::Float,
        Ty::String => ResolvedType::String,
        _ => {
            eprintln!("Error while trying to resolve type: {:?}", ty);
            ResolvedType::ErrType
        }
    }
}

fn typecheck_type_decl(ctx: &mut TypecheckingContext, ty: untyped::TypeDeclaration) {
    use untyped::TypeDeclaration;

    match ty {
        TypeDeclaration::Sum(st) => {
            let ident = Rc::new(st.ident.0.clone());

            let td = TypeDefinition::Sum {
                qualified_name: ident.clone(),
                variants: st
                    .variants
                    .iter()
                    .map(|(v, t)| (v.0.clone(), resolve_type(ctx, t)))
                    .collect(),
            };

            ctx.insert_type_def(td);
        }
        TypeDeclaration::TypeAlias(n, t) => {
            let t = resolve_type(ctx, &t);
            ctx.environment
                .borrow_mut()
                .type_aliases
                .insert(n.0.clone(), t);
        }
        _ => unimplemented!(),
    }
}

pub fn generate_closed_typeclass_instance(
    ctx: &mut TypecheckingContext,
    tc: &untyped::ClosedTypeClass,
) {
    let qualified_name = match ctx.variant {
        None => tc.ident.0.clone(),
        Some(ref p) => format!("{}_p_{}", tc.ident.0, p),
    };
    let qualified_name = Rc::new(qualified_name);

    let th = ctx.insert_type_def(TypeDefinition::ClosedTypeClassInstance {
        qualified_name: qualified_name.clone(),
        methods: Vec::new(),
        impls: Vec::new(),
        members: Vec::new(),
    });

    let mut members = Vec::new();

    ctx.symbols
        .insert("Self".to_owned(), ResolvedType::TypeHandle(th.clone()));

    for m in tc.typeclass_members.iter() {
        match m {
            TypeDeclaration::Record(r) => {
                let qualified_name = Rc::new(format!("{}.{}", qualified_name, r.ident.0));

                let td = TypeDefinition::Record {
                    qualified_name,
                    fields: r
                        .fields
                        .iter()
                        .flat_map(|(n, t, a)| {
                            if a.is_some() && a.clone().map(|s| s.0) != ctx.variant {
                                None
                            } else {
                                Some((n.0.clone(), resolve_type(ctx, t)))
                            }
                        })
                        .collect(),
                };

                members.push(ctx.insert_type_def(td));
            }
            _ => unimplemented!(),
        }
    }

    ctx.environment.borrow_mut().types[th.index] = TypeDefinition::ClosedTypeClassInstance {
        qualified_name: qualified_name.clone(),
        members,
        impls: Vec::new(),
        methods: Vec::new(),
    };
}

pub fn typecheck(ast: untyped::Untyped) -> Result<TypeChecked, Vec<TypeCheckingError>> {
    let mut checking_context = TypecheckingContext {
        environment: Rc::new(RefCell::new(TypeEnvironment::new())),
        symbols: HashMap::new(),
        errors: Vec::new(),
        variant: None,
    };

    let mut bindings = HashMap::new();

    for d in ast.declarations {
        match d {
            Declaration::Type(ty) => typecheck_type_decl(&mut checking_context, ty),
            Declaration::ClosedTypeClass(tc) => {
                if let Some((_, variants)) = &tc.value_param {
                    for v in variants {
                        checking_context.variant = Some(v.0.clone());
                        generate_closed_typeclass_instance(&mut checking_context, &tc);
                    }
                    checking_context.variant = None;
                } else {
                    generate_closed_typeclass_instance(&mut checking_context, &tc);
                }
            }
            Declaration::TypeAnnotation(ident, t) => {
                let t = resolve_type(&mut checking_context, &t);
                checking_context.symbols.insert(ident.0, t);
            }
            Declaration::Binding(ident, expr) => {
                if let Some(expected) = checking_context.symbols.get(&ident.0).cloned() {
                    if let Some(e) = check_type(&mut checking_context, &expr, &expected) {
                        bindings.insert(ident.0.clone(), e);
                    } else {
                        checking_context
                            .errors
                            .push(TypeCheckingError::TypeMismatch(
                                ident.clone(),
                                expected.clone(),
                            ));
                    }
                } else {
                    if let Some(e) = infer_type(&mut checking_context, &expr) {
                        bindings.insert(ident.0.clone(), e);
                    } else {
                        checking_context
                            .errors
                            .push(TypeCheckingError::MissingTypeAnnotation(ident.clone()));
                    }
                }
            }
            _ => {
                dbg!(d);
                unimplemented!()
            }
        }
    }

    if checking_context.errors.len() > 0 {
        dbg!(checking_context.environment.borrow());
        Err(checking_context.errors)
    } else {
        Ok(TypeChecked {
            bindings,
            environment: checking_context.environment,
        })
    }
}
