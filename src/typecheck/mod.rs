use crate::{
    ast::untyped::Expr,
    ast::{
        typed::*,
        untyped::{self, Declaration, Ty},
    },
    parser::Span,
    parser::Spanned,
};

use std::cell::RefCell;
use std::{collections::HashMap, rc::Rc};

pub mod judgement;
use judgement::*;

#[derive(Debug, Clone)]
pub enum TypeCheckingError {
    UnknownType(Spanned<String>),
    MissingTypeAnnotation(Spanned<String>),
    TypeMismatch(Span, ResolvedType, Option<ResolvedType>),
    IllegalFieldAccess(Spanned<String>, String),
    ExpectedFunctionType(Span),
    UnknownSymbol(Spanned<String>),
    IllegalAttributeLocation(Span),
    GenericError(String, Span),
    CompoundError(Vec<TypeCheckingError>),
    InferenceFailed(Span),
}

impl TypeCheckingError {
    pub fn compound(self, other: TypeCheckingError) -> TypeCheckingError {
        use TypeCheckingError::*;

        match (self, other) {
            (CompoundError(e1), CompoundError(e2)) => {
                TypeCheckingError::CompoundError(e1.into_iter().chain(e2.into_iter()).collect())
            }
            (CompoundError(mut errors), e) => {
                errors.push(e);
                TypeCheckingError::CompoundError(errors)
            }
            (e, CompoundError(mut errors)) => {
                errors.push(e);
                TypeCheckingError::CompoundError(errors)
            }
            (s, o) => TypeCheckingError::CompoundError(vec![s, o]),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypecheckingContext {
    pub environment: Rc<RefCell<TypeEnvironment>>,
    pub symbols: HashMap<String, ResolvedType>,
    pub scopes: HashMap<String, TypecheckingContext>,
    variant: Option<String>,
}

impl TypecheckingContext {
    pub fn new() -> Self {
        Self {
            environment: Rc::new(RefCell::new(TypeEnvironment::new())),
            symbols: HashMap::new(),
            scopes: HashMap::new(),
            variant: None,
        }
    }
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
) -> TypeJudgement<TypedExpr> {
    if let ResolvedType::TypeParameter(p) = ty {
        return infer_type(ctx, expr)
            .add_constraint(|(_, t)| Constraint::TypeParameterIsType(p.clone(), t.clone()));
    }

    match expr {
        Expr::Conditional(cond, cons, alt) => check_type(ctx, cond, &ResolvedType::Bool)
            .and_still(|| check_type(ctx, cons, ty))
            .and_still(|| check_type(ctx, alt, ty))
            .map(|((cond, cons), alt)| {
                (ExprT::Conditional(box cond, box cons, box alt), ty.clone())
            }),
        Expr::Tuple(exprs) => match ty {
            ResolvedType::Tuple(tys) => {
                let exprs = exprs
                    .iter()
                    .zip(tys.iter())
                    .map(|(e, t)| check_type(ctx, e, t))
                    .collect::<TypeJudgement<_>>();

                exprs.map(|exprs| (ExprT::Tuple(exprs), ty.clone()))
            }
            _ => TypeJudgement::Error(TypeCheckingError::TypeMismatch(
                expr.span(),
                ty.clone(),
                infer_type(ctx, expr).map(|(_, t)| t).ok(),
            )),
        },
        Expr::Match(matchee, arms) => {
            // introducing new constraints here is illegal
            let ((matchee_te, matched_ty), _) = infer_type(ctx, matchee)?;

            match &matched_ty {
                ResolvedType::TypeHandle(i) => {
                    let t = ctx.environment.borrow().types[i.index].clone();
                    if let TypeDefinition::Sum {
                        variants,
                        qualified_name,
                    } = t
                    {
                        let mut t_arms = Vec::new();
                        for (variant, binding, body) in arms {
                            if let Some((i, (vn, vt))) = variants
                                .iter()
                                .enumerate()
                                .find(|(_, (vn, _))| vn == &variant.0)
                            {
                                binding.iter().for_each(|binding| {
                                    ctx.symbols.insert(binding.0.clone(), vt.clone());
                                });

                                t_arms.push(
                                    check_type(ctx, body, ty)
                                        .map(|t| (i, binding.clone().map(|s| s.0), t)),
                                );

                                binding.iter().for_each(|binding| {
                                    ctx.symbols.remove(&binding.0.clone());
                                });
                            } else {
                                return TypeJudgement::Error(TypeCheckingError::GenericError(
                                    format!(
                                        "variant {} does not exist on type {}",
                                        &variant.0, qualified_name
                                    ),
                                    variant.1,
                                ));
                            }
                        }

                        t_arms
                            .into_iter()
                            .collect::<TypeJudgement<_>>()
                            .map(|t_arms| {
                                (
                                    ExprT::MatchSum(box (matchee_te, matched_ty), t_arms),
                                    ty.clone(),
                                )
                            })
                    } else {
                        TypeJudgement::Error(TypeCheckingError::GenericError(
                            "matching on this type is not possible".into(),
                            matchee.span(),
                        ))
                    }
                }
                _ => TypeJudgement::Error(TypeCheckingError::GenericError(
                    "matching on this type is not possible".into(),
                    matchee.span(),
                )),
            }
        }
        Expr::Lambda(p, e) => match ty {
            ResolvedType::Function(a, b) => {
                ctx.symbols.insert(p.0.clone(), *a.clone());
                let rhs = check_type(ctx, e, b);
                ctx.symbols.remove(&p.0);
                rhs.map(|rhs| (ExprT::Lambda(p.0.clone(), box rhs), ty.clone()))
            }
            _ => TypeJudgement::Error(TypeCheckingError::TypeMismatch(e.span(), ty.clone(), None)),
        },
        Expr::LetBinding(binding, rhs, body) => {
            let rhs = infer_type(ctx, rhs);
            let mut rhs_t = ResolvedType::ErrType;
            let rhs = rhs.map(|(e, t)| {
                rhs_t = t.clone();
                (e, t)
            });

            rhs.and_still(|| {
                ctx.symbols.insert(binding.0.clone(), rhs_t);
                let body = check_type(ctx, body, ty);
                ctx.symbols.remove(&binding.0);
                body
            })
            .map(|(rhs, body)| {
                (
                    ExprT::LetBinding(binding.0.clone(), box rhs, box body),
                    ty.clone(),
                )
            })
        }
        Expr::Record(rc) => match ty {
            ResolvedType::TypeHandle(i) => {
                let t = ctx.environment.borrow().types[i.index].clone();
                match t {
                    TypeDefinition::ClosedTypeClassInstance {
                        members,
                        qualified_name,
                        ..
                    } => {
                        'records: for td in members.iter() {
                            let t = ctx.environment.borrow().types[td.index].clone();
                            if let TypeDefinition::Record { fields, .. } = t {
                                let mut sorted_fields = Vec::new();
                                for field in fields.iter() {
                                    if let Some(f) =
                                        rc.iter().find(|(name, _e)| &name.0 == &field.0)
                                    {
                                        sorted_fields.push(check_type(ctx, &f.1, &field.1));
                                    } else {
                                        continue 'records;
                                    }
                                }

                                return sorted_fields
                                    .into_iter()
                                    .collect::<TypeJudgement<_>>()
                                    .map(|sorted_fields| {
                                        (ExprT::Record(sorted_fields), ty.clone())
                                    });
                            }
                        }

                        TypeJudgement::Error(TypeCheckingError::GenericError(
                            format!(
                                "Unable to find a matching record type in type class {}",
                                qualified_name
                            ),
                            expr.span(),
                        ))
                    }
                    TypeDefinition::Record {
                        fields,
                        qualified_name,
                    } => {
                        let mut sorted_fields = Vec::new();
                        for field in fields.iter() {
                            if let Some(f) = rc.iter().find(|(name, _e)| &name.0 == &field.0) {
                                sorted_fields.push(check_type(ctx, &f.1, &field.1));
                            } else {
                                return TypeJudgement::Error(TypeCheckingError::GenericError(
                                    format!(
                                        "Field {} missing from type {}",
                                        field.0, qualified_name
                                    ),
                                    expr.span(),
                                ));
                            }
                        }

                        sorted_fields
                            .into_iter()
                            .collect::<TypeJudgement<_>>()
                            .map(|sorted_fields| (ExprT::Record(sorted_fields), ty.clone()))
                    }
                    _ => TypeJudgement::Error(TypeCheckingError::GenericError(
                        "Record type not expected".into(),
                        expr.span(),
                    )),
                }
            }
            _ => TypeJudgement::Error(TypeCheckingError::GenericError(
                "Record type not expected".into(),
                expr.span(),
            )),
        },
        Expr::ListConstructor() => match ty {
            ResolvedType::List(_) => TypeJudgement::Typed {
                inner: (ExprT::ListConstructor(), ty.clone()),
                constraints: Vec::new(),
            },
            _ => TypeJudgement::Error(TypeCheckingError::GenericError(
                "Did not expect List".into(),
                expr.span(),
            )),
        },
        _ => {
            let ((e, t), mut constraints) = infer_type(ctx, expr)?;

            if &t == ty {
                TypeJudgement::Typed {
                    inner: (e, t),
                    constraints,
                }
            } else if let ResolvedType::TypeParameter(p) = t {
                constraints.push(Constraint::TypeParameterIsType(p, ty.clone()));
                TypeJudgement::Typed {
                    inner: (e, ty.clone()),
                    constraints,
                }
            } else {
                TypeJudgement::Error(TypeCheckingError::TypeMismatch(
                    expr.span(),
                    ty.clone(),
                    Some(t),
                ))
            }
        }
    }
}

fn infer_application(
    ctx: &mut TypecheckingContext,
    (lhs, exprs): (&Expr, &Vec<Expr>),
) -> TypeJudgement<TypedExpr> {
    infer_type(ctx, lhs)
        .then(|(e, t)| {
            if let ResolvedType::Function(a, b) = t {
                let mut lt = a;
                let mut rt = b;
                let mut typed_exprs = Vec::new();
                for (i, expr) in exprs.iter().enumerate() {
                    typed_exprs.push(check_type(ctx, expr, lt));

                    if let ResolvedType::Function(na, nb) = rt.as_ref() {
                        if i != exprs.len() - 1 {
                            lt = na;
                            rt = nb;
                        }
                    } else if i != exprs.len() - 1 {
                        return TypeJudgement::Error(TypeCheckingError::GenericError(
                            "too many arguments in function application".into(),
                            expr.span(),
                        ));
                    }
                }

                typed_exprs
                    .into_iter()
                    .collect::<TypeJudgement<_>>()
                    .map(|a| (a, rt.clone()))
            } else {
                TypeJudgement::Error(TypeCheckingError::ExpectedFunctionType(lhs.span()))
            }
        })
        .map_with_constraints(|(lhs, (exprs, rt)), constraints| {
            dbg!(constraints);
            ((lhs, (exprs, rt)), vec![])
        })
        .map(|(lhs, (exprs, rt))| (ExprT::Application(box lhs, exprs), rt.as_ref().clone()))
}

fn infer_type(ctx: &mut TypecheckingContext, expr: &untyped::Expr) -> TypeJudgement<TypedExpr> {
    match expr {
        Expr::Conditional(cond, cons, alt) => check_type(ctx, cond, &ResolvedType::Bool)
            .and_still(|| infer_type(ctx, cons).then(|(e, t)| check_type(ctx, alt, &t)))
            .map(|(cond, (cons, alt))| {
                let rt = cons.1.clone();
                (ExprT::Conditional(box cond, box cons, box alt), rt)
            }),
        Expr::Tuple(exprs) => {
            let typed_exprs = exprs
                .into_iter()
                .map(|e| infer_type(ctx, e))
                .collect::<TypeJudgement<_>>();

            typed_exprs.map(|typed_exprs| {
                let tuple_type =
                    ResolvedType::Tuple(typed_exprs.iter().map(|(_, t)| t.clone()).collect());
                (ExprT::Tuple(typed_exprs), tuple_type)
            })
        }
        Expr::BinaryOp(op, lhs, rhs) => {
            use untyped::Operator;
            infer_type(ctx, lhs)
                .and_still(|| infer_type(ctx, rhs))
                .map_with_fail(|(lhs, rhs)| match (&lhs.1, &rhs.1) {
                    (ResolvedType::Int, ResolvedType::Int) => match op {
                        Operator::BinOpMul
                        | Operator::BinOpAdd
                        | Operator::BinOpSub
                        | Operator::BinOpDiv
                        | Operator::BinOpMod => {
                            Ok((ExprT::BinaryOp(*op, box lhs, box rhs), ResolvedType::Int))
                        }
                        Operator::BinOpLess
                        | Operator::BinOpLessEq
                        | Operator::BinOpGreater
                        | Operator::BinOpGreaterEq
                        | Operator::BinOpEquals => {
                            Ok((ExprT::BinaryOp(*op, box lhs, box rhs), ResolvedType::Bool))
                        }
                        _ => Err(TypeCheckingError::GenericError(
                            format!(
                                "Binary Operator {:?} is not defined for types {:?}, {:?}",
                                *op, lhs.1, rhs.1
                            ),
                            expr.span(),
                        )),
                    },
                    (ResolvedType::String, ResolvedType::String) => match op {
                        Operator::BinOpEquals => {
                            Ok((ExprT::BinaryOp(*op, box lhs, box rhs), ResolvedType::Bool))
                        }
                        _ => Err(TypeCheckingError::GenericError(
                            format!(
                                "Binary Operator {:?} is not defined for types {:?}, {:?}",
                                *op, lhs.1, rhs.1
                            ),
                            expr.span(),
                        )),
                    },
                    (ResolvedType::Bool, ResolvedType::Bool) => match op {
                        Operator::BinOpAnd | Operator::BinOpOr => {
                            Ok((ExprT::BinaryOp(*op, box lhs, box rhs), ResolvedType::Bool))
                        }
                        _ => Err(TypeCheckingError::GenericError(
                            format!(
                                "Binary Operator {:?} is not defined for types {:?}, {:?}",
                                *op, lhs.1, rhs.1
                            ),
                            expr.span(),
                        )),
                    },
                    _ => Err(TypeCheckingError::GenericError(
                        format!(
                            "Binary Operator {:?} is not defined for types {:?}, {:?}",
                            *op, lhs.1, rhs.1
                        ),
                        expr.span(),
                    )),
                })
        }
        Expr::LetBinding(binding, rhs, body) => {
            let rhs = infer_type(ctx, rhs);
            let mut rhs_t = ResolvedType::ErrType;
            let rhs = rhs.map(|(e, t)| {
                rhs_t = t.clone();
                (e, t)
            });

            rhs.and_still(|| {
                ctx.symbols.insert(binding.0.clone(), rhs_t);
                let body = infer_type(ctx, body);
                ctx.symbols.remove(&binding.0);
                body
            })
            .map(|(rhs, body)| {
                let bt = body.1.clone();
                (ExprT::LetBinding(binding.0.clone(), box rhs, box body), bt)
            })
        }
        Expr::Symbol(s) => {
            if let Some(t) = ctx.symbols.get(&s.0) {
                TypeJudgement::Typed {
                    inner: (ExprT::Symbol(s.0.clone()), t.clone()),
                    constraints: Vec::new(),
                }
            } else {
                TypeJudgement::Error(TypeCheckingError::UnknownSymbol(s.clone()))
            }
        }
        Expr::Lambda(p, e) => {
            if &p.0 == "()" {
                ctx.symbols.insert(p.0.clone(), ResolvedType::Unit);
            }

            let r = infer_type(ctx, e);

            ctx.symbols.remove(&p.0);
            let (r, _) = r?;
            let e = ExprT::Lambda(p.0.clone(), box (r.0, r.1.clone()));
            let t = ResolvedType::Function(box ResolvedType::Unit, box r.1);

            TypeJudgement::Typed {
                inner: (e, t),
                constraints: Vec::new(),
            }
        }
        Expr::Application(lhs, rhs) => infer_application(ctx, (lhs.as_ref(), &rhs)),
        Expr::FieldAccess(e, f) => {
            // VARIANT CONSTRUCTORS
            if let Expr::Symbol(s) = &**e {
                let th = ctx.environment.borrow().type_aliases.get(&s.0).cloned();
                if let Some(ResolvedType::TypeHandle(th)) = th.clone() {
                    match ctx.environment.borrow().types[th.index].clone() {
                        TypeDefinition::Sum { variants, .. } => {
                            if let Some((i, v)) = variants
                                .iter()
                                .enumerate()
                                .find(|(_i, (vn, _))| &vn == &&f.0)
                            {
                                return TypeJudgement::Typed {
                                    inner: (
                                        ExprT::VariantConstructor(th.clone(), i),
                                        match &v.1 {
                                            ResolvedType::Unit => {
                                                ResolvedType::TypeHandle(th.clone())
                                            }
                                            t => ResolvedType::Function(
                                                box t.clone(),
                                                box ResolvedType::TypeHandle(th.clone()),
                                            ),
                                        },
                                    ),
                                    constraints: Vec::new(),
                                };
                            } else {
                                return TypeJudgement::Error(
                                    TypeCheckingError::IllegalFieldAccess(s.clone(), f.0.clone()),
                                );
                            }
                        }
                        _ => {
                            return TypeJudgement::Error(TypeCheckingError::IllegalFieldAccess(
                                s.clone(),
                                f.0.clone(),
                            ));
                        }
                    }
                }
            }

            infer_type(ctx, e).map_with_fail(|lhs| match lhs {
                (te, ResolvedType::TypeHandle(th)) => {
                    match ctx.environment.borrow().types[th.index].clone() {
                        TypeDefinition::Record { fields, .. } => {
                            if let Some((i, (_, ft))) =
                                fields.iter().enumerate().find(|(_i, (s, _))| s == &f.0)
                            {
                                Ok((
                                    ExprT::FieldAccess(
                                        box (te, ResolvedType::TypeHandle(th.clone())),
                                        i,
                                    ),
                                    ft.clone(),
                                ))
                            } else {
                                panic!()
                            }
                        }
                        _ => Err(TypeCheckingError::IllegalFieldAccess(
                            Spanned("not a record type".to_owned(), e.span()),
                            f.0.clone(),
                        )),
                    }
                }
                (te, ResolvedType::Tuple(tys)) => {
                    if let Some(index) = f.parse::<usize>().ok() {
                        if index >= tys.len() {
                            return Err(TypeCheckingError::IllegalFieldAccess(
                                Spanned(
                                    format!(
                                        "field index on tuple {:?}[{}] is out of bounds",
                                        tys, index
                                    ),
                                    e.span(),
                                ),
                                f.0.clone(),
                            ));
                        }

                        let t = tys[index].clone();
                        Ok((
                            ExprT::FieldAccess(box (te, ResolvedType::Tuple(tys)), index),
                            t,
                        ))
                    } else {
                        Err(TypeCheckingError::IllegalFieldAccess(
                            Spanned(
                                "expected field access on a tuple to be an integer value".into(),
                                e.span(),
                            ),
                            f.0.clone(),
                        ))
                    }
                }
                _ => Err(TypeCheckingError::IllegalFieldAccess(
                    Spanned("not a user type".to_owned(), e.span()),
                    f.0.clone(),
                )),
            })
        }
        Expr::Unit(_) => TypeJudgement::Typed {
            inner: (ExprT::Unit, ResolvedType::Unit),
            constraints: Vec::new(),
        },
        Expr::StringLiteral(s) => TypeJudgement::Typed {
            inner: (ExprT::StringLiteral(s.0.clone()), ResolvedType::String),
            constraints: Vec::new(),
        },
        Expr::IntegerLiteral(i) => TypeJudgement::Typed {
            inner: (ExprT::IntegerLiteral(i.0), ResolvedType::Int),
            constraints: Vec::new(),
        },
        Expr::BooleanLiteral(b) => TypeJudgement::Typed {
            inner: (ExprT::BooleanLiteral(b.0), ResolvedType::Bool),
            constraints: Vec::new(),
        },
        _ => TypeJudgement::Error(TypeCheckingError::InferenceFailed(expr.span())),
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
                return ResolvedType::ErrType;
            }
        }
        Ty::List(t) => ResolvedType::List(box resolve_type(ctx, t)),
        Ty::Unit => ResolvedType::Unit,
        Ty::Int => ResolvedType::Int,
        Ty::Float => ResolvedType::Float,
        Ty::String => ResolvedType::String,
        Ty::Bool => ResolvedType::Bool,
        Ty::TypeVariable(p) => ResolvedType::TypeParameter(p.0.clone()),
        Ty::ConstructedType(n, p) => {
            let t = ctx
                .environment
                .borrow()
                .type_constructors
                .get(&n.0)
                .cloned();
            if let Some(t) = t {
                if p.len() == t.type_parameters.len() {
                    ResolvedType::ConstructedType(
                        n.0.clone(),
                        p.iter().map(|t| resolve_type(ctx, t)).collect(),
                    )
                } else {
                    panic!("asdnz")
                }
            } else {
                panic!("{:?} not found", n)
            }
        }
        _ => {
            eprintln!("Error while trying to resolve type: {:?}", ty);
            ResolvedType::ErrType
        }
    }
}

fn typecheck_type_decl(ctx: &mut TypecheckingContext, decl: untyped::TypeDeclaration) {
    use untyped::TypeDeclaration;

    let ident = Rc::new(decl.ident.0.clone());

    match decl.definition {
        untyped::TypeDefinition::Sum { ref variants } => {
            if decl.type_parameters.is_empty() {
                let th = ctx.insert_type_def(TypeDefinition::Sum {
                    qualified_name: ident.clone(),
                    variants: Vec::new(),
                });

                let variants = variants
                    .iter()
                    .map(|(v, t)| (v.0.clone(), resolve_type(ctx, t)))
                    .collect();

                ctx.environment.borrow_mut().types[th.index] = TypeDefinition::Sum {
                    qualified_name: ident.clone(),
                    variants,
                };
            } else {
                ctx.environment.borrow_mut().type_constructors.insert(
                    ident.as_ref().clone(),
                    TypeConstructor {
                        type_parameters: decl.type_parameters.iter().map(|s| s.0.clone()).collect(),
                        type_definition: TypeDefinition::Sum {
                            qualified_name: ident.clone(),
                            variants: Vec::new(),
                        },
                    },
                );

                ctx.scopes
                    .insert(ident.as_ref().clone(), TypecheckingContext::new());

                let variants = variants
                    .iter()
                    .map(|(v, t)| (v.0.clone(), resolve_type(ctx, t)))
                    .collect::<Vec<_>>();
                let variants = variants
                    .into_iter()
                    .map(|(v, t)| {
                        let scope = ctx.scopes.get_mut(ident.as_ref()).unwrap();
                        scope.symbols.insert(
                            v.clone(),
                            ResolvedType::Function(
                                box t.clone(),
                                box ResolvedType::ConstructedType(
                                    ident.as_ref().clone(),
                                    decl.type_parameters
                                        .iter()
                                        .map(|s| ResolvedType::TypeParameter(s.0.clone()))
                                        .collect(),
                                ),
                            ),
                        );

                        (v, t)
                    })
                    .collect();

                ctx.environment
                    .borrow_mut()
                    .type_constructors
                    .get_mut(ident.as_ref())
                    .unwrap()
                    .type_definition = TypeDefinition::Sum {
                    qualified_name: ident.clone(),
                    variants,
                };
            }
        }
        untyped::TypeDefinition::Record { fields } => {
            let td = TypeDefinition::Record {
                qualified_name: ident.clone(),
                fields: fields
                    .iter()
                    .map(|(n, t, a)| (n.0.clone(), resolve_type(ctx, t)))
                    .collect(),
            };

            ctx.insert_type_def(td);
        }
        untyped::TypeDefinition::TypeAlias(t) => {
            let t = resolve_type(ctx, &t);
            ctx.environment
                .borrow_mut()
                .type_aliases
                .insert(ident.as_ref().clone(), t);
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
        match &m.definition {
            untyped::TypeDefinition::Record { fields } => {
                let qualified_name = Rc::new(format!("{}.{}", qualified_name, m.ident.0));

                let td = TypeDefinition::Record {
                    qualified_name,
                    fields: fields
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
    let mut checking_context = TypecheckingContext::new();

    let builtins = &[
        ("File_read", BuiltInFn::FileRead),
        ("String_split", BuiltInFn::StringSplit),
        ("String_parse_int", BuiltInFn::StringParseInt),
        ("String_get_first", BuiltInFn::StringGetFirst),
        ("print", BuiltInFn::Print),
        ("printi", BuiltInFn::Printi),
    ];

    let mut bindings = HashMap::new();
    for (name, f) in builtins {
        bindings.insert(name.to_string(), (ExprT::BuiltInFn(*f), f.resolved_type()));
        checking_context
            .symbols
            .insert(name.to_string(), f.resolved_type());
    }

    let mut errors = Vec::new();

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
                    checking_context
                        .symbols
                        .insert(ident.0.clone(), expected.clone());

                    if false == expected.is_generic() {
                        check_type(&mut checking_context, &expr, &expected)
                            .map(|(e, t)| {
                                bindings.insert(ident.0.clone(), (e.clone(), t.clone()));
                                (e, t)
                            })
                            .iter_err(|err| errors.push(err.clone()));
                    }
                } else {
                    infer_type(&mut checking_context, &expr)
                        .map(|(e, t)| {
                            bindings.insert(ident.0.clone(), (e.clone(), t.clone()));
                            checking_context.symbols.insert(ident.0.clone(), t.clone());
                            (e, t)
                        })
                        .iter_err(|err| errors.push(err.clone()));
                }
            }
            _ => {
                dbg!(d);
                unimplemented!()
            }
        }
    }

    if errors.len() > 0 {
        dbg!(checking_context.environment.borrow());
        Err(errors)
    } else {
        Ok(TypeChecked {
            bindings,
            environment: checking_context.environment,
        })
    }
}
