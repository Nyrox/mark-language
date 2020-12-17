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
    TypeMismatch(Span, Type, Option<Type>),
    IllegalFieldAccess(Spanned<String>, String),
    ExpectedFunctionType(Span),
    UnknownSymbol(Spanned<String>),
    IllegalAttributeLocation(Span),
    GenericError(String, Span),
    CompoundError(Vec<TypeCheckingError>),
    InferenceFailed(Span),
    ExprHasErrorType(Span),
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

    pub fn as_judgement<T>(self) -> TypeJudgement<T> {
        TypeJudgement::Error(self)
    }
}

#[derive(Debug, Clone)]
pub struct TypecheckingContext {
    pub environment: Rc<RefCell<TypeEnvironment>>,
    pub symbols: HashMap<String, Type>,
    variant: Option<String>,
}

impl TypecheckingContext {
    pub fn new() -> Self {
        Self {
            environment: Rc::new(RefCell::new(TypeEnvironment::default())),
            symbols: HashMap::new(),
            variant: None,
        }
    }

    pub fn insert_type_def(&mut self, scope: Option<String>, td: TypeDefinition) -> TypeHandle {
        let mut env = self.environment.borrow_mut();

        env.types.push(td.clone());

        let th = TypeHandle {
            environment: self.environment.clone(),
            index: env.types.len() - 1,
        };

        match scope {
            Some(s) => {
                env.scopes.entry(s).or_default().type_constructors.insert(
                    td.qualified_name().to_string(),
                    TypeConstructor::UserType(th.clone()),
                );
            }
            None => {
                env.root_scope.type_constructors.insert(
                    td.qualified_name().to_string(),
                    TypeConstructor::UserType(th.clone()),
                );
            }
        }

        th
    }
}

#[derive(Debug, Clone)]
pub struct TypeChecked {
    pub environment: Rc<RefCell<TypeEnvironment>>,
}

fn check_type(
    ctx: &mut TypecheckingContext,
    expr: &untyped::Expr,
    ty: &Type,
) -> TypeJudgement<TypedExpr> {
    let (tc, ty_params) = match ty {
        Type::TypeVariable(p) => {
            return infer_type(ctx, expr)
                .add_constraint(|(_, t)| Constraint::TypeParameterIsType(p.clone(), t.clone()));
        }
        Type::ErrType => {
            return TypeJudgement::Error(TypeCheckingError::ExprHasErrorType(expr.span()))
        }
        Type::ConstructedType(tc, ty_params) => (tc, ty_params),
    };

    match expr {
        Expr::Conditional(cond, cons, alt) => check_type(ctx, cond, &Type::BOOL)
            .and_still(|| check_type(ctx, cons, ty))
            .and_still(|| check_type(ctx, alt, ty))
            .map(|((cond, cons), alt)| {
                (ExprT::Conditional(box cond, box cons, box alt), ty.clone())
            }),
        Expr::Tuple(exprs) => match tc {
            TypeConstructor::Tuple(n) if ty_params.len() == *n => {
                let exprs = exprs
                    .iter()
                    .zip(ty_params.iter())
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
            // EDIT: I don't think this is true?
            let ((matchee_te, matched_ty), _) = infer_type(ctx, matchee)?;

            let ((matched_tc, matched_ty_params), _) = match matched_ty {
                Type::ErrType => TypeCheckingError::ExprHasErrorType(matchee.span()).as_judgement(),
                Type::TypeVariable(_) => TypeCheckingError::GenericError(
                    "cannot match on generic type parameter".to_owned(),
                    matchee.span(),
                )
                .as_judgement(),
                Type::ConstructedType(ref mtc, ref mtys) => {
                    TypeJudgement::new((mtc.clone(), mtys.clone()))
                }
            }?;

            match &matched_tc {
                TypeConstructor::UserType(i) => {
                    let t = ctx.environment.borrow().types[i.index].clone();
                    if let TypeDefinition::Sum {
                        variants,
                        qualified_name,
                        ..
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
        Expr::Lambda(p, e) => match tc {
            TypeConstructor::Function if ty_params.len() == 2 => {
                let (a, b) = (&ty_params[0], &ty_params[1]);

                ctx.symbols.insert(p.0.clone(), a.clone());
                let rhs = check_type(ctx, e, b);
                ctx.symbols.remove(&p.0);
                rhs.map(|rhs| (ExprT::Lambda(p.0.clone(), box rhs), ty.clone()))
            }
            _ => TypeJudgement::Error(TypeCheckingError::TypeMismatch(e.span(), ty.clone(), None)),
        },
        Expr::LetBinding(binding, rhs, body) => {
            let rhs = infer_type(ctx, rhs);
            let mut rhs_t = Type::ErrType;
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
        Expr::Record(rc) => match tc {
            TypeConstructor::UserType(i) => {
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
                        ..
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
        _ => {
            let ((e, t), mut constraints) = infer_type(ctx, expr)?;

            if &t == ty {
                TypeJudgement::Typed {
                    inner: (e, t),
                    constraints,
                }
            } else if let Type::TypeVariable(p) = t {
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
            let ((tc, ty_params), _) = match t {
                Type::ErrType => TypeCheckingError::ExprHasErrorType(lhs.span()).as_judgement(),
                Type::TypeVariable(_) => TypeCheckingError::GenericError(
                    "no support for inferring function types for generic type parameters"
                        .to_owned(),
                    lhs.span(),
                )
                .as_judgement(),
                Type::ConstructedType(tc, tys) => TypeJudgement::new((tc, tys)),
            }?;

            if TypeConstructor::Function != *tc {
                return TypeCheckingError::ExpectedFunctionType(lhs.span()).as_judgement();
            }

            assert_eq!(ty_params.len(), 2);

            let (a, b) = (ty_params[0].clone(), ty_params[1].clone());

            let mut lt = a;
            let mut rt = b;
            let mut typed_exprs = Vec::new();
            for (i, expr) in exprs.iter().enumerate() {
                typed_exprs.push(check_type(ctx, expr, &lt));

                if let Type::ConstructedType(TypeConstructor::Function, ref params) = rt {
                    assert_eq!(params.len(), 2);
                    if i != exprs.len() - 1 {
                        lt = params[0].clone();
                        rt = params[1].clone();
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
        })
        .map_with_constraints(|(lhs, (exprs, rt)), constraints| {
            dbg!(constraints);
            ((lhs, (exprs, rt)), vec![])
        })
        .map(|(lhs, (exprs, rt))| (ExprT::Application(box lhs, exprs), rt.clone()))
}

fn bump_generic_counters(expr: TypedExpr) -> TypedExpr {
    let bump = TYPE_GLOBAL_COUNTER.load(Ordering::SeqCst);

    fn bump_in_type(t: &mut Type, v: u32) -> u32 {
        match t {
            Type::TypeVariable(u) => {
                *u += v;
                *u
            }
            Type::ConstructedType(_, tys) => tys
                .iter_mut()
                .map(|t| bump_in_type(t, v))
                .fold(0, |acc, a| acc.max(a)),
            Type::ErrType => (0),
        }
    }

    fn impl_rec((e, mut t): TypedExpr, bump: u32) -> (TypedExpr, u32) {
        use ExprT::*;

        match e {
            Symbol(_)
            | VariantConstructor(_, _)
            | StringLiteral(_)
            | IntegerLiteral(_)
            | BooleanLiteral(_)
            | BuiltInFn(_)
            | Unit => {
                let u = bump_in_type(&mut t, bump);
                ((e, t), u)
            }
            _ => unimplemented!(),
        }
    }

    let (r, u) = impl_rec(expr, bump);

    TYPE_GLOBAL_COUNTER.fetch_add(u, Ordering::SeqCst);
    return r;
}

fn infer_type(ctx: &mut TypecheckingContext, expr: &untyped::Expr) -> TypeJudgement<TypedExpr> {
    match expr {
        Expr::Conditional(cond, cons, alt) => check_type(ctx, cond, &Type::BOOL)
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
                let tuple_type = Type::tuple(typed_exprs.iter().map(|(_, t)| t.clone()).collect());
                (ExprT::Tuple(typed_exprs), tuple_type)
            })
        }
        Expr::BinaryOp(op, lhs, rhs) => {
            use untyped::Operator;
            infer_type(ctx, lhs)
                .and_still(|| infer_type(ctx, rhs))
                .map_with_fail(|(lhs, rhs)| {
                    let tcs = lhs.1.type_constructor().zip(rhs.1.type_constructor());
                    match tcs {
                        Some((TypeConstructor::Int, TypeConstructor::Int)) => match op {
                            Operator::BinOpMul
                            | Operator::BinOpAdd
                            | Operator::BinOpSub
                            | Operator::BinOpDiv
                            | Operator::BinOpMod => {
                                Ok((ExprT::BinaryOp(*op, box lhs, box rhs), Type::INT))
                            }
                            Operator::BinOpLess
                            | Operator::BinOpLessEq
                            | Operator::BinOpGreater
                            | Operator::BinOpGreaterEq
                            | Operator::BinOpEquals => {
                                Ok((ExprT::BinaryOp(*op, box lhs, box rhs), Type::BOOL))
                            }
                            _ => Err(TypeCheckingError::GenericError(
                                format!(
                                    "Binary Operator {:?} is not defined for types {:?}, {:?}",
                                    *op, lhs.1, rhs.1
                                ),
                                expr.span(),
                            )),
                        },
                        Some((TypeConstructor::String, TypeConstructor::String)) => match op {
                            Operator::BinOpEquals => {
                                Ok((ExprT::BinaryOp(*op, box lhs, box rhs), Type::BOOL))
                            }
                            _ => Err(TypeCheckingError::GenericError(
                                format!(
                                    "Binary Operator {:?} is not defined for types {:?}, {:?}",
                                    *op, lhs.1, rhs.1
                                ),
                                expr.span(),
                            )),
                        },
                        Some((TypeConstructor::Bool, TypeConstructor::Bool)) => match op {
                            Operator::BinOpAnd | Operator::BinOpOr => {
                                Ok((ExprT::BinaryOp(*op, box lhs, box rhs), Type::BOOL))
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
                    }
                })
        }
        Expr::LetBinding(binding, rhs, body) => {
            let rhs = infer_type(ctx, rhs);
            let mut rhs_t = Type::ErrType;
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
            } else if let Some(b) = ctx.environment.borrow().root_scope.bindings.get(&s.0) {
                TypeJudgement::Typed {
                    inner: bump_generic_counters(b.clone()),
                    constraints: Vec::new(),
                }
            } else {
                TypeJudgement::Error(TypeCheckingError::UnknownSymbol(s.clone()))
            }
        }
        Expr::Lambda(p, e) => {
            if &p.0 == "()" {
                ctx.symbols.insert(p.0.clone(), Type::UNIT);
            }

            let r = infer_type(ctx, e);

            ctx.symbols.remove(&p.0);
            let (r, _) = r?;
            let e = ExprT::Lambda(p.0.clone(), box (r.0, r.1.clone()));
            let t = Type::function(Type::UNIT, r.1);

            TypeJudgement::Typed {
                inner: (e, t),
                constraints: Vec::new(),
            }
        }
        Expr::Application(lhs, rhs) => infer_application(ctx, (lhs.as_ref(), &rhs)),
        Expr::FieldAccess(e, f) => {
            // VARIANT CONSTRUCTORS
            if let Expr::Symbol(s) = &**e {
                if let Some(scope) = ctx.environment.borrow().scopes.get(&s.0) {
                    if let Some(binding) = scope.bindings.get(&f.0) {
                        return TypeJudgement::new(binding.clone());
                    } else {
                        return TypeCheckingError::GenericError(
                            format!("Symbol {} does not exist in scope {}", f.0, s.0),
                            expr.span(),
                        )
                        .as_judgement();
                    }
                }
            }

            infer_type(ctx, e).map_with_fail(|lhs| match lhs {
                (te, Type::ConstructedType(TypeConstructor::UserType(th), ty_params)) => {
                    match ctx.environment.borrow().types[th.index].clone() {
                        TypeDefinition::Record { fields, .. } => {
                            if let Some((i, (_, ft))) =
                                fields.iter().enumerate().find(|(_i, (s, _))| s == &f.0)
                            {
                                Ok((
                                    ExprT::FieldAccess(
                                        box (te, Type::user_type(th.clone(), ty_params)),
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
                (te, Type::ConstructedType(TypeConstructor::Tuple(n), ty_params)) => {
                    if let Some(index) = f.parse::<usize>().ok() {
                        if index >= n {
                            return Err(TypeCheckingError::IllegalFieldAccess(
                                Spanned(
                                    format!(
                                        "field index on tuple {:?}[{}] is out of bounds",
                                        ty_params, index
                                    ),
                                    e.span(),
                                ),
                                f.0.clone(),
                            ));
                        }

                        let t = ty_params[index].clone();
                        Ok((
                            ExprT::FieldAccess(box (te, Type::tuple(ty_params)), index),
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
            inner: (ExprT::Unit, Type::UNIT),
            constraints: Vec::new(),
        },
        Expr::StringLiteral(s) => TypeJudgement::Typed {
            inner: (ExprT::StringLiteral(s.0.clone()), Type::STRING),
            constraints: Vec::new(),
        },
        Expr::IntegerLiteral(i) => TypeJudgement::Typed {
            inner: (ExprT::IntegerLiteral(i.0), Type::INT),
            constraints: Vec::new(),
        },
        Expr::BooleanLiteral(b) => TypeJudgement::Typed {
            inner: (ExprT::BooleanLiteral(b.0), Type::BOOL),
            constraints: Vec::new(),
        },
        _ => TypeJudgement::Error(TypeCheckingError::InferenceFailed(expr.span())),
    }
}

use std::sync::atomic::AtomicU32;
use std::sync::atomic::Ordering;
static TYPE_LOCAL_COUNTER: AtomicU32 = AtomicU32::new(0);
static TYPE_GLOBAL_COUNTER: AtomicU32 = AtomicU32::new(0);

fn resolve_type(ctx: &mut TypecheckingContext, ty: &untyped::Ty) -> Type {
    TYPE_LOCAL_COUNTER.store(0, Ordering::Relaxed);

    match ty {
        Ty::Tuple(tys) => Type::tuple(tys.iter().map(|t| resolve_type(ctx, t)).collect()),
        Ty::Func(a, b) => Type::function(resolve_type(ctx, &a), resolve_type(ctx, &b)),
        Ty::TypeRef(n, p) => {
            let typename = match p {
                None => n.0.clone(),
                Some(ref p) => format!("{}_p_{}", &n.0, &p.0),
            };

            if let Some(t) = ctx
                .environment
                .borrow()
                .root_scope
                .type_constructors
                .get(&typename)
            {
                match t.arity() {
                    0 => Type::ConstructedType(t.clone(), vec![]),
                    _ => {
                        eprintln!("Not enough arguments to type constructor {:?}", t);
                        Type::ErrType
                    }
                }
            } else {
                return Type::ErrType;
            }
        }
        Ty::Unit => Type::UNIT,
        Ty::Int => Type::INT,
        Ty::Float => Type::FLOAT,
        Ty::String => Type::STRING,
        Ty::Bool => Type::BOOL,
        Ty::TypeVariable(p) => {
            Type::TypeVariable(TYPE_LOCAL_COUNTER.fetch_add(1, Ordering::Relaxed))
        }
        Ty::ConstructedType(n, p) => {
            let t = {
                let env = ctx.environment.borrow();
                env.root_scope.type_constructors.get(&n.0).cloned()
            };

            if let Some(t) = t {
                Type::ConstructedType(t.clone(), p.iter().map(|t| resolve_type(ctx, t)).collect())
            } else {
                panic!("{:?} not found", n)
            }
        }
        _ => {
            eprintln!("Error while trying to resolve type: {:?}", ty);
            Type::ErrType
        }
    }
}

fn typecheck_type_decl(ctx: &mut TypecheckingContext, decl: untyped::TypeDeclaration) {
    use untyped::TypeDeclaration;

    let ident = Rc::new(decl.ident.0.clone());

    match decl.definition {
        untyped::TypeDefinition::Sum { ref variants } => {
            let th = ctx.insert_type_def(
                None,
                TypeDefinition::Sum {
                    qualified_name: ident.clone(),
                    variants: Vec::new(),
                    type_parameters: decl.type_parameters.iter().map(|s| s.0.clone()).collect(),
                },
            );

            let variants = variants
                .into_iter()
                .enumerate()
                .map(|(i, (v, t))| {
                    let (v, t) = (v.0.clone(), resolve_type(ctx, t));

                    ctx.environment
                        .borrow_mut()
                        .scopes
                        .entry(ident.as_ref().to_owned())
                        .or_default()
                        .bindings
                        .insert(
                            v.clone(),
                            (
                                ExprT::VariantConstructor(th.clone(), i),
                                Type::function(
                                    t.clone(),
                                    Type::user_type(
                                        th.clone(),
                                        decl.type_parameters
                                            .iter()
                                            .enumerate()
                                            .map(|(i, s)| Type::TypeVariable(i as u32))
                                            .collect(),
                                    ),
                                ),
                            ),
                        );

                    (v, t)
                })
                .collect();

            ctx.environment.borrow_mut().types[th.index] = TypeDefinition::Sum {
                qualified_name: ident.clone(),
                type_parameters: decl.type_parameters.iter().map(|s| s.0.clone()).collect(),
                variants,
            };
        }
        untyped::TypeDefinition::Record { fields } => {
            let td = TypeDefinition::Record {
                qualified_name: ident.clone(),
                type_parameters: decl.type_parameters.iter().map(|s| s.0.clone()).collect(),
                fields: fields
                    .iter()
                    .map(|(n, t, a)| (n.0.clone(), resolve_type(ctx, t)))
                    .collect(),
            };

            ctx.insert_type_def(None, td);
        }
        untyped::TypeDefinition::TypeAlias(t) => {
            unimplemented!()
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

    let th = ctx.insert_type_def(
        None,
        TypeDefinition::ClosedTypeClassInstance {
            qualified_name: qualified_name.clone(),
            methods: Vec::new(),
            impls: Vec::new(),
            members: Vec::new(),
        },
    );

    let mut members = Vec::new();

    ctx.symbols
        .insert("Self".to_owned(), Type::user_type(th.clone(), vec![]));

    for m in tc.typeclass_members.iter() {
        match &m.definition {
            untyped::TypeDefinition::Record { fields } => {
                let qualified_name = Rc::new(format!("{}.{}", qualified_name, m.ident.0));

                let td = TypeDefinition::Record {
                    qualified_name: qualified_name.clone(),
                    type_parameters: m.type_parameters.iter().map(|s| s.0.clone()).collect(),
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

                members.push(ctx.insert_type_def(Some(qualified_name.to_string()), td));
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

    for (name, f) in builtins {
        checking_context
            .environment
            .borrow_mut()
            .root_scope
            .bindings
            .insert(name.to_string(), (ExprT::BuiltInFn(*f), f.resolved_type()));
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

                    check_type(&mut checking_context, &expr, &expected)
                        .map(|(e, t)| {
                            checking_context
                                .environment
                                .borrow_mut()
                                .root_scope
                                .bindings
                                .insert(ident.0.clone(), (e.clone(), t.clone()));
                            (e, t)
                        })
                        .iter_err(|err| errors.push(err.clone()));
                } else {
                    infer_type(&mut checking_context, &expr)
                        .map(|(e, t)| {
                            checking_context
                                .environment
                                .borrow_mut()
                                .root_scope
                                .bindings
                                .insert(ident.0.clone(), (e.clone(), t.clone()));
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
        Err(errors)
    } else {
        Ok(TypeChecked {
            environment: checking_context.environment,
        })
    }
}
