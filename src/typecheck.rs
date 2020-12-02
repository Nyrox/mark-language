use crate::{
    ast::untyped::{Expr, TypeDeclaration},
    ast::{
        typed::*,
        untyped::{self, Declaration, RecordDeclaration, Ty},
    },
    parser::Span,
    parser::Spanned,
};

use std::cell::RefCell;
use std::{collections::HashMap, rc::Rc};

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
        Expr::Conditional(cond, cons, alt) => {
            let cond = check_type(ctx, cond, &ResolvedType::Bool)?;
            let cons = check_type(ctx, cons, ty)?;
            let alt = check_type(ctx, alt, ty)?;

            Some((ExprT::Conditional(box cond, box cons, box alt), ty.clone()))
        }
        Expr::Tuple(exprs) => match ty {
            ResolvedType::Tuple(tys) => {
                let exprs = exprs
                    .iter()
                    .zip(tys.iter())
                    .map(|(e, t)| check_type(ctx, e, t))
                    .collect::<Option<Vec<_>>>()?;

                Some((ExprT::Tuple(exprs), ty.clone()))
            }
            _ => None,
        },
        Expr::Match(matchee, arms) => {
            let (matchee_te, matched_ty) = infer_type(ctx, matchee)?;

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

                                t_arms.push((
                                    i,
                                    binding.clone().map(|s| s.0),
                                    check_type(ctx, body, ty)?,
                                ));

                                binding.iter().for_each(|binding| {
                                    ctx.symbols.remove(&binding.0.clone());
                                });
                            } else {
                                ctx.errors.push(TypeCheckingError::GenericError(
                                    format!(
                                        "variant {} does not exist on type {}",
                                        &variant.0, qualified_name
                                    ),
                                    variant.1,
                                ));
                                return None;
                            }
                        }

                        Some((
                            ExprT::MatchSum(box (matchee_te, matched_ty), t_arms),
                            ty.clone(),
                        ))
                    } else {
                        ctx.errors.push(TypeCheckingError::GenericError(
                            "matching on this type is not possible".into(),
                            matchee.span(),
                        ));
                        None
                    }
                }
                _ => {
                    ctx.errors.push(TypeCheckingError::GenericError(
                        "matching on this type is not possible".into(),
                        matchee.span(),
                    ));
                    None
                }
            }
        }
        Expr::Lambda(p, e) => match ty {
            ResolvedType::Function(a, b) => {
                ctx.symbols.insert(p.0.clone(), *a.clone());
                let rhs = check_type(ctx, e, b)?;
                ctx.symbols.remove(&p.0);
                Some((ExprT::Lambda(p.0.clone(), box rhs), ty.clone()))
            }
            _ => None,
        },
        Expr::LetBinding(binding, rhs, body) => {
            let (rhs, rhs_t) = infer_type(ctx, rhs).or_else(|| {
                ctx.errors
                    .push(TypeCheckingError::MissingTypeAnnotation(binding.clone()));
                Some((ExprT::Unit, ResolvedType::ErrType))
            })?;

            ctx.symbols.insert(binding.0.clone(), rhs_t.clone());
            let body = check_type(ctx, body, ty)?;
            ctx.symbols.remove(&binding.0);

            let rt = (
                ExprT::LetBinding(binding.0.clone(), box (rhs, rhs_t), box body),
                ty.clone(),
            );
            Some(rt)
        }
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
                                    if let Some(f) =
                                        rc.iter().find(|(name, _e)| &name.0 == &field.0)
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
                    TypeDefinition::Record { fields, .. } => {
                        let mut sorted_fields = Vec::new();
                        for field in fields.iter() {
                            if let Some(f) = rc.iter().find(|(name, _e)| &name.0 == &field.0) {
                                if let Some(e) = check_type(ctx, &f.1, &field.1) {
                                    sorted_fields.push(e);
                                } else {
                                    panic!()
                                }
                            } else {
                                panic!();
                            }
                        }

                        return Some((ExprT::Record(sorted_fields), ty.clone()));
                    }
                    _ => None,
                }
            }
            _ => None,
        },
        Expr::ListConstructor() => match ty {
            ResolvedType::List(_) => Some((ExprT::ListConstructor(), ty.clone())),
            _ => None,
        },
        _ => {
            let (e, t) = infer_type(ctx, expr)?;
            if &t == ty {
                Some((e, t))
            } else {
                ctx.errors.push(TypeCheckingError::TypeMismatch(
                    expr.span(),
                    ty.clone(),
                    Some(t),
                ));
                None
            }
        }
    }
}

fn infer_type(ctx: &mut TypecheckingContext, expr: &untyped::Expr) -> Option<TypedExpr> {
    match expr {
        Expr::Conditional(cond, cons, alt) => {
            let cond = check_type(ctx, cond, &ResolvedType::Bool)?;
            let cons = infer_type(ctx, cons)?;

            let ct = cons.1.clone();
            let alt = check_type(ctx, alt, &ct)?;

            Some((ExprT::Conditional(box cond, box cons, box alt), ct))
        }
        Expr::BinaryOp(op, lhs, rhs) => {
            let lhs = infer_type(ctx, lhs)?;
            let rhs = infer_type(ctx, rhs)?;

            use untyped::Operator;

            match (&lhs.1, &rhs.1) {
                (ResolvedType::Int, ResolvedType::Int) => match op {
                    Operator::BinOpMul
                    | Operator::BinOpAdd
                    | Operator::BinOpSub
                    | Operator::BinOpDiv => {
                        Some((ExprT::BinaryOp(*op, box lhs, box rhs), ResolvedType::Int))
                    }
                    Operator::BinOpLess
                    | Operator::BinOpLessEq
                    | Operator::BinOpGreater
                    | Operator::BinOpGreaterEq
                    | Operator::BinOpEquals => {
                        Some((ExprT::BinaryOp(*op, box lhs, box rhs), ResolvedType::Bool))
                    }
                    _ => None,
                },
                (ResolvedType::String, ResolvedType::String) => match op {
                    Operator::BinOpEquals => {
                        Some((ExprT::BinaryOp(*op, box lhs, box rhs), ResolvedType::Bool))
                    }
                    _ => None,
                },
                (ResolvedType::Bool, ResolvedType::Bool) => match op {
                    Operator::BinOpAnd | Operator::BinOpOr => {
                        Some((ExprT::BinaryOp(*op, box lhs, box rhs), ResolvedType::Bool))
                    }
                    _ => None,
                },
                _ => None,
            }
        }
        Expr::LetBinding(binding, rhs, body) => {
            let (rhs, rhs_t) = infer_type(ctx, rhs).or_else(|| {
                ctx.errors
                    .push(TypeCheckingError::MissingTypeAnnotation(binding.clone()));
                None
            })?;

            ctx.symbols.insert(binding.0.clone(), rhs_t.clone());
            let body = infer_type(ctx, body)?;
            ctx.symbols.remove(&binding.0);

            Some((
                ExprT::LetBinding(binding.0.clone(), box (rhs, rhs_t), box body.clone()),
                body.1.clone(),
            ))
        }
        Expr::Symbol(s) => ctx
            .symbols
            .get(&s.0)
            .map(|t| (ExprT::Symbol(s.0.clone()), t.clone()))
            .or_else(|| {
                ctx.errors.push(TypeCheckingError::UnknownSymbol(s.clone()));
                None
            }),
        Expr::Lambda(p, e) => {
            if &p.0 == "()" {
                ctx.symbols.insert(p.0.clone(), ResolvedType::Unit);
            }

            let r = infer_type(ctx, e);

            ctx.symbols.remove(&p.0);
            let r = r?;
            let e = ExprT::Lambda(p.0.clone(), box (r.0, r.1.clone()));
            let t = ResolvedType::Function(box ResolvedType::Unit, box r.1);

            Some((e, t))
        }
        Expr::Application(lhs, rhs) => {
            if let (lt, ResolvedType::Function(a, b)) = infer_type(ctx, lhs)? {
                if let Some(rt) = check_type(ctx, rhs, &a) {
                    return Some((
                        ExprT::Application(box (lt, ResolvedType::Function(a, b.clone())), box rt),
                        (*b).clone(),
                    ));
                } else {
                    let err = TypeCheckingError::TypeMismatch(
                        rhs.span(),
                        (*a).clone(),
                        infer_type(ctx, rhs).map(|(_, t)| t),
                    );

                    ctx.errors.push(err);
                    return None;
                }
            } else {
                ctx.errors
                    .push(TypeCheckingError::ExpectedFunctionType(lhs.span()));
                return None;
            }
        }
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

            match infer_type(ctx, e)? {
                (te, ResolvedType::TypeHandle(th)) => {
                    match ctx.environment.borrow().types[th.index].clone() {
                        TypeDefinition::Record { fields, .. } => {
                            if let Some((i, (_, ft))) =
                                fields.iter().enumerate().find(|(_i, (s, _))| s == &f.0)
                            {
                                Some((
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
                        _ => {
                            ctx.errors.push(TypeCheckingError::IllegalFieldAccess(
                                Spanned("not a record type".to_owned(), e.span()),
                                f.0.clone(),
                            ));
                            return None;
                        }
                    }
                }
                (te, ResolvedType::Tuple(tys)) => {
                    let index: usize = f.parse().ok().or_else(|| {
                        ctx.errors.push(TypeCheckingError::IllegalFieldAccess(
                            Spanned(
                                "expected field access on a tuple to be an integer value".into(),
                                e.span(),
                            ),
                            f.0.clone(),
                        ));
                        None
                    })?;

                    if index >= tys.len() {
                        ctx.errors.push(TypeCheckingError::IllegalFieldAccess(
                            Spanned(
                                format!(
                                    "field index on tuple {:?}[{}] is out of bounds",
                                    tys, index
                                ),
                                e.span(),
                            ),
                            f.0.clone(),
                        ));
                        return None;
                    }

                    let t = tys[index].clone();
                    Some((
                        ExprT::FieldAccess(box (te, ResolvedType::Tuple(tys)), index),
                        t,
                    ))
                }
                _ => {
                    ctx.errors.push(TypeCheckingError::IllegalFieldAccess(
                        Spanned("not a user type".to_owned(), e.span()),
                        f.0.clone(),
                    ));
                    return None;
                }
            }
        }
        Expr::Unit(_) => Some((ExprT::Unit, ResolvedType::Unit)),
        Expr::StringLiteral(s) => Some((ExprT::StringLiteral(s.0.clone()), ResolvedType::String)),
        Expr::IntegerLiteral(i) => Some((ExprT::IntegerLiteral(i.0), ResolvedType::Int)),
        Expr::BooleanLiteral(b) => Some((ExprT::BooleanLiteral(b.0), ResolvedType::Bool)),
        _ => {
            dbg!("Excuse me?", expr);
            None
        }
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
        Ty::Bool => ResolvedType::Bool,
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

            let th = ctx.insert_type_def(TypeDefinition::Sum {
                qualified_name: ident.clone(),
                variants: Vec::new(),
            });

            let variants = st
                .variants
                .iter()
                .map(|(v, t)| (v.0.clone(), resolve_type(ctx, t)))
                .collect();

            ctx.environment.borrow_mut().types[th.index] = TypeDefinition::Sum {
                qualified_name: ident.clone(),
                variants,
            };
        }
        TypeDeclaration::Record(RecordDeclaration { ident, fields }) => {
            let qualified_name = Rc::new(ident.0.clone());

            let td = TypeDefinition::Record {
                qualified_name,
                fields: fields
                    .iter()
                    .map(|(n, t, a)| {
                        if let Some(a) = a {
                            ctx.errors
                                .push(TypeCheckingError::IllegalAttributeLocation(a.1))
                        }
                        (n.0.clone(), resolve_type(ctx, t))
                    })
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
                        bindings.insert(ident.0.clone(), e.clone());
                        checking_context.symbols.insert(ident.0.clone(), e.1);
                    } else {
                        let err = TypeCheckingError::TypeMismatch(
                            ident.1,
                            expected.clone(),
                            infer_type(&mut checking_context, &expr).map(|(_, t)| t),
                        );

                        checking_context.errors.push(err);
                    }
                } else {
                    if let Some(e) = infer_type(&mut checking_context, &expr) {
                        bindings.insert(ident.0.clone(), e.clone());
                        checking_context.symbols.insert(ident.0.clone(), e.1);
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
