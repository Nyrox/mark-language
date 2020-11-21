#![feature(box_syntax)]

pub mod parser;
use std::{cell::RefCell, collections::HashMap, rc::Rc};

use parser::Scanner;

pub mod ast;
use ast::untyped::{self, *};

mod typed {
    use crate::ast::untyped::{self};
    use std::{cell::RefCell, rc::Rc};

    #[derive(Debug, Clone)]
    pub struct NamedFuncSig {
        pub ident: String,
        pub sig: (ResolvedType, ResolvedType),
    }

    #[derive(Debug, Clone)]
    pub struct TypeClassImplItem {
        pub what: String,
        pub who: String,
        pub body: untyped::Expr,
    }

    #[derive(Debug, Clone)]
    pub struct ClosedTypeClass {
        pub ident: String,
        pub methods: Vec<NamedFuncSig>,
        pub impls: Vec<TypeClassImplItem>,
        pub members: Vec<(String, ResolvedType)>,
    }

    #[derive(Debug, Clone)]
    pub struct SumType {
        pub ident: String,
        pub variants: Vec<(String, ResolvedType)>,
    }

    #[derive(Debug, Clone)]
    pub struct RecordType {
        pub fields: Vec<(String, ResolvedType)>,
        pub c_typeclass: Option<Rc<ClosedTypeClass>>,
    }

    #[derive(Debug, Clone)]
    pub enum ResolvedType {
        Record(RecordType),
        Function(Box<ResolvedType>, Box<ResolvedType>),
        ClosedTypeClass(Rc<RefCell<ClosedTypeClass>>),
        Sum(Rc<RefCell<SumType>>),
        Tuple(Vec<ResolvedType>),
        List(Box<ResolvedType>),
        Unit,
        Int,
        Float,
        String,
    }
}

use typed::*;

#[derive(Clone, Debug)]
struct GlobalSymbols {
    c_typeclass_instances: HashMap<String, Rc<RefCell<typed::ClosedTypeClass>>>,
    type_aliases: HashMap<String, ResolvedType>,
}

impl GlobalSymbols {
    pub fn new() -> Self {
        Self {
            c_typeclass_instances: HashMap::new(),
            type_aliases: HashMap::new(),
        }
    }

    pub fn lookup(&self, name: &str, param: Option<String>) -> Option<&ResolvedType> {
        match param {
            None => self.type_aliases.get(name),
            Some(p) => self.type_aliases.get(&format!("{}_p_{}", name, p)),
        }
    }
}

#[derive(Clone, Debug)]
struct Context<'a> {
    symbols: HashMap<String, ResolvedType>,
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

    pub fn branch_with(&'a self, (k, v): (String, ResolvedType)) -> Context<'a> {
        let mut symbols = HashMap::new();
        symbols.insert(k, v);
        Context {
            symbols,
            parent: Some(self),
            global: self.global.clone(),
        }
    }
}

fn check_type(context: &Context, expr: &Expr, ty: &ResolvedType) -> bool {
    use Expr::*;

    match expr {
        Lambda(p, e) => match ty {
            ResolvedType::Function(a, b) => {
                check_type(&context.branch_with((p.0.clone(), *a.clone())), e, b)
            }
            _ => false,
        },
        Expr::Record(record) => match ty {
            ResolvedType::Record(r) => unimplemented!(),
            ResolvedType::ClosedTypeClass(tc) => {
                'members: for (_, ty) in tc.borrow().members.iter() {
                    if let ResolvedType::Record(r) = ty {
                        for field in r.fields.iter() {
                            if let Some(f) = record.iter().find(|(name, e)| &name.0 == &field.0) {
                                if !check_type(&context, &f.1, &field.1) {
                                    continue 'members;
                                }
                            } else {
                                continue 'members;
                            }
                        }
                        return true;
                    }
                }

                false
            }
            _ => false,
        },
        Expr::FieldAccess(e, f) => {
            let l_ty = infer_type(context, &e).unwrap();

            match l_ty {
                ResolvedType::Sum(st) => {
                    if let Some(v) = st.borrow().variants.iter().find(|(vn, _)| &vn == &&f.0) {
                        match (&v.1, ty) {
                            (ResolvedType::Unit, ResolvedType::Sum(sc)) if sc.borrow().ident == st.borrow().ident => true,
                            _ => false,
                        }
                    } else {
                        panic!("Field {} does not exist on {:#?}", &f.0, st);
                    }
                }
                _ => panic!("Field access on {:#?} is illegal", l_ty)
            }
        }
        Expr::ListConstructor() => match ty {
            ResolvedType::List(_) => true,
            _ => false,
        }
        Expr::StringLiteral(_) => match ty {
            ResolvedType::String => true,
            _ => false,
        }
        _ => false,
    }
}

fn infer_type(context: &Context, expr: &Expr) -> Option<ResolvedType> {
    match expr {
        Expr::Symbol(s) => {
            if let Some(t) = context.global.borrow().lookup(&s.0, None) {
                return Some(t.clone())
            } else if let Some(t) = context.symbols.get(&s.0) {
                return Some(t.clone())
            } else {
                return None
            }
        }
        Expr::Lambda(_, e) => {
            Some(ResolvedType::Function(box ResolvedType::Unit, box infer_type(context, e)?))
        }
        Expr::Application(lhs, rhs) => {
            let lhs_ty = infer_type(context, lhs)?;

            match lhs_ty {
                ResolvedType::Function(a, b) => {
                    if check_type(context, rhs, &a) {
                        return Some(*b.clone())
                    } else {
                        panic!("Expected {:#?}, found {:#?}", a, rhs);
                    }
                },
                _ => panic!("Tried to apply to non-function value {:#?}", lhs_ty)
            }
        }
        _ => None,
    }
}

fn generate_c_typeclass_variant(
    symbols: Rc<RefCell<GlobalSymbols>>,
    class: &untyped::ClosedTypeClass,
    variant: Option<String>,
) {
    let typename = match variant {
        None => class.ident.0.clone(),
        Some(ref p) => format!("{}_p_{}", class.ident.0, p),
    };

    let tc = typed::ClosedTypeClass {
        ident: typename.clone(),
        methods: Vec::new(),
        impls: Vec::new(),
        members: Vec::new(),
    };

    let tc = Rc::new(RefCell::new(tc));

    symbols
        .borrow_mut()
        .c_typeclass_instances
        .insert(typename.clone(), tc.clone());
    symbols
        .borrow_mut()
        .type_aliases
        .insert(typename, ResolvedType::ClosedTypeClass(tc.clone()));

    let mut ctx = Context {
        symbols: HashMap::new(),
        global: symbols.clone(),
        parent: None,
    };

    ctx.symbols.insert("Self".to_owned(), ResolvedType::ClosedTypeClass(tc.clone()));

    for m in class.typeclass_members.iter() {
        tc.borrow_mut().members.push((
            m.ident.0.clone(),
            resolve_type(&ctx, &m.ty, variant.as_ref()),
        ));
    }
}

fn resolve_type(ctx: &Context, ty: &untyped::Ty, variant: Option<&String>) -> typed::ResolvedType {
    match ty {
        Ty::Tuple(tys) => {
            ResolvedType::Tuple(tys.iter().map(|t| resolve_type(ctx, t, variant)).collect())
        }
        Ty::Sum(variants) => ResolvedType::Sum(Rc::new(RefCell::new(SumType {
            ident: String::new(), // DISGUSTING
            variants: variants
                .iter()
                .map(|(n, t)| (n.to_string(), resolve_type(ctx, t, variant)))
                .collect(),
        }))),
        Ty::Func(a, b) => ResolvedType::Function(
            box resolve_type(ctx, &a, variant),
            box resolve_type(ctx, &b, variant),
        ),
        Ty::Record(record) => ResolvedType::Record(RecordType {
            c_typeclass: None,
            fields: record
                .fields
                .iter()
                .flat_map(|(i, t, a)| {
                    if a.is_some() && a.as_ref().map(|s| &s.0) != variant {
                        None
                    } else {
                        Some((i.0.clone(), resolve_type(ctx, t, variant)))
                    }
                })
                .collect(),
        }),
        Ty::TypeRef(n, p) => {
            let (n, p) = (n, p.clone().map(|s| s.0.clone()));

            if let Some(t) = ctx.symbols.get(n) {
                return t.clone();
            }

            ctx.global
                .borrow()
                .lookup(n, p.clone())
                .expect(&format!("Couldn't find {}_p_{:?} in {:#?}", n, p, ctx))
                .clone()
        }
        Ty::List(t) => ResolvedType::List(box resolve_type(ctx, t, variant)),
        Ty::Unit => ResolvedType::Unit,
        Ty::Int => ResolvedType::Int,
        Ty::Float => ResolvedType::Float,
        Ty::String => ResolvedType::String,
        _ => {
            dbg!(ty);
            unimplemented!()
        }
    }
}

fn typecheck(ast: Untyped) -> Context<'static> {
    let global_symbols = Rc::new(RefCell::new(GlobalSymbols::new()));
    let mut context = Context {
        symbols: HashMap::new(),
        parent: None,
        global: global_symbols.clone(),
    };

    for d in ast.declarations.into_iter() {
        match d {
            Declaration::Type(ty) => {
                let t = resolve_type(&context, &ty.ty, None);
                if let ResolvedType::Sum(st) = &t {
                    st.borrow_mut().ident = ty.ident.0.clone();
                }

                global_symbols
                    .borrow_mut()
                    .type_aliases
                    .insert(ty.ident.0, t);
            }
            Declaration::TypeAnnotation(ident, ty) => {
                context
                    .symbols
                    .insert(ident.0, resolve_type(&context, &ty, None));
            }
            Declaration::ClosedTypeClass(tc) => {
                if let Some((_, variants)) = &tc.value_param {
                    for v in variants {
                        generate_c_typeclass_variant(
                            global_symbols.clone(),
                            &tc,
                            Some(v.0.clone()),
                        );
                    }
                } else {
                    generate_c_typeclass_variant(global_symbols.clone(), &tc, None);
                }
            }
            Declaration::Binding(ident, expr) => {
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

    return context;
}

fn main() {
    let file = std::fs::read_to_string("basic.ml").unwrap();

    let tokens = Scanner::new(file.chars()).scan_all().unwrap();

    let ast = parser::Parser::new(&tokens).parse().unwrap();

    // dbg!(&ast);

    let typechecked = typecheck(ast);

    dbg!(typechecked);
}
