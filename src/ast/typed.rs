use std::{cell::RefCell, collections::HashMap, fmt::Debug, rc::Rc};

use super::untyped;

#[derive(Debug, Clone)]
pub enum TypeDefinition {
    Record {
        qualified_name: Rc<String>,
        type_parameters: Vec<String>,
        fields: Vec<(String, Type)>,
    },
    Sum {
        qualified_name: Rc<String>,
        type_parameters: Vec<String>,
        variants: Vec<(String, Type)>,
    },
    ClosedTypeClassInstance {
        qualified_name: Rc<String>,
        methods: Vec<NamedFuncSig>,
        impls: Vec<TypeClassImplItem>,
        members: Vec<TypeHandle>,
    },
}

impl TypeDefinition {
    pub fn qualified_name(&self) -> Rc<String> {
        match self {
            TypeDefinition::Record { qualified_name, .. } => qualified_name.clone(),
            TypeDefinition::Sum { qualified_name, .. } => qualified_name.clone(),
            TypeDefinition::ClosedTypeClassInstance { qualified_name, .. } => {
                qualified_name.clone()
            }
        }
    }

    pub fn generic_arity(&self) -> usize {
        use TypeDefinition::*;

        match self {
            Record {
                type_parameters, ..
            } => type_parameters.len(),
            Sum {
                type_parameters, ..
            } => type_parameters.len(),
            ClosedTypeClassInstance { .. } => 0,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct TypeEnvironment {
    pub root_scope: Scope,
    pub scopes: HashMap<String, Scope>,
    pub types: Vec<TypeDefinition>,
}



#[derive(Clone, Debug, Default)]
pub struct Scope {
    pub bindings: HashMap<String, Kind>,
    pub type_constructors: HashMap<String, TypeConstructor>,
}

#[derive(Clone)]
pub struct TypeHandle {
    pub index: usize,
    pub environment: Rc<RefCell<TypeEnvironment>>,
}

impl Debug for TypeHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "UT:{}",
            self.environment.borrow().types[self.index].qualified_name()
        ))
    }
}

impl PartialEq for TypeHandle {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl Eq for TypeHandle {}

#[derive(Debug, Clone)]
pub struct NamedFuncSig {
    pub ident: String,
    pub sig: (Type, Type),
}

#[derive(Debug, Clone)]
pub struct TypeClassImplItem {
    pub what: String,
    pub who: String,
    pub body: untyped::Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeConstructor {
    Tuple(usize),
    UserType(TypeHandle),
    Function,
    Int,
    Float,
    String,
    Bool,
    Unit,
}

impl TypeConstructor {
    pub fn arity(&self) -> usize {
        use TypeConstructor::*;

        match self {
            Tuple(n) => *n,
            UserType(th) => th.environment.borrow().types[th.index].generic_arity(),
            Function => 2,
            Int | Float | String | Bool | Unit => 0,
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum Type {
    TypeVariable(u32),
    ConstructedType(TypeConstructor, Vec<Type>),
    ErrType, // indicates that type checking failed
}

#[derive(Clone, PartialEq, Eq)]
pub enum Kind {
    TypeSchema(Vec<String>, Type),
    Type(Type),
}

impl Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::ErrType => f.write_str("ErrType"),
            Type::TypeVariable(s) => f.write_fmt(format_args!("'{}", s)),
            Type::ConstructedType(tc, tys) => {
                f.write_fmt(format_args!("{:?} ", tc))?;
                if tys.len() != 0 {
                    f.debug_list().entries(tys.iter()).finish()
                } else {
                    Ok(())
                }
            }
        }
    }
}

impl Type {
    pub const INT: Type = Self::primitive(TypeConstructor::Int);
    pub const FLOAT: Type = Self::primitive(TypeConstructor::Float);
    pub const STRING: Type = Self::primitive(TypeConstructor::String);
    pub const BOOL: Type = Self::primitive(TypeConstructor::Bool);
    pub const UNIT: Type = Self::primitive(TypeConstructor::Unit);

    pub const fn primitive(tc: TypeConstructor) -> Type {
        Type::ConstructedType(tc, vec![])
    }

    pub fn function(a: Type, b: Type) -> Type {
        Type::ConstructedType(TypeConstructor::Function, vec![a, b])
    }

    pub fn tuple(tys: Vec<Type>) -> Type {
        Type::ConstructedType(TypeConstructor::Tuple(tys.len()), tys)
    }

    pub fn user_type(th: TypeHandle, params: Vec<Type>) -> Type {
        Type::ConstructedType(TypeConstructor::UserType(th), params)
    }

    pub fn type_constructor(&self) -> Option<&TypeConstructor> {
        match self {
            Type::ConstructedType(ref tc, _) => Some(tc),
            _ => None,
        }
    }
}

impl Type {
    pub fn is_generic(&self) -> bool {
        use Type::*;

        match self {
            TypeVariable(_) => true,
            ConstructedType(_, tys) => tys
                .iter()
                .map(Self::is_generic)
                .fold(false, |acc, a| acc || a),
            ErrType => false,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum BuiltInFn {
    FileRead,
    StringSplit,
    StringParseInt,
    StringGetFirst,
    Printi,
    Print,
}

impl BuiltInFn {
    pub fn resolved_type(&self) -> Type {
        use BuiltInFn::*;

        match self {
            FileRead => Type::function(Type::STRING, Type::STRING),
            StringSplit => Type::function(
                Type::tuple(vec![Type::STRING, Type::STRING]),
                Type::tuple(vec![Type::STRING, Type::STRING]),
            ),
            StringParseInt => Type::function(Type::STRING, Type::INT),
            StringGetFirst => {
                Type::function(Type::STRING, Type::tuple(vec![Type::STRING, Type::STRING]))
            }
            Print => Type::function(Type::STRING, Type::UNIT),
            Printi => Type::function(Type::INT, Type::UNIT),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ExprT {
    Conditional(Box<TypedExpr>, Box<TypedExpr>, Box<TypedExpr>),
    Lambda(String, Box<TypedExpr>),
    BinaryOp(untyped::Operator, Box<TypedExpr>, Box<TypedExpr>),
    MatchSum(Box<TypedExpr>, Vec<(usize, Option<String>, TypedExpr)>),
    Record(Vec<TypedExpr>),
    Tuple(Vec<TypedExpr>),
    Application(Box<TypedExpr>, Vec<TypedExpr>),
    FieldAccess(Box<TypedExpr>, usize),
    LetBinding(String, Box<TypedExpr>, Box<TypedExpr>),
    Symbol(String),
    VariantConstructor(TypeHandle, usize),
    StringLiteral(String),
    IntegerLiteral(i64),
    BooleanLiteral(bool),
    BuiltInFn(BuiltInFn),
    Unit,
}

pub type TypedExpr = (ExprT, Type);
