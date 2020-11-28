use std::{cell::RefCell, collections::HashMap, fmt::Debug, rc::Rc};

use super::untyped;

#[derive(Debug, Clone)]
pub enum TypeDefinition {
    Record {
        qualified_name: Rc<String>,
        fields: Vec<(String, ResolvedType)>,
    },
    Sum {
        qualified_name: Rc<String>,
        variants: Vec<(String, ResolvedType)>,
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
}

#[derive(Debug, Clone)]
pub struct TypeEnvironment {
    pub types: Vec<TypeDefinition>,
    pub type_aliases: HashMap<String, ResolvedType>,
}

impl TypeEnvironment {
    pub fn new() -> Self {
        Self {
            types: Vec::new(),
            type_aliases: HashMap::new(),
        }
    }
}

#[derive(Clone)]
pub struct TypeHandle {
    pub qualified_name: Rc<String>,
    pub index: usize,
    pub environment: Rc<RefCell<TypeEnvironment>>,
}

impl Debug for TypeHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TypeHandle")
            .field("qualified_name", &self.qualified_name)
            .field("index", &self.index)
            .finish()
    }
}

impl PartialEq for TypeHandle {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

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

#[derive(Debug, Clone, PartialEq)]
pub enum ResolvedType {
    TypeHandle(TypeHandle),
    Function(Box<ResolvedType>, Box<ResolvedType>),
    Tuple(Vec<ResolvedType>),
    List(Box<ResolvedType>),
    Unit,
    Int,
    Float,
    String,
    ErrType, // indicates that type checking previously failed
}

#[derive(Debug, Clone)]
pub enum ExprT {
    Lambda(String, Box<TypedExpr>),
    StringLiteral(String),
    Record(Vec<TypedExpr>),
    ListConstructor(),
    VariantConstructor(TypeHandle, usize),
    Application(Box<TypedExpr>, Box<TypedExpr>),
    Symbol(String),
    FieldAccess(Box<TypedExpr>, usize),
    LetBinding(String, Box<TypedExpr>, Box<TypedExpr>),
    Tuple(Vec<TypedExpr>),
    Unit,
    MatchSum(Box<TypedExpr>, Vec<(usize, Option<String>, TypedExpr)>),
    BinaryOp(untyped::Operator, Box<TypedExpr>, Box<TypedExpr>),
    IntegerLiteral(i64),
}

pub type TypedExpr = (ExprT, ResolvedType);
