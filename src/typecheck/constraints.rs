use crate::ast::typed::{Type, TypedExpr};

use super::TypeCheckingError;



#[derive(Debug, Clone)]
pub enum Constraint {
    TypeParameterIsType(u32, Type),
}


#[derive(Debug, Clone)]
struct Element {
    pub parent: Option<usize>,
    pub ty: Option<Type>,
}

#[derive(Debug, Clone)]
pub struct TypeSet {
    elements: Vec<Option<Element>>,
}

impl TypeSet {
    pub fn apply(expr: TypedExpr) -> TypedExpr {

        expr
    }

    pub fn add_constraint(&mut self, constraint: Constraint) -> Result<(), TypeCheckingError> {
        match constraint {
            Constraint::TypeParameterIsType(p, t) => self.c_param_is_type(p, t),
        }
    }


    fn c_param_is_type(&mut self, p: u32, t: Type) -> Result<(), TypeCheckingError> {

        ()
    }
}

pub fn solve(constraints: Vec<Constraint>) -> Result<TypeSet, TypeCheckingError> {
    let typeset = TypeSet::new();
    
    for c in constraints {
        typeset.add_constraint(c)?;
    }
    
    Ok(typeset)
}

