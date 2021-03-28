use crate::{
    ast::typed::{Type, TypedExpr},
    parser::Span,
};

use super::TypeCheckingError;

#[derive(Debug, Clone)]
pub enum Constraint {
    TypeParameterIsType(u32, Type),
}

#[derive(Debug, Clone)]
pub struct Element {
    pub parent: Option<usize>,
    pub ty: Option<Type>,
}

#[derive(Debug, Clone)]
pub struct TypeSet {
    elements: Vec<Option<Element>>,
}

impl TypeSet {
    pub fn new() -> TypeSet {
        TypeSet {
            elements: Vec::new(),
        }
    }

    pub fn apply(expr: TypedExpr) -> TypedExpr {
        expr
    }

    pub fn add_constraint(&mut self, constraint: Constraint) -> Result<(), TypeCheckingError> {
        match constraint {
            Constraint::TypeParameterIsType(p, t) => self.c_param_is_type(p as usize, t),
        }
    }

    pub fn find(&self, mut i: usize) -> Option<(usize, &Element)> {
        if i >= self.elements.len() {
            return None;
        }

        let mut elem = self.elements[i].as_ref();

        loop {
            if let Some(e) = elem {
                if let Some(p) = e.parent {
                    i = p;
                    elem = self.elements[i].as_ref();
                } else {
                    break;
                }
            } else {
                break;
            }
        }

        elem.map(|e| (i, e))
    }

    pub fn find_mut(&mut self, mut i: usize) -> Option<(usize, &mut Element)> {
        let (i, _) = self.find(i)?;
        self.elements.get_mut(i).unwrap().as_mut().map(|e| (i, e))
    }

    pub fn grab(&mut self, i: usize) -> (usize, &mut Element) {
        if self.find_mut(i).is_some() {
            self.find_mut(i).unwrap()
        } else {
            if self.elements.len() <= i {
                self.elements.resize(i + 1, None);
            }

            self.elements[i] = Some(Element {
                parent: None,
                ty: None,
            });
            (i, self.elements[i].as_mut().unwrap())
        }
    }

    pub fn union(&mut self, a: usize, b: usize) {
        if self.elements.len() <= a.max(b) {
            self.elements.resize(a.max(b) + 1, None);
        }

        let (a, _) = self.grab(a);
        let (b, _) = self.grab(b);

        // a and b are already the same set
        if a == b {
            return;
        }

        let ae = self.elements[a].as_ref().unwrap();
        let be = self.elements[b].as_ref().unwrap();

        let t = match (&ae.ty, &be.ty) {
            (Some(t1), Some(t2)) => {
                panic!()
            }
            (Some(e), None) | (None, Some(e)) => Some(e.clone()),
            (None, None) => None,
        };

        self.elements[a].as_mut().unwrap().ty = t;
        self.elements[b].as_mut().unwrap().ty = None;
        self.elements[b].as_mut().unwrap().parent = Some(a);
    }

    fn c_param_is_type(&mut self, p: usize, t: Type) -> Result<(), TypeCheckingError> {
        match &t {
            Type::TypeVariable(v) => {
                self.union(p, *v as usize);
            }
            Type::ErrType => {
                panic!()
            }
            Type::ConstructedType(ctor, tys) => {
                let (_, elem) = self.grab(p);

                if let Some(et) = elem.ty.as_mut() {
                    if *et != t {
                        Err(TypeCheckingError::TypeMismatch(
                            Span::empty(),
                            et.clone(),
                            Some(t),
                        ))?;
                    }
                } else {
                    elem.ty = Some(t);
                }
            }
        }

        Ok(())
    }
}

pub fn solve(constraints: Vec<Constraint>) -> Result<TypeSet, TypeCheckingError> {
    let mut typeset = TypeSet::new();

    for c in constraints {
        typeset.add_constraint(c)?;
    }

    Ok(typeset)
}

pub fn apply_typeset(expr: TypedExpr, typeset: &TypeSet) -> TypedExpr {
    dbg!(typeset);
    expr
}
