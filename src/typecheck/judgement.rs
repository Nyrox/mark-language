use super::{constraints::Constraint, constraints::TypeSet, TypeCheckingError};
use crate::ast::typed::TypedExpr;

use std::iter::FromIterator;
use std::ops::{Try, ControlFlow};

pub enum TypeJudgement<T> {
    Typed {
        inner: T,
        constraints: Vec<Constraint>,
    },
    Error(TypeCheckingError),
}

impl<T1> TypeJudgement<T1> {
    pub fn new(inner: T1) -> TypeJudgement<T1> {
        TypeJudgement::Typed {
            inner,
            constraints: Vec::new(),
        }
    }

    pub fn ok(self) -> Option<T1> {
        match self {
            TypeJudgement::Typed { inner, .. } => Some(inner),
            TypeJudgement::Error(_) => None,
        }
    }

    pub fn and_still<T2, F>(self, f: F) -> TypeJudgement<(T1, T2)>
    where
        F: FnOnce() -> TypeJudgement<T2>,
    {
        self.and(f())
    }

    pub fn then<T2, F>(self, f: F) -> TypeJudgement<(T1, T2)>
    where
        F: FnOnce(&T1) -> TypeJudgement<T2>,
    {
        match self {
            TypeJudgement::Typed { inner, constraints } => {
                let other = f(&inner);
                TypeJudgement::Typed { inner, constraints }.and(other)
            }
            TypeJudgement::Error(e) => TypeJudgement::Error(e),
        }
    }

    pub fn map_with_fail<T2, F>(self, f: F) -> TypeJudgement<T2>
    where
        F: FnOnce(T1) -> Result<T2, TypeCheckingError>,
    {
        match self {
            TypeJudgement::Typed { inner, constraints } => match f(inner) {
                Ok(inner) => TypeJudgement::Typed { inner, constraints },
                Err(e) => TypeJudgement::Error(e),
            },
            TypeJudgement::Error(e) => TypeJudgement::Error(e),
        }
    }

    pub fn map_with_constraints<T2, F>(self, f: F) -> TypeJudgement<T2>
    where
        F: FnOnce(T1, Vec<Constraint>) -> (T2, Vec<Constraint>),
    {
        match self {
            TypeJudgement::Typed { inner, constraints } => {
                let (ni, nc) = f(inner, constraints);
                TypeJudgement::Typed {
                    inner: ni,
                    constraints: nc,
                }
            }
            TypeJudgement::Error(e) => TypeJudgement::Error(e),
        }
    }

    pub fn map_with_constraints_and_fail<T2, F>(self, f: F) -> TypeJudgement<T2>
    where
        F: FnOnce(T1, Vec<Constraint>) -> Result<(T2, Vec<Constraint>), TypeCheckingError>,
    {
        match self {
            TypeJudgement::Typed { inner, constraints } => match f(inner, constraints) {
                Ok((inner, constraints)) => TypeJudgement::Typed { inner, constraints },
                Err(e) => TypeJudgement::Error(e),
            },
            TypeJudgement::Error(e) => TypeJudgement::Error(e),
        }
    }

    pub fn iter_err<F>(self, f: F) -> Self
    where
        F: FnOnce(&TypeCheckingError) -> (),
    {
        match self {
            TypeJudgement::Typed { .. } => self,
            TypeJudgement::Error(ref err) => {
                f(err);
                self
            }
        }
    }

    pub fn and<T2>(self, other: TypeJudgement<T2>) -> TypeJudgement<(T1, T2)> {
        use TypeJudgement::*;
        match (self, other) {
            (Error(e1), Error(e2)) => Error(TypeCheckingError::compound(e1, e2)),
            (Typed { .. }, Error(e)) => Error(e),
            (Error(e), Typed { .. }) => Error(e),
            (
                Typed {
                    inner: i1,
                    constraints: c1,
                },
                Typed {
                    inner: i2,
                    constraints: c2,
                },
            ) => TypeJudgement::Typed {
                inner: (i1, i2),
                constraints: c1.into_iter().chain(c2.into_iter()).collect(),
            },
        }
    }

    pub fn map<F, TN>(self, f: F) -> TypeJudgement<TN>
    where
        F: FnOnce(T1) -> TN,
    {
        match self {
            TypeJudgement::Typed { inner, constraints } => TypeJudgement::Typed {
                inner: f(inner),
                constraints,
            },
            TypeJudgement::Error(e) => TypeJudgement::Error(e),
        }
    }

    pub fn add_constraint<F>(mut self, f: F) -> TypeJudgement<T1>
    where
        F: FnOnce(&T1) -> Constraint,
    {
        match &mut self {
            TypeJudgement::Typed { inner, constraints } => constraints.push(f(inner)),
            _ => (),
        }

        self
    }
}

impl<T> FromIterator<TypeJudgement<T>> for TypeJudgement<Vec<T>> {
    fn from_iter<I: IntoIterator<Item = TypeJudgement<T>>>(iter: I) -> TypeJudgement<Vec<T>> {
        let mut ts = Vec::new();
        let mut cs = Vec::new();
        let mut error = None;

        for i in iter {
            match i {
                TypeJudgement::Typed {
                    inner,
                    mut constraints,
                } => {
                    ts.push(inner);
                    cs.append(&mut constraints);
                }
                TypeJudgement::Error(e) => {
                    error = match error {
                        Some(e2) => Some(TypeCheckingError::compound(e2, e)),
                        None => Some(e),
                    }
                }
            }
        }

        match error {
            Some(e) => TypeJudgement::Error(e),
            None => TypeJudgement::Typed {
                inner: ts,
                constraints: cs,
            },
        }
    }
}

impl<T> Try for TypeJudgement<T> {
    type Output = (T, Vec<Constraint>);
    type Residual = TypeJudgement<std::convert::Infallible>;

    fn from_output(output: Self::Output) -> Self {
        let (inner, constraints) = output;
        TypeJudgement::Typed { constraints, inner }
    }

    fn branch(self) -> std::ops::ControlFlow<Self::Residual, Self::Output> {
        match self {
            TypeJudgement::Typed { inner, constraints } => ControlFlow::Continue((inner, constraints)),
            TypeJudgement::Error(e) => ControlFlow::Break(TypeJudgement::Error(e))
        }
    }
}

impl<T> std::ops::FromResidual for TypeJudgement<T> {
    fn from_residual(residual: TypeJudgement<std::convert::Infallible>) -> Self {
        match residual {
            TypeJudgement::Error(e) => TypeJudgement::Error(e),
            TypeJudgement::Typed { inner, .. } => match inner {}
        }
    }
}



impl TypeJudgement<TypedExpr> {
    pub fn solve_constraints(self) -> TypeJudgement<(TypedExpr, TypeSet)> {
        self.map_with_constraints_and_fail(|expr, constraints| {
            let typeset = super::constraints::solve(constraints.clone())?;
            let expr = super::constraints::apply_typeset(expr, &typeset);
            Ok(((expr, typeset), constraints))
        })
    }
}
