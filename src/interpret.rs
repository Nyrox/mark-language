use std::collections::HashMap;

use crate::{ast::typed::TypedExpr, ast::typed::*, typecheck::TypeChecked};

#[derive(Debug, Clone)]
pub enum Value {
    Unit,
    Tuple(Vec<Value>),
    Function(String, Vec<(String, Value)>, TypedExpr),
    String(String),
    Variant(TypeHandle, usize, Box<Value>),
}

#[derive(Debug)]
struct Interpreter {
    stack: Vec<Value>,
    bindings: HashMap<String, Value>,
    program: TypeChecked,
}

impl Interpreter {
    pub fn push_val(&mut self, value: Value) {
        self.stack.push(value);
    }

    pub fn pop_val(&mut self) -> Option<Value> {
        self.stack.pop()
    }

    pub fn call_fn(&mut self, f: &str) {
        let (e, t) = self.program.bindings.get(f).unwrap();
        if let ExprT::Lambda(p, body) = e.clone() {
            self.eval_expr(&body)
        } else {
            panic!("Tried to call non function value {:?}", e);
        }
    }

    pub fn eval_expr(&mut self, (expr, et): &TypedExpr) {
        match expr {
            ExprT::Application(lhs, rhs) => {
                self.eval_expr(lhs);

                if let Some(Value::Function(p, curried, body)) = self.pop_val() {
                    for (i, e) in curried.clone() {
                        self.bindings.insert(i, e);
                    }

                    self.eval_expr(rhs);
                    let rv = self.pop_val().unwrap();
                    self.bindings.insert(p.clone(), rv);

                    self.eval_expr(&body);

                    self.bindings.remove(&p);
                    for (i, _) in curried {
                        self.bindings.remove(&i);
                    }
                } else {
                    dbg!(lhs, &self.stack, &self.bindings);
                    panic!("Not good")
                }
            }
            ExprT::Lambda(p, body) => {
                self.push_val(Value::Function(
                    p.clone(),
                    self.bindings.clone().into_iter().collect(),
                    *body.clone(),
                ));
            }
            ExprT::Symbol(s) => {
                if let Some(b) = self.program.bindings.get(s) {
                    if let (ExprT::Lambda(p, body), _) = b {
                        self.push_val(Value::Function(p.clone(), vec![], *body.clone()));
                    } else {
                        panic!()
                    }
                } else if let Some(b) = self.bindings.get(s).cloned() {
                    self.push_val(b);
                } else {
                    panic!()
                }
            }
            ExprT::Record(fields) => {
                let mut r = Vec::new();
                for f in fields {
                    self.eval_expr(f);
                    r.push(self.pop_val().unwrap());
                }
                self.push_val(Value::Tuple(r));
            }
            ExprT::StringLiteral(s) => {
                self.push_val(Value::String(s.clone()));
            }
            ExprT::ListConstructor() => {
                self.push_val(Value::Tuple(vec![]));
            }
            ExprT::VariantConstructor(th, vi) => {
                let t = self.program.environment.borrow().types[th.index].clone();
                if let TypeDefinition::Sum { variants, .. } = t {
                    let (n, vt) = &variants[*vi];
                    if let ResolvedType::Unit = vt {
                        self.push_val(Value::Variant(th.clone(), *vi, box Value::Unit));
                    } else {
                        panic!()
                    }
                } else {
                    panic!()
                }
            }
            ExprT::FieldAccess(lhs, i) => {
                self.eval_expr(lhs);

                if let Some(Value::Tuple(values)) = self.pop_val() {
                    self.push_val(values[*i].clone())
                } else {
                    panic!()
                }
            }
            ExprT::Unit => self.push_val(Value::Unit),
            _ => {
                dbg!(expr);
                unimplemented!()
            }
        }
    }
}

pub fn interpret(program: TypeChecked) {
    let mut interpreter = Interpreter {
        bindings: HashMap::new(),
        stack: Vec::new(),
        program,
    };

    interpreter.call_fn("main");

    dbg!(interpreter.pop_val());
}
