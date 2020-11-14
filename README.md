Experimenting with advanced type systems

```ml
type Span = (Int, Int)
type Spanned 't = ('t, Span)

type TypeKind =
  | I32
  | F32
  | TypeRef of String

closed typeclass Expr<Phase: Parsed | Typechecked> begin
  sourceSpan :: Self -> Span

  [TypeChecked]
  exprType :: Self -> TypeKind


  type FuncCall = {
    ident: Spanned String,
    params: Expr<Phase> List,
    [TypeChecked]
    retType: TypeKind,
  }

  impl sourceSpan for FuncCall f = f.ident.1
  impl exprType for FuncCall f = f.retType

  ...

end
```
