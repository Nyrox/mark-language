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

typecheck :: Expr<Parsed> -> Expr<TypeChecked>
typecheck expr =
	match expr with
	| FuncCall f -> FuncCall { retType: TypeKind.I32, ..f }


main () =
	typecheck (FuncCall { ident: ("foo", (0, 0)), params: [] })

