type Span = (Int, Int, ())
//type Spanned 't = ('t, Span)

type TypeKind =
  | I32
  | F32
  | TypeRef of String

closed typeclass Expr<Phase: Parsed | TypeChecked> begin
  sourceSpan :: Self -> Span -> (Foo -> Bar, Int)

  [TypeChecked]
  exprType :: Self -> TypeKind


  type FuncCall = {
    ident: String,
    params: String[],
    [TypeChecked]
    retType: TypeKind
  }

  impl sourceSpan for FuncCall f = f.ident.1
  impl exprType for FuncCall f = f.retType
end

typecheck :: Expr<Parsed> -> Expr<TypeChecked>
typecheck expr =
	{ ident: "bruh", retType: TypeKind.I32, params: [] }


type Test2 = {
  a: String,
  b: String
}

type Test3 = {
  a: String,
  b: String,
  c: String
}

test :: String -> String -> Test2
test a b =
  { a: a, b: b }

test_curry :: (String -> Test2) -> String -> Test3
test_curry f c =
	let r = f "two"
  	{ a: r.a, b: r.b, c: c }


main () =
	let b =
		let r = "cyka"
		r

	test_curry (\a ->
		{ a: a, b: "blyat" }
	) b


