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


type Test = {
  str: String
}

create_rec :: String -> Test
create_rec blah =
  { str: blah }


//main () =
//    (create_rec "din mor").str


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
  { a: (f "two").a, b: (f "two").b, c: c }


main () =
  test_curry (test "one") "three"