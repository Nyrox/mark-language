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


test_curry :: String -> String -> () -> (String, String)
test_curry a b =
	\_ -> (a, b)


test :: (() -> (String, String)) -> String -> (String, String, String)
test f c =
	let r = f ()
	(r.0, r.1, c)


type SOption =
	| Some of String
	| None

main_options :: () -> String
main_options () =
	// test (test_curry "din" "mor") "gey"
	let opt = SOption.Some "din mor"
	// let opt = SOption.None
	match opt with
	| Some s -> (test (test_curry "din" "mor") s).2
	| None -> "Wasn't"

type SList =
	| Cons of (String, SList)
	| End

main_lists () =
	let list = SList.Cons ("mor", SList.Cons ("din", SList.End))
	list


double :: Int -> Int
double x = x + x

test_nums_ops :: () -> Int
test_nums_ops () =
	(5 - 2) * double 7 + 3 * 7 + 9 / 2


main () =
	test_nums_ops ()
