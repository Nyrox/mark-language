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

main_slists () =
	let list = SList.Cons ("mor", SList.Cons ("din", SList.End))
	list


double :: Int -> Int
double x = x + x

test_nums_ops :: () -> Int
test_nums_ops () =
	(5 - 2) * double 7 + 3 * 7 + 9 / 2


test_cond :: Int -> Int
test_cond i =
	if i > 5 then
		i + i
	else
		i * i


type Op =
	| Add of Int
	| Sub of Int

type OpList =
	| Cons of (Op, OpList)
	| Nil

apply_op :: Op -> Int -> Int
apply_op op a =
	match op with
	| Add b -> a + b
	| Sub b -> a - b

apply :: OpList -> Int -> Int
apply oplist init =
	match oplist with
	| Cons cons -> apply cons.1 (apply_op cons.0 init)
	| Nil -> init


type List 'a =
	| Cons of ('a, List 'a)
	| Nil



map :: ('a -> 'b) -> List 'a -> List 'b
map f list =
	match list with
	| Cons a ->
		List.Cons (f a.0, map f a.1)
	| Nil ->
		List.Nil



main () =
	let someList = List.Cons ("yo", List.Nil)
	map (\x -> print x) someList


main () =
	let ops = OpList.Cons (Op.Add 5, OpList.Cons (Op.Sub 3, OpList.Cons (Op.Add 7, OpList.Nil)))
	apply ops 10




