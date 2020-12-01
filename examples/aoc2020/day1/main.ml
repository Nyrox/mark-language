


type IList =
	| Cons of (Int, IList)
	| Nil


collect :: String -> String -> IList
collect sep input =
	if input == "" then
		IList.Nil
	else
		let split = String_split (input, sep)
		IList.Cons (String_parse_int split.0, collect sep split.1)

type IOption =
	| Some of Int
	| None


iter_while :: (Int -> IOption) -> IList -> IOption
iter_while f list =
	match list with
	| Cons cons ->
		match f cons.0 with
		| Some s -> IOption.Some s
		| None -> iter_while f cons.1
		end
	| Nil -> IOption.None


zip :: ((Int, Int, Int) -> IOption) -> IList -> IList -> IList -> IOption
zip f a b c =
	iter_while (\ia ->
		let _ = printi ia
		let _ = print "\n"
		iter_while (\ib ->
			iter_while (\ic ->
				f (ia, ib, ic)
			) c
		) b
	) a


main () =
	let input = File_read "./input"
	let ilist = collect "\r\n" input
	zip (\ip ->
		if ip.0 + ip.1 + ip.2 == 2020 then
			IOption.Some (ip.0 * ip.1 * ip.2)
		else
			IOption.None
		) ilist ilist ilist
