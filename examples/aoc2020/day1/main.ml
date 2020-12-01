


type SList =
	| Cons of (String, SList)
	| Nil


collect :: String -> String -> SList
collect sep input =
	if input == "" then
		SList.Nil
	else
		let split = String_split (input, sep)
		SList.Cons (split.0, collect sep split.1)

map :: (String -> ()) -> SList -> ()
map f list =
	match list with
	| Cons sl ->
		let _ =  f sl.0
		map f sl.1
	| Nil -> ()

main () =
	let input = File_read "./input"
	let list = collect "\r\n" input
	map (\s -> println s) list
