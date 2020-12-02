
type Input = {
	min: Int,
	max: Int,
	pred: String,
	input: String
}

type IList =
	| Cons of (Input, IList)
	| Nil

parse_line :: String -> Input
parse_line line =
	let min_split = String_split (line, "-")
	let max_split = String_split (min_split.1, " ")
	let pred_split = String_split (max_split.1, ": ")
	{
		min: String_parse_int min_split.0,
		max: String_parse_int max_split.0,
		pred: pred_split.0,
		input: pred_split.1
	}

parse :: String -> IList
parse input =
	if input == "" then
		IList.Nil
	else
		let split = String_split (input, "\r\n")
		IList.Cons (
			parse_line split.0,
			parse split.1
		)


count_bools :: (Input -> Bool) -> IList -> Int
count_bools f list =
	match list with
	| Cons cons ->
		if f cons.0 then
			(count_bools f cons.1) + 1
		else
			(count_bools f cons.1)
	| Nil -> 0


count_substr :: String -> String -> Int
count_substr sub haystack =
	if haystack == "" then
		0
	else
		let split = String_get_first haystack
		if split.0 == sub then
			1 + count_substr sub split.1
		else
			count_substr sub split.1


main () =
	let input = File_read "./input"
	let input_parsed = parse input

	count_bools (\elem ->
		let count = count_substr elem.pred elem.input
		count >= elem.min and count <= elem.max
		) input_parsed
