Experimenting with advanced type systems, featuring Closed type classes, i.e. type classes whose members are known at declaration time to allow for exhaustive pattern matching.

Planned:

- [ ] Pattern Matching closed type classes
- [ ] Simple generic type constructors

Maybe Planned:

- [ ] Generic Functors aka. Module Generics á la Ocaml
- [ ] Refinement Types

Implemented:
- [x] Bi-Directional Type Checker allowing for large scale inference just from top-level annotation
- [x] Closed Type Classes
- [x] Variant Polymorphism, allowing closed type classes to declare multiple variants and conditionally compile types and methods based on those variants
- [x] Functions as first-class objects
- [x] Partial Function Application and Currying
- [x] Full algebraic data types, including pattern matching on union types
- [x] Simple and mutual function recursion
- [x] Recursive data types


Current progress: This program **runs**

```ml
type Row =
	| Cons of (Bool, Row)
	| Nil

type Map =
	| Cons of (Row, Map)
	| Nil


parse_row :: String -> Row
parse_row input =
	if input == "" then
		Row.Nil
	else
		let split = String_get_first input
		Row.Cons (split.0 == "#", parse_row split.1)

parse :: String -> Map
parse input =
	if input == "" then
		Map.Nil
	else
		let split = String_split (input, "\r\n")
		Map.Cons (parse_row split.0, parse split.1)


row_len :: Row -> Int
row_len row =
	match row with
	| Cons m -> row_len m.1 + 1
	| Nil -> 0


get_nth_elem :: Row -> Int -> Bool
get_nth_elem row n =
	match row with
	| Cons r ->
		if n == 0 then
			r.0
		else
			get_nth_elem r.1 (n - 1)

has_tree :: Row -> Int -> Bool
has_tree row xpos =
	let len = row_len row
	get_nth_elem row (xpos % len)


type Slope = (Int, Int)


traverse_map_inner :: Map -> Slope -> Int -> Int -> Int
traverse_map_inner map slope xpos ypos =
	match map with
	| Cons m ->
		if ypos % slope.1 == 0 then
			let rest = traverse_map_inner m.1 slope (xpos + slope.0) (ypos + 1)
			if has_tree m.0 xpos then
				1 + rest
			else
				rest
		else
			// skip rows that are not described by the slope
			traverse_map_inner m.1 slope xpos (ypos + 1)
	| Nil ->
		0 // we are done

traverse_map :: Map -> Slope -> Int
traverse_map map slope =
	traverse_map_inner map slope 0 0

main () =
	let input = File_read "./input"
	let map = parse input

	let results = (
		traverse_map map (1, 1),
		traverse_map map (3, 1),
		traverse_map map (5, 1),
		traverse_map map (7, 1),
		traverse_map map (1, 2)
	)

	results.0 * results.1 * results.2 * results.3 * results.4

```
