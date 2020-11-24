


mul3 :: Int -> Int -> Int -> Int
mul3 a b c =
    a * b * c

mul3 a =
    \b -> (\c -> a * b * c)


.mul3 .params a
    .lambda .params b
        .lambda .params c
            .loads a
            .loads b
            .imul
            .loads c
            .imul

.mul3 [a: Int]
    .lambda [b: Int] .captures [a]
        .lambda [c: Int] .captures [a. b]
            .iload a
            .iload b
            .imul
            .iload c
            .imul

.def mul3 [a: Int]
    .def $0 [a, b, c]
		a * b * c

	.def $1 [a, b]
		.partial $0 [a, b]

	.partial $1 [a]


mul a b =
	a * b

main () =
	mul 3 5

.def mul [a: Int]
	.def $0 [a, b]
		a * b

	.partial $0 [a]

.def main
	.iconst 3
	.call mul

	.iconst 5
	.apply



# capturing



foo :: Int -> Int -> Int
foo a =
	print a
	\b ->
		print b
		b

.def foo [a: Int]
	.load %a
	.call print

	.lambda $0 [b: Int]
		.load b
		.ret

	.ret




foo :: Int -> Int -> Int
foo a =
	print a
	\b ->
		print b
		a * b

.def foo [a: Int]
	.load %a
	.call print

	.lambda $0 [b: Int]
		.load b
		.ret

	.ret
