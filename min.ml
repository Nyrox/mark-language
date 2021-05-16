


identity :: 'a -> 'a
identity i = i

main () =
    let id = (\x -> x)
    identity (id 5, id "test", identity (7, "bruh))