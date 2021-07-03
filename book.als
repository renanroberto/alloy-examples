module Book

sig Name, Addr {}

sig Book {
	addr : Name -> lone Addr
}


pred add(b, b' : Book, n : Name, a : Addr) {
	b'.addr = b.addr + (n -> a)
}
run add for 3 but 2 Book

pred del(b, b' : Book, n : Name) {
	all a : Addr | b'.addr = b.addr - (n -> a)
}
run del for 3 but exactly 2 Book


fun lookup(b : Book, n : Name) : set Addr {
	n.(b.addr)
}


assert delUndoesAdd {
	all b, b', b'' : Book, n : Name, a : Addr |
		( no n.(b.addr)
		 and add[b, b', n, a]
		 and del[b', b'', n]
		 ) implies b.addr = b''.addr
}
check delUndoesAdd for 10

assert addIdempotent {
	all b, b', b'' : Book, n : Name, a : Addr |
		add[b, b', n, a] and add[b', b'', n, a] implies
		b'.addr = b''.addr		
}
check addIdempotent for 10

assert addLocal {
	all b, b' : Book, disj n, n' : Name, a : Addr |
		add[b, b', n, a] implies
		lookup[b, n'] = lookup[b', n']
}
check addLocal for 10


pred show() {}
run show for 3 but exactly 1 Book
