module Book2
open util/ordering[Book]

abstract sig Target {}
abstract sig Name extends Target {}

sig Addr extends Target {}
sig Alias, Group extends Name {}

sig Book {
	names : set Name,
	addr : names -> some Target	
}


pred init(b : Book) { no b.addr }

fact traces {
	init[first]
	all b : Book - last | let b' = next[b] |
		some n : Name, t : Target |
			add[b, b', n, t] or del[b, b', n, t]
}


pred add(b, b' : Book, n : Name, t : Target) {
	t in Addr or some lookup[b, t]
	b'.addr = b.addr + (n -> t)
}

pred del(b, b' : Book, n : Name, t : Target) {
	no b.addr.n or some n.(b.addr) - t
	b'.addr = b.addr - (n -> t)
}


fun lookup(b : Book, n : Name) : set Addr {
	n.^(b.addr) & Addr
}


fact "no cycle" {
	all b : Book | no n : Name | n in n.^(b.addr)
}

fact "alias point to at most 1 target" {
	all b : Book | all a : Alias | lone a.(b.addr)
}


assert lookupYield {
	all b : Book, n : b.names |
		some lookup[b, n]
}
check lookupYield for 3 but 4 Book


assert delUndoesAdd {
	all b, b', b'' : Book, n : Name, t : Target |
		( no n.(b.addr)
		 and add[b, b', n, t]
		 and del[b', b'', n, t]
		 ) implies b.addr = b''.addr
}
check delUndoesAdd for 10

assert addIdempotent {
	all b, b', b'' : Book, n : Name, t : Target |
		add[b, b', n, t] and add[b', b'', n, t] implies
		b'.addr = b''.addr		
}
check addIdempotent for 10

/* should be invalid
assert addLocal {
	all b, b' : Book, disj n, n' : Name, t : Target |
		add[b, b', n, t] implies
		lookup[b, n'] = lookup[b', n']
}
check addLocal for 10
*/


pred show() {}
run show for 4
