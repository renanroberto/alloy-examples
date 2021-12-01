sig Node {
	edges : set Node
}

sig Ball {
	var loc : Node
}

one sig Final in Node {}


fact "Connected graph" {
	some n : Node | n.*edges = Node
}

fact "No self edges" {
	no n : Node | n in n.edges
}


pred move[b : Ball, n : Node] {
	n in b.loc.edges
	no b2 : Ball | b2.loc = n
	b.loc' = n
}

pred moved[b : Ball] {
	some n : Node | move[b, n]
}

pred unchanged[b : Ball] {
	b.loc' = b.loc
}

pred reached[b : Ball, n : Node] {
	once b.loc = n
}


pred init {
	all disj b1, b2 : Ball |
		b1.loc != b2.loc
}

pred step {
	all b : Ball | moved[b] or unchanged[b]
}

pred rule {
	all b : Ball |
		b.loc != Final until (all n : Node | once b.loc = n) 
}

pred final {
	all b : Ball | b.loc = Final
}

pred spec {
	init
	always step
	rule
	eventually final
}


check no_overlap {
	spec => always {
		no disj b1, b2 : Ball | b1.loc = b2.loc
	}
} for 5 but exactly 2 Ball


example1 : run {
	some b : Ball | always moved[b]
}

example2 : run {
	some b : Ball {
		always moved[b]
		all n : Node | eventually b.loc = n
	}
}

example3 : run {
	some b : Ball {
		always moved[b]
		eventually some n : Node {
			b.loc = n ; b.loc != n ; b.loc = n
		}
	}
}

example4 : run {
	some b : Ball {
		always moved[b]
		b.loc != Final until (all n : Node | reached[b, n])
	}
} for 3 but exactly 5 Node, 2 Ball

example5 : run {
	spec
} for exactly 5 Node, exactly 2 Ball



















