open util/ordering[Member]

sig Member {
	refer : set User
}

sig User {}


pred init(m : Member) {
	no m.refer
}


pred add(m, m' : Member, u : User) {
	u not in m.refer
	m'.refer = m.refer + u
}

pred del(m, m' : Member, u : User) {
	u in m.refer
	m'.refer = m.refer - u
}


fact traces {
	init[first]

	all m : (Member - last) | let m' = next[m] | some u : User |
		add[m, m', u] or del[m, m', u]
}

// fix
check one_add_or_del_at_time {
	all m : (Member - last) | let m' = next[m] {
		(#m.refer = #m'.refer + 1) or (#m.refer = #m'.refer - 1)
	}
} for 5


pred show() {}
run show for 10 but exactly 5 Member
