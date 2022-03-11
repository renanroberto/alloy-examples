sig Event {}

sig Person {
	events : set Event,
	likes : set Event,
	hates : set Event
}


sig NewPerson {
	person : Person
}

sig Attendance {
	event : Event,
	attendee : NewPerson
}

abstract sig Review {
	event : Event,
	reviewer : NewPerson
}

sig Likes, Hates extends Review {}


pred valid[p : Person] {
	no p.likes & p.hates
}

pred valid[p : NewPerson] {
	all r1, r2 : p.~reviewer |
		r1 in Likes and r2 in Hates
			implies r1.event != r2.event
}

pred same_events[p : Person, np : NewPerson] {
	p.events = np.~attendee.event
}

pred same_reviews[p : Person, np : NewPerson] {
	p.likes = (np.~reviewer & Likes).event
	p.hates = (np.~reviewer & Hates).event
}

pred equivalent[p : Person, np : NewPerson] {
	p = np.person
	same_events[p, np]
	same_reviews[p, np]
}


pred migration[p : Person, np : NewPerson] {
	p = np.person
	
	-- migrate events
	all e : p.events | one a : Attendance {
		a.event = e
		a.attendee = np
	}

	-- migrate likes
	all l : p.likes | one r : Likes {
		r.event = l
		r.reviewer = np
	}

	-- migrate hates
	all h : p.hates | one r : Hates {
		r.event = h
		r.reviewer = np
	}

	-- only generate what is needed
	#p.events = #np.~attendee
	#p.likes = #np.~reviewer & Likes
	#p.hates = #np.~reviewer & Hates
}


check equivalence_preserves_validity {
	all p : Person, np : NewPerson |
		equivalent[p, np] implies (valid[p] iff valid[np])
} for 5

check migration_perserves_equivalence {
	all p : Person, np : NewPerson |
		migration[p, np] implies equivalent[p, np]
} for 5


example : run {
	one Person
	one NewPerson
	equivalent[Person, NewPerson]
}
