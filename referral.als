sig User { invite : lone Invite }
sig Invite { invited : set User }

// all invites has a owner
fact { all i : Invite | one u : User | i in u.invite }

// acyclic
fact { no u : User | u in u.^(invite.invited) }

// at most one invite per user
fact {all u : User | lone i : Invite | u in i.invited}


pred show() {}
run show for exactly 4 User, exactly 2 Invite
