sig Bicycle {
	front : Wheel,
	rear : Wheel
} { rear != front }

sig Wheel {}


fun wheels(b : Bicycle) : set Wheel {
	b.rear + b.front
}


fact "no orphan wheel" {
	all w : Wheel | some b : Bicycle |
		w in wheels[b]
}

fact "no shared wheel" {
	all w : Wheel | all disj b1, b2 : Bicycle |
		w in wheels[b1] implies w not in wheels[b2]
}


assert twoWheels {
	all b : Bicycle | #wheels[b] = 2
}
check twoWheels for 5

assert frontOrRearWheel {
	all w : Wheel | one b : Bicycle | w in b.rear or w in b.front
}
check frontOrRearWheel


pred show() {}
run show for 6 but exactly 3 Bicycle
