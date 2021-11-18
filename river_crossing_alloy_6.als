module farmer

abstract sig Object {
	eats: lone Object
}

one sig Farmer, Fox, Chicken, Grain extends Object {}

fact eating {
	eats = (Fox -> Chicken) + (Chicken -> Grain)
}

var sig Crossed in Object {}

pred same_side[o1, o2: Object] {
	o1 in Crossed <=> o2 in Crossed
}

pred cross[o: Object] {
  	{
    		(o + Farmer) in Crossed
    		Crossed' = Crossed - (Farmer + o)
  	} or
  	{
    		(o + Farmer) in Object - Crossed
		Crossed' = Crossed + (Farmer + o)
  	}
}

pred safe {
	all o1: Object, o2: o1.eats |
		same_side[o1, o2] implies same_side[o1, Farmer]
}

pred Next {
	some item: Object |
		cross[item]
}

solvePuzzle: run {
 	no Crossed
	always Next
 	always safe
  	eventually Crossed = Object
}


run show {} for 5
