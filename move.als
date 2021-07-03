abstract sig FSObject {}

sig File, Dir extends FSObject {}

sig FileSystem {
	live : set FSObject,
	root : Dir & live,
	parent : (live - root) ->one (Dir & live),
	contents : Dir -> FSObject
} {
	live in root.*contents
	parent = ~contents
}

fact { all o : FSObject | one fs : FileSystem | o in fs.live }


pred move [fs, fs' : FileSystem, x : FSObject, d : Dir] {
	(x + d) in fs.live
	fs'.parent = fs.parent - x->(x.(fs.parent)) + x->d
}

run move for exactly 2 FileSystem, 4 FSObject

pred show() {}

run show for exactly 1 FileSystem, 15 FSObject
