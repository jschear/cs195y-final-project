
sig Addr {}
sig Object {
	pointers: set Object
}
//sig Integer, Double in Object
//TODO: Model primitive objects w/ no pointers

sig Memory {
	data: Addr -> lone Object,
	marked: set Addr
}

pred mark[m, m': Memory, rs: set Object] {
	
}

// pred for mark and sweep garbage collection
// takes in memory before, after, root set
pred markAndSweep[m, m': Memory, rs: set Object] {

}



// check that all objects stayed in the same place

// 





// eventually use this for checking mark and sweep
pred markAndSweep[m, m': Memory, rs: set Object] {
	let reachable = rs.^pointers {
		m.marked = reachable
	}
	m'.data[Addr] = m.marked
}


/*
pred init [m: Memory] {
	no m.data
}

pred write [m, m': Memory, a: Addr, o: Object] {
	m'.data = m.data ++ a -> d
}

pred read [m: Memory, a: Addr, d: Data] {
	let d' = m.data [a] | some d' implies d = d'
}

fact Canonicalize {
	no disj m, m': Memory | m.data = m'.data
}

// This command should not find any counterexample
WriteRead: check {
	all m, m': Memory, a: Addr, d1, d2: Data |
		write [m, m', a, d1] and read [m', a, d2] => d1 = d2
	}

// This command should not find any counterexample
WriteIdempotent: check {
	all m, m', m": Memory, a: Addr, d: Data |
		write [m, m', a, d] and write [m', m", a, d] => m' = m"
	}
*/
