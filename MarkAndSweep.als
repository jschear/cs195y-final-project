module Final/MarkAndSweep

open Final/Memory
open util/ordering[Time] //ordering on Time

sig Time {}
one sig MemoryState {
	mem: one Memory,
	//mem: Memory one -> Time,
	marked: Addr -> Time, // set of marked addresses
	rootSet: set Addr // root set of live objects
}

fact {
	one Memory
}

// Events
abstract sig Event {
	pre, post: Time
}

sig MarkEvent extends Event {
	toMark: one Addr
} {
	// one address in the marked set
  /* one addr: MemoryState.marked.pre {
		let obj = addrToObject[MemoryState.mem.pre, addr] { // current object
			// there must be some progress
			some a: objectToAddr[MemoryState.mem.pre, obj.pointers] | a not in MemoryState.marked.pre
			// add object's pointers to marked set
			MemoryState.marked.post = MemoryState.marked.pre + objectToAddr[MemoryState.mem.pre, obj.pointers]
		}
	}
	MemoryState.mem.post = MemoryState.mem.pre // memory doesn't change*/

	toMark in MemoryState.marked.pre
	let obj = addrToObject[MemoryState.mem, toMark] { // current object
		// there must be some progress
		some a: objectToAddr[MemoryState.mem, obj.pointers] | a not in MemoryState.marked.pre
		// add object's pointers to marked set
		MemoryState.marked.post = MemoryState.marked.pre + objectToAddr[MemoryState.mem, obj.pointers]
	}
}

sig SweepEvent extends Event {} {
	//MemoryState.mem.post = MemoryState.mem.pre // memory doesn't change
}

// Helper functions
fun addrToObject[m: Memory, a: Addr]: one Object {
	m.data[a]
}

fun objectToAddr[m: Memory, o: Object]: set Addr {
	m.data.o
}


// Traces
fact Traces {
	init[first]
	all t: Time - last |
		let t' = t.next |
			//one e: MarkEvent | e.pre = t and e.post = t'
			one e: Event {
				e.pre = t and e.post = t'
				MemoryState.marked.t != MemoryState.marked.t' => e in MarkEvent
			}
}

pred init[t: Time] {
	some rootSet // some live objects
	marked.t = rootSet // marked set is initially the same as the root set
	//all addr: MemoryState.rootSet | some addrToObject[MemoryState.mem.t, addr].pointers
	all addr: MemoryState.rootSet | some addrToObject[MemoryState.mem, addr].pointers
}

run {} for 3 but 3 Object, 3 Addr

// pred for mark and sweep garbage collection
// takes in memory before, after, root set
/* pred markAndSweep[m, m': Memory, rootSet: set Addr] {
	
}

pred mark[m, m': Memory, rootSet: set Addr] {
	one addr: rootSet {
		m'.marked = m.marked + addr
	}
}*/

// check that all objects stayed in the same place


// eventually use this for checking mark and sweep
/*
pred markAndSweep[m, m': Memory, rs: set Object] {
	let reachable = rs.^pointers {
		m.marked = reachable
	}
	m'.data[Addr] = m.marked
}
*/


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
