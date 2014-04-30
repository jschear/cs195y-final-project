module Final/MarkAndSweep

open Final/Memory
open util/ordering[Time] //ordering on Time

//1. getting the event idiom working
//2. if there's a better way than MemoryState

sig Time {}
one sig MemoryState {
	mem: Memory one -> Time,
	marked: Addr -> Time, // set of marked addresses
	rootSet: set Addr // root set of live objects
} {
	mem.Time = Memory // no extraneous memories
}

// Events
abstract sig Event {
	pre, post: Time
}

sig MarkEvent extends Event {
	a: set Addr // the current marked set
} {
	a = MemoryState.marked.pre
	let objs = addrToObject[MemoryState.mem.pre, a] | // set of objects in addr
		let addrs = objectToAddr[MemoryState.mem.pre, objs.pointers] { // set of pointer addresses
			some b: addrs | b not in MemoryState.marked.pre // must be some address in pointer set that isn't in marked set
			MemoryState.marked.post = MemoryState.marked.pre + addrs // add object's pointers to marked set
		}
	MemoryState.mem.post = MemoryState.mem.pre // memory doesn't change
}


sig SweepEvent extends Event {
	
} {
	MemoryState.mem.post = MemoryState.mem.pre // memory doesn't change
}


// Traces
fact Traces {
	init[first]
	all t: Time - last | let t' = t.next |
		one e: Event {
			e.pre = t and e.post = t'
			MemoryState.marked.t != MemoryState.marked.t' => e in MarkEvent
			//MemoryState.mem.t != MemoryState.mem.t' => e in SweepEvent
		}
}

pred init[t: Time] {
	some rootSet // some live objects
	marked.t = rootSet // marked set is initially the same as the root set
	all addr: MemoryState.rootSet | some addrToObject[MemoryState.mem.t, addr].pointers
}

run {} for 4 //but 3 Object, 3 Addr

// Properties

// check that all objects stayed in the same place

// check that transitive closure
