module Final/MarkAndSweep

open Final/Memory
open util/ordering[Time] //ordering on Time

sig Time {}
one sig MemoryState {
	mem: one Memory,
	//mem: Memory one ->one Time,
	marked: Addr -> Time, // set of marked addresses
	rootSet: set Addr // root set of live objects
}

//1. getting the event idiom working
//2. if there's a better way than MemoryState


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

// check that all objects stayed in the same place

// eventually use this for checking mark and sweep
