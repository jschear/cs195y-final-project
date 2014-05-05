module final/JonathanStopAndCopy

open final/Memory
open util/ordering[Time]

sig ActiveHeap, InactiveHeap extends Addr {}
sig RootSet in Object {}
sig Time {}

one sig SC {
	mem: Memory one -> Time,
} {
	mem.Time = Memory // No extraneous memories
}

fact AtMostOneMapping {
	all m: Memory | all o: Object {
		lone a: ActiveHeap| a->o in m.data
		lone i: InactiveHeap| i->o in m.data
	}
}

// All addresses are either in the active or inactive side
fact AllAddrInHeap {
	Addr = ActiveHeap + InactiveHeap
}

abstract sig Event {
	pre, post: Time
}

sig CopyEvent extends Event {} {
	// we're only adding data mappings
	SC.mem.pre.data in SC.mem.post.data //or SC.mem.pre.data = SC.mem.post.data
	let liveObjs = SC.mem.pre.data[InactiveHeap] |
		let newObjs = liveObjs.pointers - liveObjs {
			some newObjs // we're copying something
			all o: newObjs | one i: InactiveHeap | i->o in SC.mem.post.data // all objects to copy are now mapped in the inactive side
		}
	// Frame condition: mappings for live portion of heap don't change
	ActiveHeap <: SC.mem.pre.data = ActiveHeap <: SC.mem.post.data
}

fact Traces {
	init[first]
	all e: Event | e.post = e.pre.next // no skipping times
	all t: Time - last | let t' = t.next | one e: Event | e.pre = t and e.post = t'
}

pred init[t: Time] {
	some RootSet
	all o: Object {
		one a: ActiveHeap | a->o in SC.mem.t.data
		o in RootSet => {one a: InactiveHeap | a->o in SC.mem.t.data} else {no i : InactiveHeap | i->o in SC.mem.t.data}
	}
}

run {} for 3 but 6 Addr, 3 Object

// Properties to check
// check that no live objects were removed

// check that all objects are now in the inactive side

// check that all object's addresses have changed
