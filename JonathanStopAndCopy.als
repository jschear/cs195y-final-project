module final/JonathanStopAndCopy

open final/JonathanMemory
open util/ordering[Time]

sig ActiveHeap, InactiveHeap extends Addr {}
sig RootSet in Addr {}
sig Time {}

one sig SC {
	mem: Memory one -> Time,
	toCopy: Addr -> Time // set of addresses that have been copied?
} {
	mem.Time = Memory // No extraneous memories
}

// All addresses are either in the active or inactive side
fact AllAddrInHeap {
	Addr = ActiveHeap + InactiveHeap
}

abstract sig Event {
	pre, post: Time
}

sig CopyEvent extends Event {} {
	let objsToCopy = SC.mem.pre.data[(SC.toCopy.pre)] {
		SC.toCopy.post = SC.mem.pre.data.objsToCopy
		all o: objsToCopy | one a: InactiveHeap {
			SC.mem.post.data = SC.mem.pre.data + (a -> o) - (ActiveHeap -> o)
		}
	}
}

pred init[t: Time] {
	some RootSet
	//all a: RootSet | a in ActiveHeap 
	all a: Addr | a in SC.mem.t.data.Object => a in ActiveHeap // all current addresses are in live portion
	SC.toCopy.t = RootSet // initialize the set to copy to the root set
}

fact Traces {
	init[first]
	all e: Event | e.post = e.pre.next // no skipping times
	all t: Time - last | let t' = t.next | one e: Event | e.pre = t and e.post = t'
}

run {} for 6 but 5 Time

// Properties to check
// check that no live objects were removed

// check that all objects are now in the inactive side
