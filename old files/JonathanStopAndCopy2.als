module final/JonathanStopAndCopy

open final/JonathanMemory
open util/ordering[Time]

sig ActiveHeap, InactiveHeap extends Addr {}
sig RootSet in Addr {}
sig Time {}

one sig SC {
	visited: Addr -> Time,
	mem: Memory one -> Time
} {
	mem.Time = Memory // No extraneous memories
}

// All addresses are either in the active or inactive side
fact AllAddrInHeap {
	Addr = ActiveHeap + InactiveHeap
	Addr = SC.mem.Time.data.Object // All Addrs are mapped at some point
}

abstract sig Event {
	pre, post: Time
}

sig CopyEvent extends Event {} {
	let visitedObjs = SC.mem.pre.data[SC.visited.pre] | // set of visited objects
		let pointerAddrs = SC.mem.pre.data.(visitedObjs.pointers) | // set of addrs visited objects point to
			let newAddrs = pointerAddrs - SC.visited.pre { // remove visited pointers from set
				SC.visited.post = SC.visited.pre + newAddrs
				all a: newAddrs | let o = SC.mem.pre.data[a] {
					one newAddr: InactiveHeap | (newAddr -> o) in SC.mem.post.data // all live objects are now mapped in the inactive side
 					let oldAddr = SC.mem.pre.data.o | (oldAddr -> o) not in SC.mem.post.data // remove old mappings
				}
			}
	}
}

pred init[t: Time] {
	some RootSet
	no SC.visited.t // no visited set to start
	all a: RootSet | a in ActiveHeap // all RootSet pointers are in live portion
	all a: Addr | a in SC.mem.t.data.Object => a in ActiveHeap // all current addresses are in live portion
	all o: SC.mem.t.data[Addr].^pointers | o in SC.mem.t.data[ActiveHeap] // all objects pointers are in ActiveHeap
}

fact Traces {
	init[first]
	all e: Event | e.post = e.pre.next // no skipping times
	all t: Time - last | let t' = t.next | one e: Event | e.pre = t and e.post = t'
	//one CopyEvent and post.last in CopyEvent // one CopyEvent (the last event)
}

run {} for 4

// Properties to check
// check that no live objects were removed

// check that all objects are now in the inactive side

// check that all object's addresses have changed
