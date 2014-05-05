module final/StopAndCopy

open final/Memory
open util/ordering[Time]

sig ActiveHeap, InactiveHeap extends Addr {}
sig RootSet in Object {} // RootSet of objects
sig Time {}

one sig SC {
	mem: Memory one -> Time
} {
	mem.Time = Memory // No extraneous memories
}

/** Facts **/
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

/** Events **/
abstract sig Event {
	pre, post: Time
}

//
sig CopyEvent extends Event {} {
	let liveObjs = SC.mem.pre.data[InactiveHeap] |
		let newObjs = liveObjs.pointers - liveObjs {
			some newObjs // something is being copies
			all o: newObjs | one i: InactiveHeap | i -> o in SC.mem.post.data // all objects to copy are now mapped in the inactive side
			no o: Object | (InactiveHeap -> o) in (SC.mem.post.data - SC.mem.pre.data) and (o not in newObjs) // no extraneous new mappings in the inactive side
		}
	SC.mem.pre.data in SC.mem.post.data // we're only adding data mappings
	ActiveHeap <: SC.mem.pre.data = ActiveHeap <: SC.mem.post.data // Frame condition: mappings for live portion of heap don't change
}

//
one sig FinishedEvent extends Event {} {
	SC.mem.pre.data = SC.mem.post.data
	let liveObjs = SC.mem.pre.data[InactiveHeap] | no (liveObjs.pointers - liveObjs)
}

/** Traces **/
fact Traces {
	init[first]
	all e: Event | e.post = e.pre.next // no skipping times
	all t: Time - last | let t' = t.next | one e: Event | e.pre = t and e.post = t'
	post.last in FinishedEvent 
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
assert AllLiveObjectsInNewHeap {
	let memEnd = SC.mem.last.data |
		let liveObjs = RootSet.^pointers |
			all o: liveObjs | o in memEnd[InactiveHeap]
}
check AllLiveObjectsInNewHeap for 7
check AllLiveObjectsInNewHeap for 7 but 20 Addr, 10 Object
check AllLiveObjectsInNewHeap for 5 but 14 Addr, 7 Object

// check that all objects are now in the inactive side
check {
	let memEnd = SC.mem.last.data | RootSet.^pointers = memEnd[InactiveHeap]
} for 6

// check that all object's addresses have changed
assert AllLiveObjectsHaveNewAddresses {

}

// check that the set of inactive addrs is less than or equal to the set of active addrs
assert UsingLEQAddrs {
	#(ActiveHeap <: SC.mem.first.data) >= #(InactiveHeap <: SC.mem.last.data)
}
check UsingLEQAddrs for 7
