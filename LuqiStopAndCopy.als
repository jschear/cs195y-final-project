module final/LuqiStopAndCopy

open final/LuqiMemory
open util/ordering[Time]

sig ActiveHeap, InactiveHeap extends Addr {}
sig RootSet in Object {}
sig Time {}

one sig SC {
	mem: Memory one -> Time,
} {
	mem.Time = Memory // No extraneous memories
}

fact AtMostOneMapping{
	all m: Memory | all o: Object {
		lone a: ActiveHeap| a->o in m.data
		lone i: InactiveHeap| i->o in m.data
	}
}

// All addresses are either in the active or inactive side
fact AllAddrInHeap {
	Addr = ActiveHeap + InactiveHeap
}

/*fact NoDanglingObject {
	all t: Time| Object in SC.mem.t.data[Addr]
}*/

abstract sig Event {
	pre, post: Time
}

sig CopyEvent extends Event{} {
	// we're only adding data mappings
	SC.mem.pre.data in SC.mem.post.data or SC.mem.pre.data = SC.mem.post.data
	/*let liveObjs = SC.mem.pre.data[InactiveHeap] |
	let newObjs = liveObjs.pointers - liveObjs |
		all o: newObjs | one i: InactiveHeap |
		SC.mem.post.data = i->o + SC.mem.pre.data*/
	/*one obj: SC.mem.pre.data[InactiveHeap] |
		all o: obj.pointers - obj| one i: InactiveHeap |
		i->o in SC.mem.post.data*/
}

pred init[t: Time] {
	some RootSet
	//all a: RootSet | a in ActiveHeap 
	//all a: Addr | a in SC.mem.t.data.Object => a in ActiveHeap // all current addresses are in live portion
//	SC.toCopy.t = RootSet // initialize the set to copy to the root set
	all o: RootSet| one a: ActiveHeap| a->o in SC.mem.t.data
	all o: RootSet| one a: InactiveHeap| a->o in SC.mem.t.data
	all o: Object| o not in RootSet => {
		one a: ActiveHeap | a->o in SC.mem.t.data and
		no i : InactiveHeap | i->o in SC.mem.t.data
	}
}

run init for 1 but 6 Addr, 3 Object

fact Traces {
	init[first]
	all e: Event | e.post = e.pre.next // no skipping times
	all t: Time - last | let t' = t.next | one e: Event | e.pre = t and e.post = t'
}

run {} for 3 but 6 Addr, 3 Object

// Properties to check
// check that no live objects were removed

// check that all objects are now in the inactive side
