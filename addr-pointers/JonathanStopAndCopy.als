module final/StopAndCopy

open final/Memory
open util/ordering[Time]

sig ActiveHeap, InactiveHeap extends Addr {}
sig RootSet in Object {} // RootSet of objects
sig Time {}

one sig SC {
	mem: Memory one -> Time,
	forward: (ActiveHeap lone -> InactiveHeap) -> Time
} {
	mem.Time = Memory // No extraneous memories
}

// The forwarding pointers only include 
fact OnlyValidForwards {
	all a: ActiveHeap, i: InactiveHeap, t: Time {
		a -> i in SC.forward.t iff {
			SC.mem.t.data[a] = SC.mem.t.data[i]
			some SC.mem.t.data[a]
		}
	}
}

fact OnlyValidPointers {
	all t: Time, a: Addr, o: Object {
		o -> a in SC.mem.t.pointers => some o': Object | a-> o' in SC.mem.t.data
	}
}

/** Facts **/
fact AtMostOneMapping {
	// in our Memory model, we don't have any constraint on the multiplicity of Addr,
	// this fact is to enforce this
	all m: Memory | all o: Object {
		lone a: ActiveHeap | a -> o in m.data
		lone i: InactiveHeap | i -> o in m.data
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

// Copy all objects that are neighborhoods of current live objects
sig CopyEvent extends Event {} {
	SC.mem.pre.data in SC.mem.post.data // we're only adding data mappings
	ActiveHeap <: SC.mem.pre.data = ActiveHeap <: SC.mem.post.data // Frame condition: mappings for live portion of heap don't change
	SC.mem.pre.pointers = SC.mem.post.pointers

	let liveObjs = SC.mem.pre.data[InactiveHeap] | // objects in inactive side
	let pointerAddrs = SC.mem.pre.pointers[liveObjs] | // addrs of the live objs's pointers
	let pointerObjs = SC.mem.pre.data[pointerAddrs] |
	let newObjs = pointerObjs - liveObjs {
		some newObjs // something is being copied
		all o: newObjs | one i: InactiveHeap {
			(i -> o) in SC.mem.post.data // all objects to copy are now mapped in the inactive side
			(SC.mem.pre.data.o -> i) in SC.forward.post // add forwarding mapping
		}
		all o: Object - newObjs | no i: InactiveHeap {
		 	(i -> o) in (SC.mem.post.data - SC.mem.pre.data) // no extraneous new mappings in the inactive side
			(SC.mem.pre.data.o -> i) in (SC.forward.post - SC.forward.pre)
		}
	}
}

sig UpdatePointersEvent extends Event {} {
	SC.mem.pre.data = SC.mem.post.data // frame condition: memory mappings don't change
	SC.forward.pre = SC.forward.post // frame condition: forwarding pointers don't change

	let liveObjs = SC.mem.pre.data[InactiveHeap] | // objects in inactive side
		all o: liveObjs | let pointerAddrs = SC.mem.pre.pointers[o] {
			some pointerAddrs
			all a: pointerAddrs | let forwardAddr = SC.forward.pre[a] {
				some forwardAddr
				a in ActiveHeap and some forwardAddr => forwardAddr in SC.mem.post.pointers[o] and a not in SC.mem.post.pointers[o]
			}
		}
}

// Signaling that we've copied all live objects
/*
one sig FinishedEvent extends Event {} {
	SC.mem.pre.data = SC.mem.post.data
	let liveObjs = SC.mem.pre.data[InactiveHeap] | no (liveObjs.pointers - liveObjs)
}*/

/** Traces **/
fact Traces {
	init[first]
	pre.first in UpdatePointersEvent // first event must be updating pointers
	all e: Event | e.post = e.pre.next // no skipping times
	all t: Time - last | let t' = t.next | one e: Event | e.pre = t and e.post = t'
	//post.last in FinishedEvent 
}

pred init[t: Time] {
	some RootSet
	all o: RootSet | one a: ActiveHeap, i: InactiveHeap {
		(a -> o) in SC.mem.t.data
		(i -> o) in SC.mem.t.data
		(a -> i) in SC.forward.t
	}
	all o: Object - RootSet {
		one a: ActiveHeap | a->o in SC.mem.t.data
		o not in SC.mem.t.data[InactiveHeap]
		SC.mem.t.data.o not in SC.forward.t.InactiveHeap
	}
}

run init for 3 but 0 Event, 1 Memory, 1 Time

run {} for 6 but 3 Time, 2 Event

/*
// Properties to check
// check that all objects are now in the inactive side
assert SoundAndComplete {
	let memEnd = SC.mem.last.data | RootSet.*pointers = memEnd[InactiveHeap]
	// equal sign here makes sure that we're not collecting more nor less
} 
check SoundAndComplete for 6 but 20 Addr, 10 Object

// check that no live objects were removed
assert AllLiveObjectsInNewHeap {
	let memEnd = SC.mem.last.data | // memory at the end
		let liveObjs = RootSet.^pointers | // all live objects using TC
			all o: liveObjs | o in memEnd[InactiveHeap]
}
check AllLiveObjectsInNewHeap for 7
check AllLiveObjectsInNewHeap for 7 but 20 Addr, 10 Object
check AllLiveObjectsInNewHeap for 5 but 14 Addr, 7 Object



// check that all live objects have addresses in InactiveHeap
assert AllLiveObjectsHaveNewAddresses {
	all o: RootSet.*pointers | one i: InactiveHeap | i->o in SC.mem.last.data
}
check AllLiveObjectsHaveNewAddresses for 5 but 14 Addr, 7 Object

// check that the set of inactive addrs is less than or equal to the set of active addrs
assert UsingLEQAddrs {
	#(ActiveHeap <: SC.mem.first.data) >= #(InactiveHeap <: SC.mem.last.data)
}
check UsingLEQAddrs for 7
*/



// at any time, every object's set of pointers is either in the active side or inactive side
/*
fact AllPointersInOneSide {
	all o: Object, t: Time |
		let pointerAddrs = SC.mem.t.pointers[Object] |
			(pointerAddrs in InactiveHeap) or (pointerAddrs in ActiveHeap)
}
*/
