module final/LuqiStopAndCopy

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

/** Facts **/
fact AtMostOneMapping {
	// in our Memory model, we don't have any constraint on the 
	// multiplicity of Addr, this fact is to enforce this
	all m: Memory | all o: Object {
		lone a: ActiveHeap| a->o in m.data
		lone i: InactiveHeap| i->o in m.data
	}
}

// at any time, every object's set of pointers is either in the active side or inactive side
/*
fact AllPointersInOneSide {
	all o: Object, t: Time |
		let pointerAddrs = SC.mem.t.pointers[Object] |
			(pointerAddrs in InactiveHeap) or (pointerAddrs in ActiveHeap)
}
*/

// All addresses are either in the active or inactive side
fact AllAddrInHeap {
	// in this model, the address could only be eitheer Active or Inactive
	Addr = ActiveHeap + InactiveHeap
}

fact validPointersMapping {
	all t: Time | SC.mem.t.pointers
}

/** Events **/
abstract sig Event {
	pre, post: Time
}


pred init[t: Time] {
//	some RootSet
	all o: Object {
		one a: ActiveHeap | a->o in SC.mem.t.data
		o in RootSet => {
			one i: InactiveHeap {
				i->o in SC.mem.t.data
				//(SC.mem.t.data.o -> i) in SC.forward.t
			}
		} else {
			no i: InactiveHeap {
				i->o in SC.mem.t.data
				//(SC.mem.t.data.o -> i) in SC.forward.t
			}
		}
	}
	no SC.forward.t
}
run init for 1 but 6 Addr, 3 Object
