module final/LuqiStopAndCopy

open final/Memory
open util/ordering[Time]

sig ActiveHeap, InactiveHeap extends Addr {}
sig RootSet in Object {} // RootSet of objects
sig Time {}

one sig SC {
	mem: Memory one -> Time,
	forward: (ActiveHeap -> InactiveHeap) -> Time
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

// All addresses are either in the active or inactive side
fact AllAddrInHeap {
	// in this model, the address could only be eitheer Active or Inactive
	Addr = ActiveHeap + InactiveHeap
}

fact OnlyValidForwards {
	all a: ActiveHeap, i: InactiveHeap, t: Time {
		a -> i in SC.forward.t iff {
			SC.mem.t.data[a] = SC.mem.t.data[i]
			some SC.mem.t.data[a]
		}
	}
}

fact OnlyValidPointers {
	all t: Time, a: Addr, o: Object| 
		o->a in SC.mem.t.pointers iff {
			some o': Object | a->o' in SC.mem.t.data
		}
}

/** Events **/
abstract sig Event {
	pre, post: Time
}


pred init[t: Time] {
	some RootSet
	all o: Object | one a: ActiveHeap | a->o in SC.mem.t.data // all object have one mapping in the ActiveHeap
	all o: RootSet {
		one i: InactiveHeap {
			(i -> o) in SC.mem.t.data
			//(SC.mem.t.data.o -> i) in SC.forward.t
		}
	}
	all o: Object - RootSet {
		o not in SC.mem.t.data[InactiveHeap]
		SC.mem.t.data.o not in SC.forward.t[ActiveHeap]
	}
}
run init for 3 but 4 Addr, 3 Object, 1 Time
