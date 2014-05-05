module final/LuqiStopAndCopyNoTime

open final/Memory

sig ActiveHeap, InactiveHeap extends Addr {}
sig RootSet in Object {} // RootSet of objects

one sig SC {
	mem: Memory,
	forward: (ActiveHeap -> InactiveHeap)
} {
	mem = Memory // No extraneous memories
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
	all a: ActiveHeap, i: InactiveHeap {
		a -> i in SC.forward iff {
			SC.mem.data[a] = SC.mem.data[i]
			some SC.mem.data[a]
		}
	}
}

fact OnlyValidPointers {
	all a: Addr, o: Object| 
		o->a in SC.mem.pointers => {
			some o': Object | a->o' in SC.mem.data
		}
}



pred init[] {
	some RootSet
	all o: Object | one a: ActiveHeap | a->o in SC.mem.data // all object have one mapping in the ActiveHeap
	all o: RootSet {
		one i: InactiveHeap {
			(i -> o) in SC.mem.data
			//(SC.mem.data.o -> i) in SC.forward
		}
	}
	all o: Object - RootSet {
		o not in SC.mem.data[InactiveHeap]
		SC.mem.data.o not in SC.forward[ActiveHeap]
	}
}
run init for 2 but 4 Addr, 2 Object
