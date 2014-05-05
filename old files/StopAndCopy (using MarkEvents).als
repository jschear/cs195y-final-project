module final/JonathanStopAndCopy

open final/JonathanMemory
open util/ordering[Time]

sig ActiveHeap, InactiveHeap extends Addr {}
sig RootSet in Addr {}
sig Time {}

one sig SC {
	marked: Addr -> Time,
	mem: Memory one -> Time
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

sig MarkEvent extends Event {} {
	let objs = SC.mem.pre.data[SC.marked.pre] | 
		let addrs = SC.mem.pre.data.(objs.pointers) {
			some (addrs - SC.marked.pre) // something new is being added to the marked set
			SC.marked.post = SC.marked.pre + addrs
		}
	SC.mem.pre = SC.mem.post
}

sig CopyEvent extends Event {} {
	some (Addr - SC.marked.pre) // there are some objects to remove
	let markedObjs = SC.mem.pre.data[SC.marked.pre] {
		let nextAddrs = SC.mem.pre.data.(markedObjs.pointers) | nextAddrs in SC.marked.pre // We are finished marking
		all o: markedObjs {
			one newAddr: InactiveHeap | (newAddr -> o) in SC.mem.post.data // all live objects are now mapped in the inactive side
			let oldAddr = SC.mem.pre.data.o | (oldAddr -> o) not in SC.mem.post.data
		}
	}
	SC.marked.post = SC.marked.pre
}

pred init[t: Time] {
	some RootSet
	all a: RootSet | a in ActiveHeap 
	all a: Addr | a in SC.mem.t.data.Object => a in ActiveHeap // all current addresses are in live portion
	SC.marked.t = RootSet // initialize the set to copy to the root set
}

fact Traces {
	init[first]
	all e: Event | e.post = e.pre.next // no skipping times
	all t: Time - last | let t' = t.next |
		one e: Event {
			e.pre = t and e.post = t'
			SC.marked.t = SC.marked.t' or e in MarkEvent
			SC.mem.t = SC.mem.t' or e in CopyEvent
		}
	some MarkEvent // must mark
	one CopyEvent and post.last in CopyEvent // one CopyEvent (the last event)
}

run {} for 4

// Properties to check
// check that no live objects were removed

// check that all objects are now in the inactive side

// check that all object's addresses have changed
