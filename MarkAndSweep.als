module final/MarkAndSweep

open final/Memory
open util/ordering[Time]

sig Time {}
one sig RootSet in Addr {} // RootSet, initial set of live addresses

// Encapsulates the marked set, and the Memory mappings for each Time atom
one sig MS { 
	marked: Addr -> Time,
	mem: Memory one -> Time
} {
	mem.Time = Memory // No extraneous memories
}

/** Facts **/
// Every object is mapped to by some address in some memory
fact NoDanglingObjects {
	Object = Memory.data[Addr]
}

// All objects are mapped to by at most one address
fact InjectiveAddrs {
	all o: Object | lone Memory.data.o
}

/** Events **/
abstract sig Event {
	pre, post: Time
}

// MarkEvent: One step in the Mark phase
sig MarkEvent extends Event {} {
	let markedObjs = MS.mem.pre.data[MS.marked.pre] | // set of marked objects
		let nextAddrs = MS.mem.pre.data.(markedObjs.pointers) { // the addresses of the objects they point to
			some (nextAddrs - MS.marked.pre) // some new addresses were reached
			MS.marked.post = MS.marked.pre + nextAddrs // add to new marked set
		}
	MS.mem.pre = MS.mem.post // frame condition: memory mappings don't change
}

// SweepEvent: The Sweep phase
one sig SweepEvent extends Event {} {
	let markedObjs = MS.mem.pre.data[MS.marked.pre] | 
		let nextAddrs = MS.mem.pre.data.(markedObjs.pointers) |
			nextAddrs in MS.marked.pre // finished marking

	some (Addr - MS.marked.pre) // something is being sweeped
	MS.mem.post.data = MS.marked.pre <: MS.mem.pre.data // remove unmarked addrs from memory
	MS.marked.post = MS.marked.pre // frame condition: marked set doesn't change
}

/** Traces **/
fact Traces {
	init[first]
	all e: Event | e.post = e.pre.next // no skipping times
	all t: Time - last | let t' = t.next {
		one e: Event {
			e.pre = t and e.post = t'
			MS.marked.t = MS.marked.t' or e in MarkEvent // a change in the marked set implies a MarkEvent
			MS.mem.t = MS.mem.t' or e in SweepEvent  // a change in the memory mappings implies a SweepEvent
		}
	}
	some MarkEvent // we must mark before sweeping
	post.last in SweepEvent // last event is a SweepEvent (the last event)
}

pred init[t: Time] {
	some RootSet
	MS.marked.t = RootSet // initialize marked set to root set
}

run {} for 6 but exactly 2 Memory
/* For best visualizations:
1. Magic Layout
2. Project over MS, Memory and Time
Now, cycle through times. You can tell what events you are between by the 'pre' and 'post' labels on events.
*/


/** Properties **/
// Check that the mark search is the transitive closure of the root set
assert MarkTraversalTransitiveClosure {
	let memStart = MS.mem.first.data | MS.marked.last = memStart.(RootSet.(memStart.*pointers))
}
check MarkTraversalTransitiveClosure for 8
check MarkTraversalTransitiveClosure for 8 but 5 Time

// Check that no live objects were removed
assert NoLiveObjectsCollected {
	let memStart = MS.mem.first.data | 
		let memEnd = MS.mem.last.data |
			let liveObjs = RootSet.(memStart.*pointers) |
				all o: liveObjs | o in memEnd[Addr]
}
check NoLiveObjectsCollected for 9 // Exactly 9 Time, so 8 Event (worst case: Objects are a linked list)
check NoLiveObjectsCollected for 5 but 10 Object, 10 Addr // More reasonable case, it takes fewer marks to cover everything
check NoLiveObjectsCollected for 5 but 13 Object, 13 Addr

// Check that all objects not reachable from root set are removed from memory
assert AllDeadObjectsCollected {
	let memStart = MS.mem.first.data | 
		let memEnd = MS.mem.last.data |
			let liveObjs = RootSet.(memStart.*pointers) |
				let deadObjs = Object - liveObjs |
					all o: deadObjs | o not in memEnd[Addr]
}
check AllDeadObjectsCollected for 8 
check AllDeadObjectsCollected for 5 but 10 Object, 10 Addr
check AllDeadObjectsCollected for 5 but 13 Object, 13 Addr

// Check that all objects stayed in the same place
assert NoMovingObjects {
	let memStart = MS.mem.first.data |
		let memEnd = MS.mem.last.data |
			all o: memStart[Addr] | o in memEnd[Addr] => memEnd.o = memStart.o
}
check NoMovingObjects for 10
check NoMovingObjects for 10 but 15 Object, 15 Addr

// Between any two times, the address of an object doesn't change (if it is still mapped)
assert NoMovingObjectsEver {
	all disj t1, t2: Time {
		let mem1 = MS.mem.t1.data | let mem2 = MS.mem.t2.data |
			all o: mem1[Addr] | o in mem2[Addr] => mem1.o = mem2.o
	}
}
check NoMovingObjectsEver for 10
