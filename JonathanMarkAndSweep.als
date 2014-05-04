module final/JonathanMarkAndSweep

open final/JonathanMemory
open util/ordering[Time]

sig Time {}
one sig MS {
	rootSet: set Addr,
	marked: Addr -> Time,
	mem: Memory one -> Time
} {
	mem.Time = Memory // No extraneous memories
}

abstract sig Event {
	pre, post: Time
}

fact Traces {
	init[first]
	all e: Event | e.post = e.pre.next // no skipping times
	all t: Time - last | let t' = t.next {
		one e: Event {
			e.pre = t and e.post = t'
			MS.marked.t = MS.marked.t' or e in MarkEvent
			MS.mem.t = MS.mem.t' or e in SweepEvent
		}
	}
	some MarkEvent // must mark
	one SweepEvent and post.last in SweepEvent // one SeepEvent (the last event)
}

pred init[t: Time] {
	some MS.rootSet
	MS.marked.t = MS.rootSet
}

sig MarkEvent extends Event {} {
	let objs = MS.mem.pre.data[(MS.marked.pre)] | 
		let addrs = MS.mem.pre.data.(objs.pointers) {
			some (addrs - MS.marked.pre) // something new is being added to the marked set
			MS.marked.post = MS.marked.pre + addrs
		}
	MS.mem.pre = MS.mem.post
}

sig SweepEvent extends Event {} {
	some (Addr - MS.marked.pre) // something is being sweeped
	MS.mem.post.data != MS.mem.pre.data
	MS.mem.post.data = MS.marked.pre <: MS.mem.pre.data
	MS.marked.post = MS.marked.pre
}

run {} for 6 but exactly 2 Memory
/* For best visualizations:
1. Magic Layout
2. Project over MS, Memory and Time
Now, cycle through times. You can tell what events you are between by the 'pre' and 'post' labels on events.
*/

// Properties
// check that the mark search is the transitive closure of the root set
assert MarkTraversalTransitiveClosure {
	let memStart = MS.mem.first.data | MS.marked.last = memStart.(MS.rootSet.(memStart.^pointers))
}
check MarkTraversalTransitiveClosure for 10 but 11 Time

// check that no live objects were removed
assert NoLiveObjectsCollected {
	let memStart = MS.mem.first.data | 
		let memEnd = MS.mem.last.data |
			let liveObjs = MS.rootSet.(memStart.^pointers) |
				all o: liveObjs | o in memEnd[Addr]
}
check NoLiveObjectsCollected for 10 but 11 Time

// check that all objects stayed in the same place
assert NoMovingObjects {
	let memStart = MS.mem.first.data |
		let memEnd = MS.mem.last.data |
			all o: memStart[Addr] {
				o in memEnd[Addr] => memEnd.o = memStart.o
			}
}
check NoMovingObjects for 10
