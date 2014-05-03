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
	all t: Time - last | let t' = t.next {
		one e: Event {
			e.pre = t and e.post = t'
			MS.marked.t = MS.marked.t' or e in MarkEvent
			MS.mem.t = MS.mem.t' or e in SweepEvent
		}
	}
	all e: Event | e.post = e.pre.next
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
*/

// Properties to check

// check that all objects stayed in the same place

// check that the mark search is the transitive closure of the root set

// check that no live objects were removed

// check that all objects still in memory are alive
