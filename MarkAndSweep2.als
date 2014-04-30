module Final/MarkAndSweep

open Final/Memory
open util/ordering[Time] //ordering on Time

sig Time {}
one sig MS {
	//mem: Memory one -> Time, // each Time is associated with one Memory
	mem: Memory one -> Time, 
	marked: Addr -> Time, // set of marked addresses
	rootSet: set Addr // root set of live objects
} {
	mem.Time = Memory // no extraneous memories
}

// Events
abstract sig Event {
	pre, post: Time
}

sig MarkEvent extends Event { } {
	let objs = addrToObject[MS.mem.pre, MS.marked.pre] | // set of objects in addr
		let addrs = objectToAddr[MS.mem.pre, objs.pointers] { // set of pointer addresses
			some b: addrs | b not in MS.marked.pre // must be some address in pointer set that isn't in marked set
			MS.marked.post = MS.marked.pre + addrs // add object's pointers to marked set
		}
	MS.mem.post = MS.mem.pre // frame condition: memory doesn't change
}

sig SweepEvent extends Event { } {
	let notMarked = Addr - MS.marked.pre {
		some MS.mem.pre.data[notMarked] // there are some objects that need to be collected
		MS.mem.post.data = MS.mem.pre.data - (notMarked -> Object)
	}
	MS.marked.post = MS.marked.pre // frame condition: marked set doesn't change
}


// Traces
fact Traces {
	init[first]
	all t: Time - last | let t' = t.next |
		one e: Event {
			e.pre = t and e.post = t'
			MS.marked.t != MS.marked.t' => e in MarkEvent
			MS.mem.t.data != MS.mem.t'.data => e in SweepEvent
		}
	one se: SweepEvent | se.pre = last.prev and se.post = last // last event is a sweep
}

pred init[t: Time] {
	some MS.rootSet // some live objects
	MS.marked.t = MS.rootSet // marked set is initially the same as the root set
	all addr: MS.rootSet | some addrToObject[MS.mem.t, addr].pointers
}

run {} for 6 but 5 Time, 4 Event, 2 Memory
// 5 Times => 4 Events, one sweep => 2 Memory

// Properties

// check that all objects stayed in the same place

// check that the mark search is the transitive closure of the root set

// check that no live objects were removed

// check that all objects still in memory are alive


