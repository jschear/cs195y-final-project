module Final/MarkAndSweep2

open Final/Memory
open util/ordering[Time] //ordering on Time

sig Time {}
one sig MS {
	mem: Memory one -> Time,  // each Time is associated with one Memory, but a Memory can be the same for multiple times
	marked: Addr -> Time, // set of marked addresses, changes over time
	rootSet: set Addr // root set of live objects, doesn't change
} {
	mem.Time = Memory // no extraneous Memory atoms
}

// Events
abstract sig Event {
	pre, post: Time
}

/* One step in the mark phase. */
sig MarkEvent extends Event { } {
	let objs = addrToObject[MS.mem.pre, MS.marked.pre] | // set of objects in addr
		let addrs = objectToAddr[MS.mem.pre, objs.pointers] { // set of pointer addresses
			some b: addrs | b not in MS.marked.pre // must be some address in pointer set that isn't in marked set
			MS.marked.post = MS.marked.pre + addrs // add object's pointers to marked set
		}
	MS.mem.post = MS.mem.pre // frame condition: memory doesn't change
}

/* The sweep phase. 
* Removes all non-marked address mappings from the memory.
*/
sig SweepEvent extends Event { } {
	/*
	let notMarked = Addr - MS.marked.pre {
		some notMarked
	//	some MS.mem.pre.data[notMarked] // there are some objects that need to be collected
		MS.mem.post.data = MS.mem.pre.data - (notMarked <: MS.mem.pre.data) // removes mappings in memory of all dead objects
	}
	*/
	//MS.mem.post.data !=  MS.mem.pre.data
	//MS.mem.post != MS.mem.pre // Memory changes
	MS.mem.post.data = MS.marked.pre <: MS.mem.pre.data // Memory data mappings are pre domain restricted to the marked addresses
	MS.marked.post = MS.marked.pre // frame condition: marked set doesn't change
}


// Trace
fact Traces {
	init[first]
	one me: MarkEvent {
		me.pre = first
		me.post = first.next
	}
	one se: SweepEvent {
		se.pre = first.next
		se.post = last
	}
	/*all t: Time - last | let t' = t.next |
		one e: Event {
			e.pre = t
			e.post = t'
			MS.marked.t != MS.marked.t' => e in MarkEvent
			MS.mem.t != MS.mem.t' => e in SweepEvent //or MS.mem.t.data != MS.mem.t'.data => e in SweepEvent
		}
	post.last in SweepEvent */
	/*
	all t: Time - (last + last.prev) | let t' = t.next |
		one e: MarkEvent {
			e.pre = t
			e.post = t'
		}
	//post.last in SweepEvent
	one se: SweepEvent | se.pre = last.prev and se.post = last // last event is a sweep
*/
}

// Initial state
pred init[t: Time] {
	some MS.rootSet // some live objects
	MS.marked.t = MS.rootSet // marked set is the same as the root set
	all addr: MS.rootSet | some addrToObject[MS.mem.t, addr].pointers // each object in the root set has some pointers
}

run {} for 6 but exactly 3 Time, exactly 2 Event, exactly 2 Memory
// n Times => n - 1 Events, one sweep => 2 Memory




