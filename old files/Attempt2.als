module final/JonathanMarkAndSweepAlternate
open util/ordering[Time]

sig Time {}
sig Addr {
	marked: set Time
}
sig RootSet in Addr {}

sig Object {
	pointers: set Object
}

one sig Memory {
	data: (Addr -> lone Object) -> Time // one so that every object will have an address
} {
	Object in data.Time[Addr] // all objects in memory
	Addr in data.Time.Object // all addrs in memory
}

abstract sig Event {
	pre, post: Time
}

fact Traces {
	init[first]
	all t: Time - last | let t' = t.next {
		one e: Event {
			e.pre = t and e.post = t'
			marked.t = marked.t' or e in MarkEvent
			Memory.data.t = Memory.data.t' or e in SweepEvent
		}
	}
	all e: Event | e.post = e.pre.next
	one SweepEvent
	post.last in SweepEvent
}

pred init[t: Time] {
	some RootSet
	marked.t = RootSet
}

sig MarkEvent extends Event {} {
	let objs = Memory.data.pre[(marked.pre)] | 
		let addrs = Memory.data.pre.(objs.pointers) {
			marked.post != marked.pre // marked set changes
			marked.post = marked.pre + addrs
		}
	Memory.data.pre = Memory.data.post
}

sig SweepEvent extends Event {} {
	some (Addr - marked.pre) // something is being sweeped
	Memory.data.post in Memory.data.pre
	Memory.data.post = marked.pre <: Memory.data.pre
	marked.post = marked.pre
}

run {} for 7 but 5 Time, 4 Event
