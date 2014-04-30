module Final/Memory

sig Addr {}
sig Object {
	pointers: set Object
}

sig Primitive extends Object{}
{no pointers}

sig Memory {
	//one so that every object will have an address
	data: Addr one -> lone Object
}
// every Object is in Memory
{all o: Object| o in Addr.data}

fact Canonicalize {
	no disj m, m': Memory | m.data = m'.data
}

// Helper functions
fun addrToObject[m: Memory, a: Addr]: set Object {
	m.data[a]
}

// set: might want to ask for the set of addresses of the pointer objects
fun objectToAddr[m: Memory, o: Object]: set Addr {
	m.data.o
}

run {
// test if we can have some Addr mapping to nothing
//	some a: Addr| a not in Memory.data.Object
} for 3 but 1 Memory
