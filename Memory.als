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

run {
// test if we can have some Addr mapping to nothing
//	some a: Addr| a not in Memory.data.Object
} for 3 but 1 Memory
