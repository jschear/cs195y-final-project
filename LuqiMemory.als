module final/LuqiMemory

sig Addr {}
sig Object {
	pointers: set Object
}

sig Memory {
	data: Addr -> lone Object //THE BUG! not one, but lone, because we need to have multiple memories
}

fact Canonicalize {
	no disj m, m': Memory | m.data = m'.data
}


