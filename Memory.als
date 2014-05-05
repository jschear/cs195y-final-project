module Final/Memory

sig Addr {}
sig Object {
	pointers: set Object
}

sig Primitive extends Object {} {
	no pointers
}

sig Memory {
	data: Addr -> lone Object
}

// No two Memory atoms have the same data mappings
fact Canonicalize {
	no disj m, m': Memory | m.data = m'.data
}
