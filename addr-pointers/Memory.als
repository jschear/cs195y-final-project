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
	pointers: Object->Addr
}

fact Canonicalize {
	no disj m, m': Memory | m.data = m'.data
}
