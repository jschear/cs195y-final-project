module Final/Memory

sig Addr {}
sig Object {
	//pointers: set Addr
}

sig Primitive extends Object {} {
	no pointers
}

sig Memory {
	pointers: Object -> Addr,
	data: Addr -> lone Object
}

fact Canonicalize {
	no disj m, m': Memory | m.data = m'.data
}
