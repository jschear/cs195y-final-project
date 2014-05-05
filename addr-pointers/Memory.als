module Final/Memory

sig Addr {}
sig Object {
	//pointers: set Addr
}

sig Primitive extends Object {}

sig Memory {
	pointers: (Object - Primitive) -> Addr,
	data: Addr -> lone Object
}

fact Canonicalize {
	no disj m, m': Memory | m.data = m'.data
}
