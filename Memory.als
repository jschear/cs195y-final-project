module Final/Memory

sig Addr {}
sig Object {
	pointers: set Object
}

sig Primitive extends Object{}
{no pointers}

sig Memory {
	data: Addr one-> lone Object
}

run {} for 3 but 1 Memory
