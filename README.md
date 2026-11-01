# Snowgrave

Snowgrave closes a finite CLOS program into functions and structs.
It obtains effective-method compositions through MOP,
lowers classes to records, then recompiles the supplied source with closed
bindings. `bind-entry` specializes an entry for a fixed component graph.

