# Snowgrave

Snowgrave closes a finite CLOS program into ordinary Common Lisp functions
and structures. It obtains effective-method compositions through Closer MOP,
lowers classes to records, then recompiles the supplied source with closed
bindings. `bind-entry` specializes an entry for a fixed component graph.
