# Snowgrave

Snowgrave closes authored CLOS into ordinary functions and records. The SBCL
adapter builds portable source artifacts; Mezzano adapters provide cold typed
record materialization and admitted native access primitives. Full Mezzano
supervisor admission remains incomplete.

With this directory registered with ASDF:

```lisp
(asdf:load-system "snowgrave/sbcl")
(asdf:test-system "snowgrave")
```

The [specification](paper/README.md) is in `paper/`.

Hosted import, resource-indexing and generic-call measurements:

```sh
sbcl --script scripts/bench-configuration-imports.lisp
sbcl --script scripts/bench-native-resources.lisp
sbcl --script scripts/bench-generic-call-conventions.lisp
```
