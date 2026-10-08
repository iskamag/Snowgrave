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

The original paper snapshot remains in `paper/`.
