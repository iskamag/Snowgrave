This adapter lowers caller-admitted operations through Mezzano's actual finalized
record and array layouts. It supports sealed scalar T/FIXNUM/finite keyword
fields, BIT fields, and explicit signed or unsigned field widths from 1 through
32. Native integer fields use their upgraded 8/16/32-bit storage and natural
alignment. A record BIT field occupies a byte; BIT arrays are packed.

Scoped AREF read/write and numeric CAS support T and signed/unsigned 8/16/32-bit
vectors, including nondisplaced rank-one complex vectors. Packed BIT read/write
requires exclusive mutation; BIT CAS and 64-bit integer access are rejected.
Full-width 64-bit results can require allocating bignum boxes.

Define the actual native DEFSTRUCT with ordinary `:type` declarations, register
its exact getter/slot pairs with `DEFINE-RECORD-ACCESSORS`, then compile entries
with `DEFINE-ADMITTED-ENTRY` and `WITH-ADMITTED-ACCESS`. The owner supplies the
failure action and retains the exact bindings, layouts, code, storage and
mutation lifetime. Calls outside that lexical scope retain ordinary behavior.

The portable source closer preserves supported authored slot types in each
`:slot-types` layout description and checks typed writes. It does not yet
materialize those closed CLOS layouts as native Mezzano records.

Run `sbcl --script scripts/test.lisp` for portable checks. Native probes require
an owned archived Mezzano source and the four dependency directory variables
read by `scripts/mezzano-width-probe.lisp`. Run that script for layout and emitted
code checks, `scripts/mezzano-width-image.lisp` to build an isolated image, and
`scripts/mezzano-width-runtime.sh` with the same `SNOWGRAVE_MEZZANO_CACHE` to
execute the native boundary fixture.
