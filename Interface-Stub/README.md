# Interface stub overlay

For the M-F seal check, `FunctionCategory.lean` replaces only the opaque package
with an axiom of the same specification type. `scripts/check_seal.py` overlays it
on a fresh copy of Interface, preserving the transparent specification.

The stub is test-only and its axiom is rejected by the implementation audit. Both
builds run in CI via `scripts/swap_test.sh`; neither modifies the working tree.
Broad stub generation remains future work. See `Prototype/MatrixCategory.md`.

Cites: D-CH-25, D-RT-28, D-TL-17, AT-FD-2.
