# Interface — bundled specification and seal

`CategorySpec.lean` is transparent logical infrastructure. `FunctionCategory.lean`
seals an inhabited package containing an object carrier, hom family, operations,
and laws. `SEALED` lists this initial package. Its API remains provisional.

Clients use its projections and proved laws; the implementation-only carrier
equation is deliberately unavailable. See `Prototype/MatrixCategory.md`.

Cites: D-CH-14, D-CH-25, D-RT-28, AT-FD-2.
