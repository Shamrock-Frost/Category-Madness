# Interface/ — the seal (D-RT-13)

Exactly the list in D-RT-13 (`dec-rt-0013`), nothing else: shapes as categories, `Space`,
the root, the constructions, the closure and rectification package. Constants are
`opaque` (inhabited from the kernel) or `@[irreducible]` with private equation lemmas;
every exported theorem is stated in interface vocabulary only (scripts/check_statement_hygiene.py).

Two-tier extension policy: new constants need a superseding decision; lemmas statable in
interface vocabulary and provable in `Root/` may be added by PR.

`SEALED` (to be generated at M3) lists the sealed constant names for scripts/check_unfolding.py.

Empty at M0. Interface v1 is frozen at M3.
