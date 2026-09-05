# Matrix universe prototype

Cites: D-FD-01, D-CH-23, D-RT-25, D-RT-27, D-WF-10, AT-FD-1.

This is the matrix-family and entry-lift portion of AT-FD-1, statement version 1.
The full gate remains **proposed**: its root, labelled shapes, walking structures,
monad/Mod collections, space classifier, category projection, and other necessary
lifts have not yet been stated or checked. The prototype exports no sealed API.

`Matrix.lean` defines families, maps fixing the labels, identity and composition,
and entry lifting through `ULift`. Its seven theorems state identity and associativity
laws, both inverse laws for lifting maps, and preservation of identity and composition.
`lowerMap` works only between specified lifted entry types; it cannot lower arbitrary
types or their collections.

All declarations are in `Prototype.Universes`; map operations and laws are in its
`Matrix` namespace. Only Lean's implicit `Init` import is needed.

| Expression | Universe |
| --- | --- |
| Object types `A`, `B` | `Type u` |
| Collection of object types `Type u` | `Type (u + 1)` |
| Entry `M a b` | `Type v` |
| Family collection `Matrix A B` | `Type (max u (v + 1))` |
| Maps `Matrix.Map M N` | `Type (max u v)` |
| Lifted entry | `Type (max v w)` |
| Lifted family collection | `Type (max u (max v w + 1))` |

`Examples.lean` asserts the collection levels for `(u, v) = (0, 1), (1, 1),
(1, 0)` and supplies actual families and identity-law clients at each pair. It
also exercises both inverse laws with `(u, v, w) = (1, 0, 1)`. These examples
test the matrix-family component of D-RT-27, not the entire proposed root signature.

## Reproduce

With the pinned Lean toolchain installed:

```sh
lake build
lake env lean Prototype/Universes/Examples.lean
python3 scripts/forest_check.py
python3 scripts/check_revision.py
python3 scripts/check_imports.py
python3 scripts/check_unfolding.py
python3 scripts/check_statement_hygiene.py
python3 mcp/server.py --selftest
bash scripts/swap_test.sh
```

`Prototype` is the default Lake target while the four planned layer libraries have
no Lean modules. Their library declarations remain available for subsequent work.
`lake-manifest.json` records the resolved pinned dependency revisions. This prototype
does not require Mathlib's compiled cache; on a first setup, the optional download
can be skipped with `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update`.

The examples print the axiom dependencies of all seven theorems. These reports are
local evidence for the matrix lemmas; the complete AT-FD-11 dependency audit remains
outstanding. The swap script currently skips because there are no Theory clients.

## Check record

Checked on 2026-09-05 with Lean 4.33.1, release commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`:

- Both Lean modules compiled, including all explicit universe examples.
- `lake build` passed with the `Prototype` default target (5 jobs).
- Forest, revision lineage, import, unfolding, and statement-hygiene checks passed.
- The registry retrieval self-test passed (289 nodes).
- The swap script reported no Theory sources and skipped; no seal evidence is claimed.

The theorem axiom reports were:

| Theorems in `Prototype.Universes.Matrix` | Axioms |
| --- | --- |
| `id_comp`, `comp_id`, `comp_assoc` | None |
| `lowerMap_liftMap`, `liftMap_comp` | None |
| `liftMap_lowerMap`, `liftMap_id` | `Quot.sound` |

`Quot.sound` is a standard Lean axiom allowed by D-TL-17. No theorem depends on
`sorryAx`, a stub axiom, a project axiom, or a universe-lowering axiom.

The execution environment lacks `/proc/<pid>/exe`. A local launcher adapter supplied
the current executable path from `AT_EXECFN` for that lookup; the released Lean
compiler, kernel, libraries, and proof terms were unchanged. This is an environment
accommodation, not part of the project or its mathematical dependencies.
