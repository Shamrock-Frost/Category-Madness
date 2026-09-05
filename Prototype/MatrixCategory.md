# Discrete matrix monads to categories

Cites: D-FD-01, D-RT-25, D-RT-27, D-CH-14, D-CH-25, D-RT-28,
D-TL-17, D-WF-10, AT-FD-1, AT-FD-2, AT-FD-11, AT-RT-10.

This is the first end-to-end implementation. A matrix monad yields an ordinary
category structure, types and functions supply a concrete inhabitant, and a client
proves uniqueness of inverses using the sealed category laws.

## Construction

`Kernel.Matrix.Family A B` is `A → B → Type v`. A unit cell maps equality of labels
to an entry. A binary cell maps a pair of composable entries to an output entry.
`Kernel.Matrix.Monad A` bundles a horizontal family, those cells, and their unit and
associativity laws. This uses virtual multicells directly: it does not assume that
an intermediate-object sum forms another horizontal at the original entry universe.

`Root.MatrixCategory.toCategory` extracts hom types, identities, composition, and
all category laws. `ofCategory` constructs the matrix unit by equality transport
and multiplication from category composition. Both round trips are proved equal:
`toCategory_ofCategory` and `ofCategory_toCategory`. This compares with the ordinary
lawful structure defined in `Interface.Category`; it is not yet a Mathlib adapter.

`Kernel.Matrix.functions` has types as objects and functions as entries. Its object
level is `u+1` while its hom level is `u`. Concrete checks show that increment then
double maps 3 to 8, whereas double then increment maps 3 to 7.

| Dependency | Role |
| --- | --- |
| `Kernel.Matrix` | Matrix cells, monad laws, concrete function model |
| `Interface.CategorySpec` | Transparent dependent specification, no implementation imports |
| `Root.MatrixCategory` | Comparison in both directions and round-trip proofs |
| `Interface.FunctionCategory` | Opaque inhabitant containing carrier, operations, and laws |
| `Theory.Category` | Generic and sealed inverse-uniqueness proofs |

The shared specification is an independent module; the module dependency graph is
acyclic even though the Root construction uses that public specification type.

## Seal and evidence

`Interface.functionCategory` seals a complete `CategorySpec`, including its object
carrier. Its category fields are transparent logical projections. Consequently the
client can use the laws, but cannot identify the sealed carrier with `Type` by `rfl`.
The stub replaces only this inhabitant with an axiom of exactly the same type.
Transparent specification infrastructure is copied unchanged.

Run:

```sh
lake build
bash scripts/swap_test.sh
```

The swap check uses two new temporary projects and fresh build directories. It
copies the exact current source files, preserves the Lean options/toolchain, and
builds the identical client in each. The stub project contains no Kernel or Root
sources and inherits no project `LEAN_PATH`. The isolated configuration has no
Mathlib dependency because this entire fragment imports only Init; the main Lake
build still checks the normal repository configuration.

`scripts/SealAudit.lean` inspects elaborated constants, compares the complete public
types and universe parameters, follows client dependencies through transparent
aliases/projections, and calls Lean's `collectAxioms` on the fragment's declarations.
It stops proof-body traversal at public interface laws and opaque packages, while
still checking their types and transitive axiom dependencies. The implementation
allows only `propext`, `Quot.sound`, and `Classical.choice`; the stub run additionally
allows its single package axiom and checks that the client actually uses it.

Negative fixtures are excluded from every certified import. They demonstrate rejection
of an implementation-only equation, a project axiom of False, `sorryAx`, a private
implementation dependency behind an alias, and the stub under implementation audit.
The false-axiom, sorry, and leak fixtures must first compile, so unrelated syntax
errors cannot count as successful rejections.

The checker writes timings, logs, source hashes, and a public-signature digest to
`build/seal-check/`. A checked summary is stored in `Prototype/MatrixCategory-evidence.json`.

## Scope

AT-FD-2 is complete for this nonempty sealed fragment. AT-FD-1, AT-FD-11, and AT-RT-10
remain proposed: their full statements include further signatures, all foundation
outputs, or Segal-presheaf comparisons. This code does not construct the augmented
VDC∞ root, general substitution of multicells, profunctors, functors, the higher
nerve, or `Mod`. Those claims cannot be inferred from the ordinary category laws.

The next mathematical work can use these implementation modules directly, extending
the discrete matrix cells and their constructions while retaining this seal check.
