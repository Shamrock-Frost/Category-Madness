# Initial foundation implementation

This completes the first work item in the M-F dependency order: a pinned dependency
inventory, minimal universe contracts and comparisons, and small ordinary
category/groupoid checks. The existing nonempty seal is rechecked separately.

Cites: D-KR-14, D-KR-19, D-KR-22, D-RT-16, D-RT-23, D-RT-24, D-RT-27,
D-SP-10, D-CH-20, D-CH-24, D-WF-08, D-WF-10, AT-KR-0, AT-FD-1, AT-FD-2.

## Reproduce

Follow [CONTAINER_SETUP.md](../CONTAINER_SETUP.md) if the container needs the
documented executable-path shim. Use the pinned toolchain and dependencies.

    lake build
    python3 scripts/check_foundations.py
    bash scripts/swap_test.sh
    python3 scripts/forest_check.py
    python3 scripts/check_revision.py
    python3 scripts/check_imports.py
    python3 scripts/check_unfolding.py
    python3 scripts/check_statement_hygiene.py
    python3 mcp/server.py --selftest

The foundation checker builds its own audited targets, reads declarations from the
Lean environment, checks the transitive axiom closure, verifies the dependency pin
and source hashes, and compares the generated evidence. After an intentional
source or dependency change, run it with --write, then regenerate the registry with
scripts/build_registry.py. Review upstream gaps whenever the pin changes.

## Dependency inventory

The exact names, universe parameters, elaborated types, source positions, direct
dependencies, scoped reverse dependencies and axiom closures are generated in
[inventory.json](inventory.json). The pin is Lean 4.33.1 / Mathlib v4.33.1,
Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474.

| Area | Available entry points | Limits relevant to the foundation |
|---|---|---|
| Categories | CategoryTheory.Category, Functor, NatTrans, Cat | Object and hom universes remain independent. |
| Labelled shapes | Functor.Elements, categoryOfElements, NatTrans.mapElements | Generic category-of-elements machinery; no augmented incidence algebra is supplied. |
| Ordinary nerves | CategoryTheory.nerve, Nerve.strictSegal, nerveAdjunction, nerveFunctor.fullyfaithful | The nerve has independent object/hom levels. The inventoried adjunction/full-faithfulness API uses equal levels; it does not identify derived MapCat for the proposed root. |
| Groupoids | SingleObj.groupoid, SingleObj.toEnd, groupoidOfElements | No groupoid-nerve Kan result was located in the bounded source search; the corresponding instance fails in the selected import closure. |
| Simplicial sets and Kan fibrations | SSet, SSet.KanComplex.hornFilling, modelCategoryQuillen.fibration_iff | Open the scoped Quillen fibration instances. These do not supply a complete model category. |
| Mapping spaces | CategoryTheory.ihom, SSet.fibration_pullbackObjObjπ | Internal hom into a Kan target is Kan. Restriction is a fibration for a monomorphism and a Kan target. Both claims have compiled witnesses here. |
| Relative maps | SSet.RelativeMorphism, RelativeMorphism.HomotopyClass | Strict relative maps and homotopy classes do not provide the derived fixed-label MapRel or categorical MapCat required later. |
| Weak equivalences / model categories | HomotopicalAlgebra.CategoryWithWeakEquivalences, WeakEquivalence, ModelCategory, PathObject | Generic machinery requires explicit instances. SSet's full Quillen structure is an upstream TODO; the selected closure has neither a weak-equivalence nor a model-category instance for SSet. |
| Reedy machinery | HomotopicalAlgebra.ReedyStructure, ReedyStructure.op, mapFactorizationData | The diagram model structure is an explicit upstream TODO. It cannot be assumed for augmented labelled arities. |

The JSON records the bounded source-search scope and digest, exact TODO locations,
and negative instance probes. A search failure is not a theorem of nonexistence.
In particular, the generic model-category definitions are not evidence that the
simplicial-set or diagram-model instances exist.

The compiled witnesses in Kernel/Foundations/Inventory.lean use only available
machinery. Later proof routes must cite these entries or state the additional
project lemmas they require.

## Universe gate

The [universe table](signatures.md) is generated from actual declarations.
Root/Foundations/UniverseChecks.lean checks all requested orderings (0,1), (1,1),
and (1,0), plus Type/Set, small spaces, classifier data and category collections.
It also checks the intended ambient offsets in D-RT-27 symbolically. Existing
matrix family and projected-category tests are reused unchanged.

The shape category and its position functor are explicit small inputs. A labelled
shape category is constructed as the opposite of the category of elements of the
contravariant labelling functor. RootSignature bundles labels and a diagram with
a supplied proposition-valued condition; this tests the universe of any later
root conditions without asserting those conditions or their satisfiability.

WalkingSignature records the boundary, whole walking diagram and inclusion.
MonadCollection measures all labels with maps out of supplied full walking monad
nerves. RelativeChoice is explicitly a strict relative choice. ModSignature records
the output diagram carrier at the resulting label and simplex sizes. It does not
construct coherent Mod, a derived relative fibre, or pointwise replacements.

Collecting all diagram maps can increase the label and simplex levels to their
maximum. The small-space classifier's data collection is one successor above
its base/total simplicial-set level. These increases are explicit in the checked
table; no equality of object and hom universes, or universe-lowering axiom, is used.

Label lifting is an actual equivalence of indexing categories. Simplex lifting
comes with mutually inverse map comparisons, a hom equivalence, and identity and
composition laws. Lowering applies only to maps between specified lifted objects.
The existing matrix entry/label comparisons remain part of the compiled gate.
Kan preservation of these lifts and classifier classification/univalence laws
belong to later semantic constructions.

This passes AT-FD-1 as its stated minimal-types gate. It does not establish the
augmented shape presentation, Kan/Segal root axioms, walking nerves, coherent Mod,
or classifier laws. Those obligations retain their separate acceptance gates.

## Small example and exporter

Kernel/Foundations/Examples.lean constructs the one-object groupoid of Boolean
permutations. Its displayed loop is not the identity, its square is the identity,
every arrow has an inverse, and its ordinary nerve satisfies strict Segal laws.
The ordinary-category and seal examples already in the repository are preserved.

The M0 exporter round-trip uses the existing quarantined
Prototype/Negative/Sorry.lean fixture. Its theorem is exported from a separate
Lean environment and parsed back through the forest registry parser. Its status
remains stated because its axiom closure contains sorryAx. The generated forest
node prominently records that it is an unfinished negative fixture, not a result.
No certified target imports it.

## Next work item

The current task is the augmented algebra/shapes and required diagram-model
lemmas under AT-FD-7. Its [current implementation](../augmented/README.md)
adds incidence, the equation families, a lawful additive-label algebra, shape/label
separation, explicit boundary transport and strict 2-category extraction to the same
compiled inventory and axiom audit. The reverse algebra laws, cell/hom round trips,
arbitrary substitution compatibility and discrete hom nerves are now checked.
The relative free cell algebra now has proved quotient laws, a universal mapping
equivalence and finite raw-term support. The global free/forgetful adjunction
and fully faithful comparison are checked. Arbitrary generating-monad algebras
now yield vertical categories, incident cells and primitive operations, with a
surjective full-boundary evaluation map preserving identities and substitution.
All five reconstructed equation families and action identification now prove
essential surjectivity and monadicity. The actual free-arity nerve square, both
monadic comparisons and the canonical monad map are constructed. The conditional
nerve theorem assumes density of the selected arities and invertibility of that
specific comparison. Finite incidence supports, their filtered-colimit presentation and the equivalence
between finite incidence and finite presentability are now proved. A small dense
candidate family of finite incidence diagrams is constructed. Its monad comparison
invertibility, the unconditional augmented nerve theorem and the labelled diagram
model remain open. The complete gate, M-F milestone and
root/interface freeze remain open.
