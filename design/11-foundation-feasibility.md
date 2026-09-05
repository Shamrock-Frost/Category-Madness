# 11 · M-F: foundation feasibility

**Position:** after M0, before M1. **Current state:** in progress; the initial inventory, minimal universe, seal, and small ordinary
example work is checked. The remaining gates are open. **Purpose:** establish a viable small path
through the foundation before expanding the library or freezing its conjectural root.

This milestone can be substantial. “Small” means one root, a few decisive examples,
and only their necessary machinery; it does not mean a finite checklist magically
proves a new ∞-categorical nerve theorem. Definitions of shapes, diagrams, and
replacement needed by these gates are pulled forward from M1/M2.

### D-FD-01 · Gate the foundation before scaling it
**Decision.** M-F requires the eleven gates below. Each names a mathematical statement
or executable check, dependencies, evidence, and a failure response. A mathematical
component passes only with a checked Lean proof of its current statement and approved
axioms. A tooling component passes only with a reproducible build/check record. Current
prose is not proof evidence. No root or interface freeze may assume an unpassed gate.
**Rationale.** The initial review found contradictions that a larger proof schedule
would not resolve. Test the semantics and implementation boundary before broad reuse.
**Rejected.** Freezing an ∞-definition solely on a discrete nerve test; treating a
proof assigned to an agent as evidence that its statement is true.
**Acceptance.** AT-FD-1 through AT-FD-11 and the final dependency audit.
**Status.** frozen process policy authorized for this revision; all gate evidence pending.

## Gate definitions

### AT-FD-1 · Universe signatures

State the Lean universes of the root, labelled shapes, matrix families, walking
structures, monad collection, `Mod`, and projected category API. Check the intended
matrix signature from D-RT-27 and the individual entry/collection levels.
Compile examples with object/entry levels `(0,1)`, `(1,1)`, and `(1,0)`, plus the
intended `Set`, small-space, and category collections. Provide necessary lifts and
prove their comparison lemmas; no universe-lowering axiom is allowed.

**Depends on:** M0 toolchain; minimal types only. **Evidence:** actual declarations,
compiled examples, universe table. **Failure response:** increase collection universes
or separate parameters; do not weaken the category API by silently forcing `u=v`.

### AT-FD-2 · A nonempty sealed interface

Build one dependent specification containing a carrier, nontrivial operations, and
laws; provide its kernel-backed inhabitant. Expose an opaque package with transparent
logical projections, or the precisely audited alternative from D-RT-28. Prove a
client theorem that uses the laws. Build the identical client against a stub package.
Also supply a client depending on an implementation equation and show the checking
pipeline rejects it. Confirm both builds use the same public signatures and record a
small performance measurement. The prototype does not need the whole root.

**Depends on:** M0; AT-FD-1 if universes are shared. **Evidence:** both successful builds,
negative-test failure, dependency audit, and timing. **Failure response:** revise the
seal packaging before creating broad Theory clients.

### AT-FD-3 · Reduced labels and homotopy gluing

For labelled Δ and then the selected augmented arities, implement terminal object
values and full boundary diagrams. Prove the endpoint and cell fibrancy hypotheses
needed by the chosen model. Prove that the actual strict Segal core computes the
homotopy core where strict limits are used; otherwise keep the homotopy-core
implementation and prove the operations it requires.
As a negative regression, use the two vertex inclusions into the contractible nerve
of the walking isomorphism: their strict pullback is empty and their homotopy pullback
is contractible. The old argument from contractibility alone must not certify the gate.
Prove the chosen reduced replacement and label reindexing preserve this specification.

**Depends on:** AT-KR-0 inventory, the relevant AT-KR-10 lemmas, AT-FD-7 for the augmented
instance. **Evidence:** comparison and replacement lemmas, plus the negative example.
**Failure response:** strengthen fibrancy or use homotopy limits; changing reduction is
an explicit root decision and resets dependent tests.

### AT-FD-4 · Categorical maps retain natural equivalences

Implement `MapRel` and `MapCat` with distinct types/specifications. Let I be the
ordinary walking isomorphism and G a nontrivial finite group, initially `C₂`.
Show that the disjoint fixed-label strict-map spaces for `1 → I` have two components,
whereas `MapCat(1,I)` is contractible. Show `MapCat(1,BG) ≃ BG`, retaining the automorphism
loop. Construct the bridge through a categorical framing/localization or complete
presentation, and compare the categorical functor object for ordinary C,D.
For the matrix/Mod instance from AT-FD-8, verify that `VertCore` has these natural
equivalences and that `VertRaw` is not silently substituted for it.

**Depends on:** the selected Segal-category comparison machinery; relative model
lemmas; AT-FD-8 only for the final root-instance check. **Evidence:** the two example
computations, the general ordinary-category bridge, and the root-instance comparison.
**Failure response:** revise the framing or vertical extraction; Reedy replacement
alone is not an alternative proof.

### AT-FD-5 · The root equivalence relation

1. In the discrete case use the chaotic strict monoidal category on `C₂`, with tensor
   given by group addition and exactly one morphism between each pair. Its full
   monoidal subcategory on the unit induces an equivalence of augmented VDCs despite
   having fewer horizontal arrows. Prove that the revised predicate accepts it.
2. Include isomorphic object representatives with horizontals at transported endpoints.
   Check the simultaneous endpoint/horizontal choices, not only literal image endpoints.
3. Prove equivalence with the exact classical augmented-VDC notion for discrete roots.
4. State the full proposed ∞-predicate without the deleted `hP`; prove composition,
   2-out-of-3, and compatibility with the local examples used by AT-FD-8. Relate it to
   the chosen unary-cell/categorical model on this required fragment. A full comparison
   with another VDC∞ theory is AT-RT-9; these foundational local results are mandatory now.

**Depends on:** the minimal augmented nerve and cell constructions, AT-FD-7 and the
needed AT-FD-3 machinery. **Evidence:** the four groups of results, with the ∞-predicate
actually stated. **Failure response:** revise the predicate or root model; do not
restore bijectivity of horizontal-object spaces merely to simplify the proof.

### AT-FD-6 · Boundary monodromy and the direct coherent route

Construct the fibration over `BC₂` associated with its transposition action on two
points and compute the nontrivial action on fibre components. Demonstrate that the
constant and generating loops give different transport maps. The public signature
contains no generic representative-based `hP` construction.
For a small cell-space example, retain the boundary data and prove the composition
or universal-cell fact needed by the selected prototype directly, without such a
truncation. If a homotopy-level intermediate is used, state and prove its precise
comparison for that example. This gate does not demand a repaired general `hP`.

**Depends on:** small groupoid/Kan and cell-space machinery. **Evidence:** the monodromy
calculation, an interface dependency audit, and the direct coherent example.
**Failure response:** retain more boundary information or revise the proof route;
quotienting away monodromy is not justified by choosing representatives.

### AT-FD-7 · Actual augmented shapes and their diagram model

Define the exact generating incidence data, operations, and equations of the set-level
augmented VDC. Build the free/arity presentation with the hypotheses actually used by
its nerve theorem. Validate `c₁^∅`, `(0,0)` cells and both their compositions, nullary
inputs, mixed rows, and shared sides. Prove the no-horizontal fragment recovers
2-categories, including composition laws. Reject the attempted ordinary active
`[0] → [1]` encoding of a one-input/empty-output transition.
Supply the diagram model required by `MapRel` and `Mod`: Reedy/elegance if that route
works, or a concrete alternative with the necessary cofibrant-source, relative
restriction, and replacement results. A fallback is accepted only with those results.
Prove any canonical encoding used by the prototype; flags or drawings alone are not
an arity or normalization theorem.

**Depends on:** minimal category/arity theory from the inventory. This gate supplies
the shape prerequisites for AT-FD-3 and AT-FD-8; it is not allowed to rely on them for
the definition of its own category. **Evidence:** algebra, shape presentation, nerve
hypotheses, fragment comparison, and actual model lemmas. **Failure response:** revise
the presentation; if no workable augmented shape/model route exists, stop the current
root track and produce a model-change decision.

### AT-FD-8 · Relative walking constructions and a nondiscrete instance

Construct the functorial inclusions `B_θ → N W_θ`, fixing entire vertex monads. Prove
that the point fibre is a point, and compute vertical-arrow, bimodule, and binary-cell
values with all selected structures fixed. Establish the fibrancy or functorial
homotopy-fibre mechanism used, Segal comparisons, units, and required composition maps.
Prove the needed invariance under `LevelEq` and the chosen `VDCEq` separately.

Use a small matrix-like ambient of explicit spaces including a two-point space and
its swap automorphism. Its horizontal classifier must retain that loop and its cells
must recover the actual map spaces over chosen boundaries. Specify a collection closed
under the operations the example uses; do not assume a finite arbitrary collection
is closed. Build a nontrivial monad, module, and cell in it, then exercise `Mod` and
categorical vertical extraction. This can precede a classifier of *all* small spaces
and `HasColimits Kan`.

As a separate slice precursor, fix the whole cone at each vertex and calculate its
point and edge fibres; the full slice construction remains AT-UP-3 at M4.

**Depends on:** AT-FD-1, the core parts of AT-FD-3/5/7, and the framing portion of
AT-FD-4. **Evidence:** exact constructions and proofs for this end-to-end instance;
the final AT-FD-4 root check then uses this result. **Failure response:** revise walking
diagrams or the root, not just add more pointwise choices.

### AT-FD-9 · Correct symmetry ambient

In the discrete setting construct the relevant fragment of the free symmetric monoidal
category on the terminal discrete category inside `Prof(Set)`. In arity two its
automorphism group is `Σ₂`; identify the corresponding one-colour collections with
sets carrying a `Σ₂`-action (and equivariant maps). Compare this with indexing over a
discrete object set, which loses that action data. Fix profunctor variance explicitly.
No full ∞-operad construction is required at this gate.

**Depends on:** the discrete matrix/profunctor prototype; no spaces colimits.
**Evidence:** arity-two action and morphism comparison. **Failure response:** revise
the ambient or the indexing mechanism before asserting symmetric-sequence equivalence.

### AT-FD-10 · Scope coherence and rectification

State the prototype's actual rectification theorem, including permitted model changes,
source conditions, fixed boundary data, and the equivalence relation on maps. Verify
that no generic fixed-target surjectivity statement appears as an unproved export.
For pasting, prove a shared-diagram restriction equality and a nondiscrete comparison
between chosen composites, with the latter typed as a path/cell as appropriate.
This gate certifies the stated scope, not an unproved universal normalization theorem.

**Depends on:** the relevant shape, cell, and mapping constructions.
**Evidence:** exact scoped theorems, the two pasting clients, export audit.
**Failure response:** narrow the export or build the missing comparison theorem;
never replace a path comparison with strict equality merely for tactic convenience.

### AT-FD-11 · Trust and dependency audit

Run kernel-backed and stub builds against the identical prototype revision. Check
elaborated interface/proof dependencies, explicit universe examples, the axiom
allowlist, and active decision references. Deliberately inject a project axiom of
False in a negative-test target and show its use is rejected as acceptance evidence;
likewise reject `sorryAx`, stub axioms in the implementation build, and a private
implementation leak. Keep these test fixtures outside certified imports.
Produce an acyclic dependency graph at the granularity of the actual lemmas, including
those pulled forward from the originally later milestones.

**Depends on:** all prior gate outputs and the seal prototype.
**Evidence:** build/check logs, allowlist, negative tests, and dependency graph.
**Failure response:** do not certify or freeze the foundation until the failure is resolved.

## Work order without circular gates

1. Inventory, universe and seal prototypes; small discrete category/groupoid examples.
2. Augmented algebra/shapes and their required diagram-model lemmas (AT-FD-7).
3. Reduced gluing/replacement and the standalone categorical framing (core parts of
   AT-FD-3/4), plus monodromy and the discrete equivalence tests.
4. State/prove the remaining equivalence laws; build relative walking constructions
   and the nondiscrete example (AT-FD-5/8).
5. Check that example's categorical extraction to finish AT-FD-4; finish the scoped
   pasting, symmetry, and final audit gates.

The subparts of AT-FD-4 are deliberately separated: its framing is a prerequisite of
the example, while its final root comparison is a client of that example. A gate-level
mutual reference does not authorize a circular Lean proof.

## Interpreting failures

Universe offsets, object reduction, and specification packaging have direct candidate
repairs. The old unconditional `hP` is removed from required architecture, so failure
to recover it is not failure of M-F. The material research risks are the augmented
arity/model theory, coherent `Mod`, and the intended equivalence/categorical comparison.
A negative result for those could require a different root presentation or a smaller
first release. It would not by itself refute the broader goal of a common,
interface-driven categorical library.
