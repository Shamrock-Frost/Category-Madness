# 00 · Charter — revision 1

The goal is a Lean 4 library in which augmented virtual double ∞-categories provide a
common ambient language for ordinary, enriched, internal, and ∞-categorical theory.
Definitions, comparison theorems, and an implementation-independent interface are the
product. The exact ∞-root remains provisional until the foundation gates in
`11-foundation-feasibility.md` pass. Revision history and supersession are recorded in
`12-revision-notes.md`; the original documents are preserved verbatim in `history/v0/`.

## Principles

### D-CH-14 · Interface over implementation
**Decision.** Theory depends on exported operations and laws. Implementations may use
Mathlib and definitional equality internally. Transparent finite shape syntax and the
logical infrastructure of a bundled interface may compute; sealed categorical data may not.
**Rationale.** An abstraction boundary supports model changes. It does not by itself
prove that a theorem generalizes: the interface hypotheses and comparison theorems do that.
**Rejected.** Depending on implementation equations in Theory; claiming every use of
`rfl` is mathematically wrong. Reflexivity on interface expressions is legitimate.
**Acceptance.** AT-FD-2, the nonempty seal prototype and adversarial client.
**Status.** frozen policy; mechanism validated only by AT-FD-2.

### D-CH-15 · Witnesses of universal properties
**Decision.** Universal properties are propositions. Existence is a separate proposition;
when witnesses exist, their appropriate groupoid or space is contractible. Theorems
quantify over witnesses. Choice is confined to explicit bridge operations, including
sections of proved trivial fibrations where coherent choices are needed. There is no
global chosen-limit operation in the public theory.
**Rationale.** Uniqueness is categorical and does not identify Lean terms.
**Rejected.** Chosen-limit data typeclasses; inferring existence from uniqueness;
inferring a coherent section from pointwise choices alone.
**Acceptance.** AT-UP-1, AT-UP-6.
**Status.** frozen policy; coherence constructions provisional until proved.

### D-CH-16 · Unbiased and shape-indexed
**Decision.** Use shape-indexed limits and unbiased multimaps. Products are indexed by
sets; finite products are the finite case. Čech diagrams are obtained by augmented
`cosk₀` where the required limits exist. Composition is controlled by shape functoriality
and universal cells. Independently chosen composites require comparison paths or cells;
shape equality alone handles restrictions from the same diagram.
**Rationale.** Unbiased presentations organize coherence; they do not remove its proofs.
**Rejected.** Treating weak composites as strictly equal; requiring a general coherence
tactic before the mathematical comparison lemmas exist.
**Acceptance.** AT-UP-6, AT-FD-10.
**Status.** frozen policy; computational API provisional.

### D-CH-17 · One ambient language, explicit comparisons
**Decision.** `Category` is a monad in `Mat(Set)`; the intended `InfCategory` is a monad
in `Mat(Kan)`. Functors, profunctors, and transformations come from `Mod`. A bootstrap
Segal-category presentation is allowed in Kernel/Root and behind a sealed interface;
its identification with the monad construction is a required theorem, not a second
permanent public definition. Vertical 2-cells and the groupoids they generate are
retained when extracting categorical mapping spaces.
**Rationale.** Reuse is a theorem about a sufficiently strong interface, not a ban on
intermediate presentations needed to build that interface.
**Rejected.** Identifying raw vertical paths with functors and natural equivalences;
claiming that every universal property of an underlying (∞,1)-category is a lax 2-limit.
**Acceptance.** AT-RT-10, AT-RT-12, AT-SP-3, AT-FD-4.
**Status.** frozen objective; ∞-identification provisional until proved.

### D-CH-18 · Preferred root presentation
**Decision.** The preferred root is a reduced, labelled Segal presheaf on an augmented
planar shape category. Object values are terminal simplicial sets; cells may have
empty horizontal targets. Kan values and the appropriate homotopy Segal limits are
part of the specification. Actual arities, fibrancy, and comparison conditions are
proved at M-F before this presentation is frozen.
**Rationale.** Labels are a useful presentation device. Categorical mapping spaces may
still require completion or localization. Ordinary active chains describe only the
unaugmented cases for which a presentation theorem has been proved.
**Rejected.** Contractible object values as a substitute for a reduced presentation;
a blanket rejection of completeness machinery; unproved equivalence with style A.
**Acceptance.** AT-FD-3, AT-FD-4, AT-FD-7, AT-FD-8; full AT-RT-9 at M6+.
**Status.** provisional. Changing the model is an allowed M-F outcome.

### D-CH-26 · Construction-specific closure
**Decision.** Every exported construction has explicit input hypotheses, an output
specification, its relevant invariance theorem, and any required fibrancy theorem.
There is no blanket fixed-target rectification theorem. A comparison may replace a
model by an equivalent strict model; strict maps into the original model are a
stronger, separately stated claim. No `hP` truncation is assumed for arbitrary roots.
**Rationale.** A named future theorem is not evidence that its hypotheses hold.
**Rejected.** A universal closure checklist whose individual entries have not been
formulated; silently using levelwise invariance as categorical invariance.
**Acceptance.** AT-FD-5, AT-FD-6, AT-FD-8, AT-FD-10.
**Status.** frozen export policy; mathematical instances provisional until proved.

### D-CH-19 · Definitions and validation
**Decision.** Definition-level decisions name acceptance tests with exact domains and
comparison targets. Tests progress through proposed, stated, and proved. A revised
statement invalidates prior validation until its proof is rechecked. Foundation choices
remain provisional until M-F; a false test requires revising the definition or the
advertised claim, not adding an axiom.
**Rationale.** This project includes mathematical research as well as proof production.
**Rejected.** Freezing conjectural definitions solely because proofs are scheduled.
**Acceptance.** All AT-FD tests and the registry audit in D-WF-10.
**Status.** frozen policy.

### D-CH-20 · Layering
**Decision.** Lean declarations, tests, and decision records are primary. Generated
notation and declaration documentation are views of them. Handwritten rationale and
research questions remain primary prose, and are never regenerated from signatures.
**Rationale.** Computation can synchronize signatures; it cannot recover design intent.
**Rejected.** Hand-maintained duplicate signatures in documentation.
**Acceptance.** AT-KR-0 and the M0 export round-trip.
**Status.** frozen policy; formatting provisional.

## Bootstrap and scope

### D-CH-21 · Three stages
**Decision.** Kernel/ uses Mathlib freely for shapes and homotopy machinery. Root/ builds
and validates the common definitions and exposes Interface/. Theory/ imports only that
interface. Prototype/ holds M-F experiments and is not part of the public interface.
**Rationale.** The logical stages are separate from implementation milestones; small
pieces of later kernel work may be pulled forward into M-F.
**Rejected.** Waiting until M6 to exercise the ∞-semantics of a root frozen at M3.
**Acceptance.** AT-FD-2 and M3's full swap build.
**Status.** frozen layout policy.

### D-CH-22 · Hard seal
**Decision.** Theory cannot directly import Kernel/, Root/, or Mathlib category theory
and algebraic topology. Compiled statement and proof dependencies are audited; a source
import grep is only a preliminary check. Tactics are allowed if their proof terms
respect the boundary. Both stub and kernel-backed builds run on each merge candidate.
**Rationale.** Imports and tactics can introduce transitive dependencies.
**Rejected.** Treating a passing stub build as a consistency proof.
**Acceptance.** AT-FD-2, AT-FD-11.
**Status.** frozen policy.

### D-CH-23 · Full universe polymorphism
**Decision.** Separate object and hom universes in category APIs. Root label collections,
entry types, and spaces of matrices are not required to occupy the same universe.
Universe maxima and successor levels required by Lean are explicit (D-RT-27).
**Rationale.** Large collections of small objects remain large collections.
**Rejected.** Using augmentation or `ULift` as universe lowering.
**Acceptance.** AT-FD-1.
**Status.** frozen policy; concrete signatures validated at M-F.

### D-CH-24 · Dependencies
**Decision.** Lean and pinned Mathlib are the mathematical dependencies. Other library
constructions may be ported with attribution. Documentation tooling has separately
pinned dependencies. No new foundation axiom is introduced by a port.
**Rationale.** Keep the proof trust base and version inventory explicit.
**Rejected.** Treating an imported theorem statement as a proved port.
**Acceptance.** AT-KR-0, AT-FD-11.
**Status.** frozen policy.

### D-CH-25 · Sealing a specification
**Decision.** Seal data together with their laws, using an opaque inhabitant of a
specification structure or an explicitly audited irreducible implementation. The
kernel-backed implementation inhabits the complete specification. An axiom stub may
replace that implementation for fast client builds; its axioms are prohibited in the
kernel-backed build. A future self-hosted kernel must inhabit the same specification.
**Rationale.** `opaque n : Nat := 0` alone does not export `n = 0`.
**Rejected.** Independently opaque operations with unconnected postulated laws.
**Acceptance.** AT-FD-2, AT-FD-11.
**Status.** frozen policy; prototype required before architecture freeze.

## Success criteria

The seal has a real implementation and passes the swap test; discrete instances recover
classical categories and augmented VDCs; categorical maps detect natural equivalences;
the coherent formal theory specializes correctly; monads in the spaces matrix ambient
agree with Segal categories. These are separate tests, not consequences of one slogan.

Algebra, analysis, geometric realization, general strict higher-category libraries, and
self-hosting are outside the immediate critical path. The geometric substrate and
additional shape families are optional extensions after M-F.
