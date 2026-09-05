# 06 · Tooling — revision 1

Tooling is staged around validated mathematics. M0 provides inventory and a minimal
registry. M-F provides a real seal prototype. Broader generators and retrieval follow
once there is a meaningful environment to index.

### D-TL-12 · Provisional agent conventions
**Decision.** Naming, formatting, and generator interfaces remain provisional. Agents
may propose changes with mechanical migration and regenerated views. A mathematical
definition frozen after its gates changes only through a superseding decision; changes
authorized in revision 1 are recorded in its crosswalk and original snapshot.
**Rationale.** Conventions can evolve without silently changing theorem meanings.
**Rejected.** Treating a provisional convention as permission to alter a frozen theorem signature.
**Acceptance.** Registry/supersession audit at M0 and AT-FD-11.
**Status.** frozen policy; conventions provisional.

### D-TL-13 · Generated human layer
**Decision.** Generate notation, binary wrappers, signature documentation, and thin
APIs from declarations and proved laws. Preserve handwritten rationale separately.
Regeneration is checked once a generator is adopted.
**Rationale.** Generated signatures should stay synchronized without erasing human decisions.
**Rejected.** Hand-editing generated artifacts or generating unproved laws.
**Acceptance.** M3 nontrivial client and regeneration check.
**Status.** provisional; no large generator prerequisite for M-F.

### D-TL-14 · Duality tooling
**Decision.** Build `to_dual` for a registered collection of proved duality operations
and transport laws. Automatically generate the supported Segal-category cases. Record
hand-proved duals outside that domain; report unsupported transformations explicitly.
**Rationale.** The scope follows actual mathematical dualities.
**Rejected.** A total transformation on augmented roots without a valid vertical opposite.
**Acceptance.** AT-UP-5 and AT-UP-7 after the underlying operations are proved.
**Status.** provisional, M4; simple prototypes may precede it.

### D-TL-15 · Witness transport
**Decision.** A witness-transport tactic uses registered functoriality lemmas on witness
categories. It fails with the missing lemma when a construction has no justified
transport. It never proves equality of arbitrary Lean witness terms from categorical uniqueness.
**Rationale.** The automation should expose missing mathematical structure.
**Rejected.** Rewriting all witnesses to a global chosen object by definition.
**Acceptance.** AT-UP-1 and a nontrivial limit-witness client at M4.
**Status.** provisional, M4.

### D-TL-16 · Shape extension
**Decision.** An extension command states the relevant pointwise universal property,
uses proved existence/coherence theorems, and names a witness. It does not invent an
extension from a collection of pointwise choices. Its primary example is Čech `cosk₀`.
**Rationale.** The command packages a construction already justified by the interface.
**Rejected.** Closing coherence obligations solely by generated syntax.
**Acceptance.** AT-UP-6 and AT-UP-7.
**Status.** provisional, M4.

### D-TL-20 · Pasting with an explicit target
**Decision.** The first `paste` handles discrete composites and equal restrictions
`P(σ)(d) = P(σ')(d)` from the same diagram. It reduces the latter to a proved decidable
shape-map equality. For separately chosen weak composites, use comparison lemmas to
construct a path, invertible cell, or higher comparison of the correct type; equality
of shapes does not supply equality of points. A future ∞-tactic may organize these
lemmas, but no general normalization theorem is assumed.
**Rationale.** Unbiased syntax still needs coherence when the diagram witnesses differ.
**Rejected.** An unconditional reduction of all weak pastings to finite equality.
**Acceptance.** AT-FD-10, AT-RT-12; one nondiscrete comparison example before expanding scope.
**Status.** provisional; discrete version M3.

### D-TL-21 · Shape representations
**Decision.** Use transparent finite data for shape syntax and morphisms after proving
its presentation theorem. Input/output incidence data handles augmented cases; flagged
rows are only a candidate encoding. Derived `DecidableEq` for syntax is not equality
of quotient morphisms: a normal-form theorem or another decision procedure is needed.
JSON formats, validation, and renderers follow the proved datatype. Transparent shape
computation is allowed in Theory; its categorical interpretation uses sealed bridge laws.
**Rationale.** A serialization is an implementation of a proved presentation.
**Rejected.** Advertising row, cube-word, or symmetry syntax as canonical without proving
that the relations are respected and equality is decided correctly.
**Acceptance.** AT-FD-7; later AT-KR-3 and any client-specific shape presentation.
**Status.** provisional; exact formats are not frozen before the mathematics.

### D-TL-22 · Drawing and import
**Decision.** Begin with a text format and renderer for validated elementary shapes.
General molecule import, interactive editing, and external interchange are optional
clients after the corresponding presentation and typing checks exist.
**Rationale.** A drawing should round-trip to checked boundary data.
**Rejected.** Letting a renderer's limitations determine the mathematical shape category.
**Acceptance.** Round-trip and invalid-boundary examples for each activated format.
**Status.** later except the small M-F examples.

### D-TL-17 · Seal, axiom audit, and CI
**Decision.** The checks below are required before merge once their code exists.
1. Check direct imports and elaborated statement/proof dependencies. Ban Theory
   references to private implementation constants. Audit transitive dependency routes;
   approved interface laws may have kernel-backed proofs behind the seal.
2. Guard sealed unfolding with syntax checks, then use the stub build as the semantic
   client-independence check. Do not ban ordinary equality transport or reflexivity
   merely for mentioning a sealed type. Transparent specification projections and
   shape syntax are explicitly allowed.
3. Check interface types by elaborated constants, including implicit arguments and
   typeclass instances; a grep alone is insufficient.
4. Build the same merge candidate against the bundled implementation and its stub.
   Preserve transparent infrastructure in the stub. Audit the implementation of every
   exported operation and law through the complete specification witness.
5. Run `collectAxioms` over acceptance tests and exported declarations. In the
   kernel-backed build allow only the explicitly audited standard Lean axiom set for
   the pinned toolchain (normally `propext`, `Classical.choice`, `Quot.sound`). Reject
   `sorryAx`, stub axioms, and unapproved project axioms. WIP declarations are visibly
   unvalidated and cannot certify an acceptance test or enter the public dependency path.
6. Compile the explicit universe examples with `autoImplicit false`; that option alone
   is not a universe-polymorphism test.
7. Check decision/test cross-references, supersession, and adopted generators.
**Rationale.** A stub tests abstraction; the kernel-backed build and axiom audit test
that its assumed specification has a legitimate implementation.
**Rejected.** Nightly-only implementation checks; reporting only `sorryAx`; superficial
syntax bans as the entire protection against definition leaks.
**Acceptance.** AT-FD-2 and AT-FD-11, including deliberately invalid clients and axioms.
**Status.** frozen policy; implementation required at M-F and completed for M3.

### D-TL-18 · Performance
**Decision.** Benchmark the bundled seal on a nontrivial client. Adjust package granularity
if projections or dependencies are expensive, without weakening the specification.
Keep object construction explicit and existence classes Prop-valued. Validated finite
shape computation may remain transparent in Theory. Measure before adding elaborate
API generators or indexing services.
**Rationale.** Empty builds cannot detect performance failures through an actual interface.
**Rejected.** Performance fixes that silently expose sealed equations.
**Acceptance.** AT-FD-2 performance record and M3 regression measurements.
**Status.** provisional.

### D-TL-19 · Layout
**Decision.** Use Kernel/, Root/, Interface/, Interface-Stub/, Theory/, Prototype/,
Generated/, forest/, scripts/, and optional mcp/. `history/v0/` in this document bundle
is archival and excluded from active decision/test indexing. Prototype/ results are
promoted only with dependencies and validation made explicit.
**Rationale.** Experimental definitions should not accidentally become public foundations.
**Rejected.** Indexing superseded historical decisions as current agent tasks.
**Acceptance.** M0 registry and M-F dependency audit.
**Status.** provisional conventions.
