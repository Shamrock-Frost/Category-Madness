# 08 · Roadmap — revision 1

Milestones are evidence gates, not dates. M-F is new and sits between M0 and M1.
It pulls forward the pieces of shape, Kan, and categorical comparison machinery needed
to test the root. Later milestones package and generalize those pieces; they are not
prerequisites that have been scheduled after their clients.

### Phase −1 · Revised design

Deliverable: this revision with the original snapshot and supersession crosswalk.
Exit: the design has explicit candidates, falsification tests, and an authorized plan.
This is not mathematical validation of the repaired ∞-root.

### M0 · Minimal skeleton

Pin Lean/Mathlib and inventory AT-KR-0. Create the repository/Prototype layout, minimal
registry, test statuses, and CI scaffolding. Round-trip one stated WIP theorem through
the minimal exporter. A full retrieval MCP and broad API generators are not exit gates.
Freeze workflow/trust policies, not the conjectural mathematical foundation.

**Exit:** AT-KR-0 verified and the minimal registry/toolchain operates.

### M-F · Foundation feasibility (new; after M0, before M1)

See `11-foundation-feasibility.md` for the exact tests and dependencies.

- Compile the universe signatures and demonstrate a real bundled seal and swap.
- Repair object reduction and prove the boundary/Segal-core comparison actually used.
- Establish categorical diagram spaces on ordinary-category examples with natural
  equivalences, separately from relative presheaf maps.
- Test and prove the required discrete/general equivalence clauses, including duplicate
  horizontals, endpoint transport, and 2-out-of-3 in the proposed root setting.
- Eliminate the unsupported truncation from required interfaces; demonstrate boundary
  monodromy and a coherent-cell route that retains the needed information.
- Establish the augmented arities and the actual cofibrancy/replacement machinery used
  by the prototype; prove the no-horizontal 2-category comparison.
- Construct relative monads/modules and one small nondiscrete matrix/Mod example,
  including whole-object fibres and the natural-equivalence extraction.
- Check the corrected symmetry ambient on a discrete action example; scope pasting and
  rectification accurately; pass the compiled-dependency and axiom audits.

**Exit:** AT-FD-1 through AT-FD-11 passed: mathematical components have checked proofs
of their current statements with approved axioms, and tooling components have reproducible
check records. No blocked prerequisite is hidden behind a later milestone. A gate
may be revised only with a decision explaining the change and its impact. Failed gates
keep the dependent foundation provisional. There is no “all gates passed” status in
this document revision: the tests are currently proposed.

**Freeze:** only the successfully validated minimal presentation/API fragment. Full
root and interface freeze remains M3, with the required M-F results as prerequisites.

### M1 · Generalize the validated shape work

Package the arity and nerve results into the general reusable theory (AT-KR-1/2/5/8/9),
complete the root presentations needed by the public interface, and implement validated
shape syntax/rendering. Add a shape family only when a scheduled client needs it.
Expand the forest exporter and retrieval against the now nonempty environment.

**Exit:** the named shape/arity/core tests required for M3 are proved. Ω, Θ_n, cubes,
and geometric presentations have their own later exits and do not block this one.
**Freeze:** those adopted shapes and formats whose presentation proofs have passed.

### M2 · Package the needed homotopy machinery

Generalize M-F's Kan, diagram, reduced replacement, and relative-mapping lemmas into the
exportable Space/diagram API (AT-KR-10/11). Complete categorical `MapCat`/`Fun` bootstrap
bridges needed by M3/M4. Do not assume the category of all VDCs has an already-proved
localization model merely because Segal categories do.

**Exit:** all hypotheses of the M3 constructions are supplied by checked lemmas.
**Freeze:** the proved Space and diagram primitives, not future construction promises.

### M3 · Full root and seal

Complete the repaired root, relative walking structures and `Mod`, the matrix/discrete
category path, and vertical 2-cell/categorical-core extraction. Prove AT-RT-1/2/3/5/6/7/
10/11/12 in their revised scopes. AT-RT-4 is retired. Complete the specific closure and
invariance theorems of each export. Run both builds, axiom audit, nontrivial client,
performance checks, and thin API generation. Discrete `paste` is usable.

**Exit:** the full exported specification has an implementation and passes the swap test.
**Freeze:** that root/signature and its proved comparisons. General `hP`, arbitrary
fixed-target rectification, and unvalidated shapes are absent from the frozen interface.

### M4 · Universal properties

Construct categorical diagrams, derived cone/comma categories, limits, witness
transport, and shape extensions. Prove AT-UP-1 through AT-UP-8, including the corrected
`sk_n ⊣ cosk_n` orientation and the Čech diagram's coherence. Add slice/functor/limit
closure certificates with their implementations, not as earlier axioms.

**Exit:** all eight tests, duality scope, and nontrivial witness/extension clients pass.
**Freeze:** the validated universal-property definitions and API.

### M5 · Coherent formal theory

State and prove the required restriction/unit and formal-theory comparisons. Develop
coherently in the root, using discrete comparisons early; optional homotopy-equipment
routes require their own established bridge. Prove AT-FT-1/2/3/5/6/7. AT-FT-8's former
general claim is retired. Construct the span recipe with its actual indexing and
relative boundaries as far as its dependencies permit; AT-SP-4 must pass before export.
AT-FT-4's full double-∞ comparison may follow at M6 if necessary.

**Exit:** every exported formal theorem has the stated hypotheses and its discrete test.
**Freeze:** the proved equipment/units definitions and formal theorem signatures.

### M6 · Full spaces and enrichment

Build the classifier and the full `Kan`, `Mat(Kan)`, `InfCategory`, `Cat_∞`, and span
instances. Prove size-bounded limits and colimits of spaces (AT-SP-12), full matrix
comparison (AT-RT-8, AT-SP-2/3), required rigidification (AT-SP-8), and construction
closure. Establish AT-SP-1/4 and the corresponding presheaf/coend clients. Operadic
nerves are introduced when their corrected algebra construction is ready.
The full span-module comparison AT-SP-5(b), double comparison AT-FT-4, and style-A
comparison AT-RT-9 may require separate research submilestones; the narrower mandatory
M-F categorical tests were not postponed to these comparisons.

**Exit:** the full root monad model agrees with the bootstrap Segal-category interface,
the formal theory applies, and the claimed presheaf category is cocomplete at stated sizes.
**Freeze:** the validated full spaces/enrichment interface.

### M7 · Extensions

The symmetry/braiding monads on the corrected profunctor ambient, the ∞-Kleisli theorem,
symmetric sequences and operads (AT-SP-9/10/13), precisely scoped E_n examples (AT-SP-11),
general monoidal enrichment, cosmoi, additional shapes and geometric substrate, and a
self-hosted kernel. Symmetric monoidal ∞-category examples include their actual
`Cat_∞` colimit prerequisites. Each extension has its own statement and comparison gate.

## Risk register

| Risk | Consequence | Evidence required / response |
|---|---|---|
| Augmented arities do not have the proposed presentation | Root construction changes | AT-FD-7; revise the algebraic/shape model before freezing formats |
| Required diagram model unavailable | Relative maps and Mod blocked | Prove an actual model/cofibrant-source alternative; generalized Reedy is not automatic |
| `VDCEq` clauses fail | Invariance and comparison claims blocked | AT-FD-5 counterexample and revised clauses; no frozen false predicate |
| Relative and categorical maps confused | Natural equivalences disappear | AT-FD-4; distinct names and clients |
| Boundary gluing fails | Cell fibres/Segal semantics wrong | AT-FD-3; use proved reduction/fibrancy or homotopy limits |
| Boundary monodromy | General hP shortcut invalid | AT-FD-6; coherent-cell route, optional scoped truncation |
| Mod fibres or coherence fail | Shared category/operad construction blocked | AT-FD-8; revise walking diagrams or the root model |
| Fixed-target rectification overstated | Construction interface unsound | AT-FD-10; state allowed replacements and exact domains |
| Classifier or spaces colimits stall | Full enrichment delayed | AT-SP-1/12; small nondiscrete evidence already required at M-F |
| Seal/performance fails | Implementation abstraction unusable | AT-FD-2; adjust specification packaging before broad clients |
| Unapproved axiom enters implementation | Acceptance status invalid | AT-FD-11; allowlist and same-revision kernel-backed build |
| Extra infrastructure dominates | Foundation remains untested | Additional shapes, geometric substrate, and large retrieval deferred |
