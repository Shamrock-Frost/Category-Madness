# 06 · Tooling

### D-TL-01 · "Agent-native" is undefined
**Decision.** The library does not define what agent-native artifacts or APIs look like.
Conventions in this document are `provisional` and are expected to be replaced by
whatever the agents converge on. Mechanism: every convention is a decision node with
status `provisional`; an agent may propose an amendment as a PR that (a) edits the node,
(b) applies the change mechanically across the codebase, (c) leaves the human layer to be
regenerated. Human review is of the *decision*, not the diff. Frozen decisions (the
charter, the root, the seal, the interface list) are out of scope for this mechanism.
**Rationale.** → D-CH-07. Pinning down agent-native conventions now would encode
2026 guesses about 2027 agents.
**Status.** frozen (the meta-rule), everything it governs `provisional`.

### D-TL-02 · The generated human layer
**Decision.** Generated, never hand-edited: notation (`X ⟶ Y`, `f ≫ g` diagrammatic,
`C ⥤ D`, `A ⇸ B`, `α ⇒ β`), binary `abbrev`s over unbiased primitives (`X ⨯[p] Y`
over `Product`, `f ≫ g` over `compN`), docstring-derived forest nodes (→ D-WF-01), and
any "pretty" API. Regeneration is a CI step; a hand edit to a generated file fails CI.
**Rationale.** → D-CH-07. The human layer is a view.
**Status.** provisional (mechanism frozen, contents provisional).

### D-TL-03 · `to_dual`
**Decision.** An attribute that, for a declaration about shapes/Segal categories/VDC∞s,
generates the dual declaration by `op` on shapes and on ambient Segal categories, with a
name translation table (`Limit ↔ Colimit`, `Terminal ↔ Initial`, `Ran ↔ Lan`,
`companion ↔ conjoint`, `restriction ↔ extension` where applicable) — modelled on
`to_additive`. No dual is ever written by hand (→ D-UP-05). Built at M0–M1 against the
shapes, extended at M4.
**Rationale.** The single highest-leverage tool Mathlib's category theory never had.
**Status.** frozen (existence), provisional (translation table).

### D-TL-04 · `witness_transport`
**Decision.** A tactic that, given a goal mentioning a witness `L : Limit F` (or any
`Terminal K`) and a second witness `L'`, rewrites along the canonical equivalence
`L ≃ L'` using the functoriality lemmas registered by the `@[witness_functorial]`
attribute (→ D-UP-06). Failure is loud: if no functoriality lemma is registered for a
construction, the tactic reports which one is missing.
**Status.** frozen (existence), provisional (interface).

### D-TL-05 · `extend`
**Decision.** A tactic/command for Kan extension along shape inclusions: given
`i : J → J'` between shapes and `F : N J → C`, produces the pointwise
extension statement (limits over slices `(j' ↓ i)`), discharges existence from
`HasLimitsOfShape` hypotheses, and names the witness. Specializations: `cosk_n`, `sk_n`,
Čech (→ D-UP-07). This replaces the coherence tactic of biased designs (→ D-CH-03).
**Status.** frozen (existence), provisional (interface).

### D-TL-09 · `paste`
**Decision.** A tactic for equality of pasting composites. Both sides are normalized to
`P(σ)(d)` — the diagram `d` restricted along a shape map `σ` — using functoriality of
`P` and the Segal/active-map lemmas; the goal reduces to `σ = σ'` in the transparent
hom-type of the shape category (→ D-TL-10), which is decided by `decide` on finite data
(for `Θ^aug_fc`, EZ normal forms: degeneracy part then sub-grid). For `Vert₂` the tactic
first rewrites 2-cell pastings through unit factorization (→ D-RT-15). This occupies the
slot the coherence tactic vacated (→ D-CH-03): coherence is shape-map equality.
**Status.** frozen (existence), provisional (interface).

### D-TL-10 · Shape formats
**Decision.** The format is the datatype: each shape category's objects and morphisms
are Lean inductives with `deriving DecidableEq, ToJson, FromJson`, exported transparently
(→ D-RT-13). Canonical forms: `Θ^aug_fc` as rows of block sizes with output flags
(`{"rows": [[2,0,3],[1,2],[2]]}`, augmented blocks `"out": false`; `pt`, `h`, `v^n`
separately), equivalently chains of active simplicial operators reusing Mathlib's
`SimplexCategory` morphisms; Δ as monotone `Fin` maps; Ω_p and Θ_n as nested lists; Ω
as a planar representative plus symmetry, with Kock's polynomial encoding as the honest
form; □ as words over faces, degeneracies, and connections. General shapes (anything
from the geometric substrate, → D-KR-12) use the oriented-graded-poset serialization of
`rewalt` (elements per dimension with input/output face lists), with the embedding of
each canonical form into it as a function and a theorem (AT-KR-12, AT-KR-13). ACSet JSON
(Catlab) is the interoperability form for presheaf data such as double graphs on `G_fc`,
never a canonical form (isomorphic ACSets are not equal). Forest nodes render grids as
Myers-style string diagrams (SVG) generated from the rows.
**Status.** frozen (the two-level scheme), provisional (encodings).

### D-TL-11 · Drawing and importing diagrams (not core)
**Decision.** An import pipeline, in increasing order of effort: (1) a text DSL for rows
and for the other canonical forms, parsed into the Lean inductives; (2) import from
`rewalt` (oriented graded posets), validated by the typing/leveling check of D-KR-12 and
normalized to rows when the shape is a VDC scheme, rejected with the failing composite
otherwise; (3) a minimal grid editor (rows of boxes, since VDC schemes are grids) that
emits the DSL; (4) ACSet import for presheaf data. Diagrams of cells *in* a given `P`
(points of `P(θ)`) are imported as the shape plus a labelling of its cells by names of
declared cells, producing a Lean term whose typechecking is the boundary check.
Rendering is the reverse direction and is the part the forest needs first.
**Rationale.** Cheap because the shapes are simple; not core because the library's
pasting proofs are generated, not drawn. A homotopy.io-style editor is out of scope.
**Status.** provisional; `later` beyond (1) and rendering.

### D-TL-06 · The seal linter and CI
**Decision.** CI jobs, all blocking:
1. **Import ban.** No file under `Theory/` imports `Mathlib.CategoryTheory.*`,
   `Mathlib.AlgebraicTopology.*`, `Kernel.*`, `Root.*`. `Mathlib.Tactic.*` and friends allowed.
2. **Unfolding ban.** In `Theory/`: no `unseal`, `with_unfolding_all`, `delta`,
   `unfold <sealed>`, `simp [<sealed>]`, `dsimp only [<sealed>]`, `rw [<x>_def]`,
   `show` that changes a sealed head symbol, `cast`/`▸`/`HEq` on sealed types, `decide`
   on sealed props (the transparent shape types of D-TL-10 are exempt), `rfl`/`Eq.refl`-closed goals whose sides differ syntactically at a
   sealed head. Implementation: a Lean linter over syntax plus an `Expr`-level check
   that no proof term in `Theory/` references a `_def` lemma or a kernel constant.
3. **Statement hygiene.** `Interface/` statements mention only interface constants.
4. **Swap test.** Build `Theory/` against `Interface-Stub/` (bodiless axioms with the
   same statements). Green means no leak; it is the operational content of → D-CH-12.
5. **Sorry accounting.** `collectAxioms` over every declaration; `sorryAx` is reported
   per node in the forest (→ D-WF-01) and blocks merges to `main` outside `wip/`.
6. **Universe test.** `Theory/` builds with `autoImplicit false` and no universe
   annotations beyond declared ones.
7. **Regeneration.** Generated human-layer files match their generators.
**Status.** frozen.

### D-TL-07 · Performance rules
**Decision.** Sealed constants are `opaque` or `irreducible` (→ D-RT-13), so elaboration
never unfolds them; instance search depth is capped and every class in the interface
is a `Prop`-class or a `structure` carried explicitly; `Space` data is never pattern-
matched in `Theory/`; large presheaf constructions in the kernel are `irreducible` with
`simp` equations; `Fin`-combinatorics stays in the kernel behind AT-KR-3 presentations.
Benchmarks are forest nodes updated in CI.
**Status.** provisional.

### D-TL-08 · Naming and layout (provisional)
**Decision.** `Kernel/`, `Root/`, `Interface/`, `Interface-Stub/`, `Theory/{UP, FT, SP,
…}`, `Generated/`, `forest/`, `scripts/`, `mcp/`. Declarations: `Structure.field_property`,
snake_case theorems, dot notation, no abbreviations in names, statement-shaped names
(`Limit.isTerminal_of_isTerminal`), theorems named for their conclusion. Subject to
→ D-TL-01.
**Status.** provisional.
