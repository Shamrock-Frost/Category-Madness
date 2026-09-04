# 08 · Roadmap

Milestones are defined by what gets **frozen** and which **acceptance tests** must be
`proved`. Order within a milestone is dependency order; agents choose. Dates are not
part of this document.

### Phase −1 · These documents
Deliverable: this tarball. Exit: human sign-off on the outline and the frozen decisions.

### M0 · Skeleton
- Repo layout (→ D-TL-08); Mathlib pinned; CI with the import ban and swap-test
  scaffolding (→ D-TL-06) running against empty directories.
- Forest skeleton, port of these documents (→ 07 porting instructions), `forest-export`,
  retrieval MCP MVP (→ D-WF-05).
- Mathlib inventory node (AT-KR-0).
- `to_dual` skeleton (→ D-TL-03).
**Freeze.** Charter (all D-CH), D-KR-01/02, D-WF-01…06, D-TL-06.
**Exit.** AT-KR-0 verified; a `sorry`-only Lean file round-trips through export, forest, MCP.

### M1 · Shapes and patterns
- BMW "monads with arities" and the general nerve theorem (AT-KR-2).
- Δ ≅ `SimplexCategory` (AT-KR-1); Δ₊ and joins; `Δ_X` (AT-KR-9).
- `G_fc`, set-level augmented VDCs, free augmented VDCs, `Θ^aug_fc`, `Θ_{fc,X}`
  (D-KR-06/07), explicit presentation (AT-KR-3), nerve theorem instance (AT-KR-8).
- Ω_p, Ω (D-KR-03; OQ-KR-1 resolved), Δ×Δ, Θ_n (AT-KR-4), □ (D-KR-09).
- Pattern structures and Segal cores (D-KR-04, AT-KR-5).
- Reedy/elegance/EZ (D-KR-05, AT-KR-6, AT-KR-7).
**Freeze.** Shape definitions and their pattern structures; the shape part of the interface list.
**Exit.** AT-KR-1…9 proved.

### M2 · Kan machinery
- Everything in D-KR-10 (AT-KR-10), Reedy fibrancy for `sSet`-presheaves on the shapes,
  homotopy fibre products, mapping spaces, exponential/pushout-product lemmas.
- Fibrant replacement for Segal presheaves on elegant shapes (D-KR-11, AT-KR-11).
**Freeze.** The `Space` API of the interface.
**Exit.** AT-KR-10, AT-KR-11 proved.

### M3 · The root and the seal
- D-RT-01…12 stated and proved: VDC∞, maps, `Vert`/`Hor`, `hP`, DK-equivalence,
  fibrancy, `Map`, walking structures, `Mod`, `Mat(Set)`, `Category`, `Cat`, discrete embedding.
- AT-RT-1 (self-hosting), AT-RT-2…7, AT-RT-10, AT-RT-11 proved.
- The closure and rectification package of D-RT-13 for the M3 objects: `Mod` preserves
  fibrancy, slices and functor objects preserve fibrancy, DK-invariance of `Mod`/`Vert`/
  `Hor`/`hP`, rectification for discrete targets (trivial) with the general statement
  stated for M6.
- `Interface/` v1 written (D-RT-13), `Interface-Stub/` generated, swap test green,
  thin API generator (D-RT-14) running, human notation layer generated (D-TL-02).
**Freeze.** The root definition, DK-equivalence clauses, the interface list v1, the
two-tier extension policy.
**Exit.** Hard seal on. From here `Kernel/` and `Root/` are invisible.

### M4 · Universal properties
- D-UP-01…09; `witness_transport` (D-TL-04) and `extend` (D-TL-05) usable.
- AT-UP-1…7 proved, including the Čech nerve (AT-UP-6).
**Freeze.** `IsTerminal`, slices, `Limit`, Kan extensions, witness discipline.
**Exit.** AT-UP-1…7 proved; `to_dual` produces all colimit-side statements.

### M5 · Formal theory
- D-FT-01…04 stated; D-FT-03 items proved first in `hP`, then coherently (OQ-FT-2).
- `Span(S)` for Segal categories with finite limits (D-SP-05 statement, AT-SP-4).
- AT-FT-1…3, 5…8 proved; AT-FT-4 stated.
**Freeze.** Augmented virtual ∞-equipment definition; the theorem list D-FT-03.
**Exit.** The formal theory instantiates to classical statements in `Cat` with no
separate proofs.

### M6 · Spaces and enrichment
- D-SP-01…06: `U`, `Kan` (fibrant, OQ-SP-3 resolved), `Mat(Kan)` (fibrant),
  `InfCategory`, `Cat_∞`, `Span(Kan)` via `Tw` shapes, ∞-operads.
- Rectification (AT-SP-8) and the closure package for `Mat(Kan)`, `Span`, limits.
- **The mountain**: `HasColimits Kan` and `HasLimits Kan` (AT-SP-12), Simpson's route.
- AT-SP-1…4, 6, 7, 8, 12 and AT-RT-8 proved; AT-SP-5 and AT-FT-4 attempted.
**Freeze.** `Kan`, `Mat(Kan)`, `InfCategory`, `Span`.
**Exit.** An ∞-category is a monad in `Mat(Kan)`, the formal theory applies to it with
no new definitions, and `PSh(C)` is cocomplete.

### M7 · Later
- Self-hosted kernel and the axiom build variant (D-CH-12).
- The strict monads `T_ℕ`, `T_𝔹`, `T_Σ` (and `T_G` for action operads) on `Mat(Kan)`;
  the horizontal Kleisli construction `H-Kl(T, X)` and Cruttwell–Shulman's equipment
  theorem at ∞ (AT-SP-13); planar/braided/symmetric ∞-operads as monads in the
  Kleisli VDC∞s; symmetric sequences as the one-object case; `E_1`, `E_2`, `E_∞` as
  contractible monads (D-SP-09, AT-SP-9…11); `E_n` for finite `n ≥ 3` via Berger's
  complete-graph operads; symmetric monoidal ∞-categories as `E_∞`-algebras in `Cat_∞`.
- Comparisons of D-SP-08 (Bergner, Joyal–Tierney, HHM, style A).
- Cosmoi (D-FT-05, AT-FT-9); general E1 enrichment (D-SP-07); Θ_n and (∞,n); test
  categories; categorical logic proper (comprehension categories/CwFs built on the
  fibration layer, with `U` as the universe object).

## Risk register

| Risk | Impact | Mitigation |
|---|---|---|
| `Θ^aug_fc` not elegant (AT-KR-6 fails) | Reedy cofibrancy of all objects lost; derived maps need cofibrant replacement | Fall back to generalized Reedy + normal objects, as for Ω; `Map` restricted to normal sources |
| Fibrant replacement theorem (AT-KR-11) harder than Bergner's | Blocks `Map`, `Mod`, all of M3 | Prove for `Δ_X` first (literature), then extend; interim: define `Map` only for fibrant targets |
| DK-equivalence clauses wrong (AT-RT-5 or style-A comparison fails) | Homotopy theory of VDC∞s wrong | Clauses are provisional until AT-RT-5; style-A comparison at M6+ is the external check |
| Boundary fibrancy (2) fails for a needed example | Definition too strict | OQ-RT-1 fallback: path-space homotopy limits |
| Augmentation axioms transcribed wrongly (D-FT-01) | Formal theory diverges from Koudenburg | AT-FT-1 is exactly this check; do it before D-FT-03 |
| Elaboration performance through three instance layers | Unusable API | D-RT-14 thin API; D-TL-07; benchmarks as nodes |
| Mathlib bump breaks kernel | Blocks everything until M7 | Pin; inventory node per bump; after M3 only `Kernel/` is affected |
| Agents redefine instead of retrieving | Definition drift | Retrieval MCP (D-WF-05); PR must cite decisions |
| `HasColimits Kan` (AT-SP-12) stalls | No `PSh`, no coends, no composites, no `SymSeq` | It is scheduled by name; Simpson's route is Segal-native; fallback is the Joyal–Tierney comparison and HTT 4.2.4.1 through Cisinski's `S` |
| Rectification (AT-SP-8) missing | Fibrant world cannot be populated by hand | Dwyer–Kan/Bergner is literature; interim: work only with standard objects exported fibrant |
| Closure package (D-CH-13) incomplete at the seal | `Theory/` cannot prove fibrancy of its own constructions | Two-tier extension policy (D-RT-13): lemmas are agent-proposable |
| `Vert` used where cells are needed | Lax notions silently wrong | D-UP-09 as amended; AT-UP-8 |
