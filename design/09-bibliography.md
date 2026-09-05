# 09 · Bibliography and proof routes — revision 1

These references supply definitions and comparison routes. A source about ordinary
VDCs, Segal categories, or a different model does not prove the corresponding theorem
for the candidate augmented ∞-root. The full original annotated bibliography is
preserved in `history/v0/09-bibliography.md`; the active routes and their limits follow.

| Primary source | What is used | Boundary of the claim |
|---|---|---|
| Koudenburg, [Augmented virtual double categories](https://arxiv.org/pdf/1910.11189), published TAC 2020; arXiv v4 includes later corrections | Exact discrete augmentation, restrictions, units, vertical cells, and equivalence comparison for D-KR-18, D-RT-21, D-FT-06 | The augmented ∞-arity/model construction is new work. Pin the version used when transcribing axioms. |
| Cruttwell–Shulman, [A unified framework for generalized multicategories](https://arxiv.org/pdf/0907.2460) | Discrete Mod/Kleisli definitions and scoped preservation results | Examples 3.12–3.14 distinguish list monads on matrices from symmetric/braided monoidal category monads on profunctors. No ∞-preservation theorem is inferred by changing the word “category.” |
| Berger–Melliès–Weber, [Monads with arities and their associated theories](https://arxiv.org/pdf/1101.3064) | General nerve recognition; separately, canonical arity results under stronger hypotheses | D-KR-15/04 record actual hypotheses for arities, generic factorization, and the chosen elementary cores. Reedy structure is additional. |
| Bergner, [Complete Segal spaces arising from simplicial categories](https://arxiv.org/html/0704.1624v2) | Distinguish strict/relative diagram maps from categorical presentations; ordinary-category comparisons in AT-FD-4 | Reedy replacement and categorical completion have different roles. This is not a construction of the candidate VDC∞ localization. |
| Lean, [Definitions reference](https://lean-lang.org/doc/reference/latest/Definitions/Definitions/) | Opaque declarations and specification packaging for D-RT-28 | Prototype against the pinned Lean version. An opaque body alone does not export implementation-specific laws. |
| Lean, [Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/) | Dependency and axiom inspection for D-TL-17 | A stub build checks clients under assumptions; the matching implementation and axiom audit are still required. |

## Additional named routes to pin when activated

- **Bergner**, *A model category structure on the category of simplicial categories*;
  *Three models for the homotopy theory of homotopy theories*. Select the exact framing,
  localization, and rigidification statements for AT-FD-4 and AT-SP-8. “Strict models
  exist up to equivalence” is distinct from maps into an arbitrary fixed strict target.
- **Rezk**, *A model for the homotopy theory of homotopy theory*. Completion and
  categorical functor objects. The necessary restricted results belong at M-F if used.
- **Dwyer–Kan**, simplicial localization and function-complex papers. Mapping-space
  tools; do not attribute all later Segal-category rigidification claims to the 1980 papers.
- **Chu–Haugseng**, *Homotopy-coherent algebra via Segal conditions*. Algebraic patterns
  and coherent recognition. Prove the candidate root satisfies the selected hypotheses.
- **Gepner–Haugseng**, *Enriched ∞-categories via non-symmetric ∞-operads*. The full
  categorical-algebra comparison target for AT-SP-3; specify the actual bridge of models.
- **Koudenburg**, *Formal category theory in augmented virtual double categories*,
  TAC 41 (2024). Discrete formal-theory statements and their hypotheses for AT-FT-1.
- **Riehl–Verity**, *Elements of ∞-Category Theory* and their module-calculus work.
  Optional specific homotopy-equipment comparisons, not a universal truncation formula.
- **Ruit**, *Formal category theory in ∞-equipments I, II*. Precise double-∞ comparison
  to be selected for AT-FT-4, including completion and model hypotheses.
- **Barwick / Haugseng**, span and iterated-span constructions. Sources for the
  proposed `Tw` route, with variance and augmented virtual adaptation proved separately.
- **Kapulkin–Lumsdaine / Cisinski / Sattler**, universe and fibration constructions.
  Select the exact classifier and path-to-equivalence theorem used at M6.
- **Simpson / Hirschhorn**, Segal-category and homotopy-(co)limit machinery. Name the
  result converting each derived (co)limit to the categorical universal property.
- **Haugseng**, *∞-operads via symmetric sequences*. Comparison after the corrected
  action-indexed collection and substitution constructions have been established.
- **Moerdijk–Weiss / Cisinski–Moerdijk**, operadic nerves and dendroidal Segal models.
  Pin the colour-reduction/completeness and equivariant model conventions when Ω is used.
- **Hadzihasanovic**, geometric diagram/pasting work; **Power / Dawson–Paré**, classical
  pasting comparisons. Optional presentations after the algebraic root is validated.
- **Sterling**, forester v5. Pin and test the actual format before the documentation port.

The cited mathematical definitions inform the revised proposals, but no citation is
recorded as a checked Lean acceptance proof. Each port records source version, theorem
number, assumptions, and any gap between the source and the library's claim.
