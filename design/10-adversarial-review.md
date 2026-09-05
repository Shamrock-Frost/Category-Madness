# 10 · Adversarial review and current disposition — revision 1

The original review and dispositions remain verbatim in `history/v0/10-adversarial-review.md`.
This revision responds to the subsequent twelve-finding design review. A disposition
below records a design change, not a proved Lean theorem. Required evidence is in M-F.

| Finding | Current design response | Remaining evidence |
|---|---|---|
| R1: horizontal bijectivity in DK clauses | Remove that condition; require fixed-boundary cell faithfulness and simultaneous essential surjectivity | AT-FD-5; ∞-predicate and comparisons remain provisional |
| R2: relative maps lose natural equivalences | Separate `MapRel`/`MapCat` and `VertRaw`/`VertCore`; retain vertical 2-cells | AT-FD-4 and AT-FD-8 |
| R3: boundary monodromy invalidates hP | Remove generic hP and its mandatory proof route; work coherently | AT-FD-6; optional specific truncations later |
| R4: contractible object values | Require a reduced presentation and prove actual boundary/core lemmas | AT-FD-3 |
| R5: Mat universes | Raise collection universes; keep category object/hom parameters separate | AT-FD-1, no signatures compiled in this revision |
| R6: walking/slice fibres omit structure labels | Fix entire selected monads/cones through relative diagram fibres | AT-FD-8, full AT-UP-3 |
| R7: augmented active-chain encoding | Replace the universal active-chain assertion with explicit augmented algebra/arity work | AT-FD-7, a material research risk |
| R8: BMW hypotheses conflated | Separate arity recognition, pattern, and Reedy theorems | AT-FD-7 and AT-KR-2 |
| R9: symmetric/braided monads on Mat | Move to the profunctor ambient and retain permutation/braid morphisms | AT-FD-9; full ∞-construction M7 |
| R10: independently opaque data and laws | Bundle the specification with its laws, or prove an audited alternative | AT-FD-2 |
| R11: broad rectification and paste promises | State model changes and fixed-target scope separately; distinguish equality from coherent comparisons | AT-FD-10 |
| R12: freeze before decisive tests | Add M-F; move speculative infrastructure later; audit all axioms and both builds before merge | AT-FD-11 and M-F exit |

The review's R3 claim is intentionally addressed conservatively: the faulty canonical
transport argument is removed, without claiming that no useful homotopy equipment can
exist. R4 identifies an invalid gluing justification; the proposed reduced replacement
still needs a proof. R7 rejects a complete encoding by ordinary active chains; flagged
augmented rows remain a possible richer presentation if their theorem is established.
R10 does not say opaque interfaces are impossible: the revision uses data and laws in
one specification, which is the appropriate prototype to test.

Earlier review findings about usable APIs, size, coherent choices, limits/colimits,
span diagrams, invariance, duality, and interface growth remain relevant. Their prior
“disposed” labels do not mean that the necessary ∞-theorems were proved. The current
charter requires construction-specific certificates and treats failed gates as reasons
to revise the mathematics.
