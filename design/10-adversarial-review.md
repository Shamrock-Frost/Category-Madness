# 10 · Adversarial review (phase −1) and disposition

A record of the adversarial pass on the VDC∞ design and what changed because of it.
Kept because the *rejected framings* are the part agents will otherwise re-derive.
Each item: what the library will want, why the design as first drafted made it hard,
disposition.

## Reframing that governs the whole list
The first draft of item 1 said an ∞-category modelled as a point of
`Map(N Mnd, R(Mat Kan))` was "uncomputable". That conflated *cannot unfold* (true and
intended, → D-CH-01) with *cannot work with* (false if the interface is right). Nobody
writes down a simplex of `Fun(Δ[n], N(Kan))` either; quasi-category theory is usable
because its interface — horn filling, `Fun`, joins, mapping spaces — is closed under the
constructions it uses, and rectification theorems populate it from strict models. The
corrected criterion is → D-CH-13: fibrancy exported as a property, closure theorems for
every exported construction, rectification. Items below are read through that lens.

## Items

1. **Usable ∞-categories.** Want: to write down and compute with an ∞-category through
   its interface. Cost: closure and rectification theorems, not a design change.
   Disposition: D-CH-13 (new); D-RT-07 and D-RT-13 amended (fibrancy exported, closure
   package in Interface v1, two-tier extension); D-SP-02/04 amended (fibrant `Kan`,
   `Mat(Kan)`; rectification AT-SP-8; construction route is OQ-SP-3).
2. **The 2-category `Cat`.** Want: natural transformations, lax notions. Problem: `Vert`
   restricts to vertical paths and forgets cells. Disposition: D-UP-09 rewritten;
   (∞,1)-universal properties in `Vert` scoped to products/exponentials/cotensors; lax
   notions go to the equipment; AT-UP-8.
3. **Large objects, small homs.** Want: `Set`, `Kan`, `Cat` as objects. Problem: single
   universe at the root. Disposition: D-RT-12 rewritten; label and value universes
   independent; `Category.{u,v}`.
4. **Coherent lifts.** Want: lifts along diagrams, functorial `cosk₀`. Problem: pointwise
   contractibility gives points, not sections. Disposition: D-UP-01 and D-UP-06 amended;
   trivial-fibration form; `Classical.choose` on sections.
5. **Colimits in `Kan`.** Want: `PSh(C)` cocomplete, coends, composites, `SymSeq`.
   Problem: unscheduled mountain. Disposition: D-SP-08 names it (AT-SP-12), Simpson's
   route, M6, risk register.
6. **`Span(S)`.** Want: internal categories, Segal spaces. Problem: compatible choices of
   pullbacks. Disposition: D-SP-05 rewritten via `Tw(θ)` shapes (Barwick, Haugseng);
   D-KR-08 amended.
7. **Invariance.** Want: DK-invariance of every construction. Problem: nothing invariant
   by construction in a strict-model design. Disposition: folded into D-CH-13 (b); every
   exported construction ships an invariance theorem; a constraint on definitions in 02–05.
8. **Duality.** Want: `to_dual` everywhere. Problem: vertical op broken by augmentation,
   transpose unavailable for virtual, `Cᵒᵖᵒᵖ ≃ C` never `rfl`. Disposition: D-UP-05
   scoped; hand-proved duals recorded by the attribute rather than generated.
9. **Interface growth.** Want: kernel facts as API after M3. Problem: every lemma a
   decision makes the human the bottleneck. Disposition: two-tier extension policy in
   D-RT-13; closure package in D-KR-10.
10. **Symmetric structures.** Want: symmetric operads, `E_n`, symmetric monoidal
    ∞-categories. First-draft problem: "E1-only excludes them." Corrected: symmetric
    operads are monoids in symmetric sequences under the (non-symmetric) composition
    product, an E1 notion; `E_1`/`E_2`/`E_∞` are the contractible monoids in
    non-symmetric/braided/symmetric sequences; `E_n` (`3 ≤ n < ∞`) via Berger's
    complete-graph operads. What is *not* viable: `E_n` (`n ≥ 2`) as non-symmetric
    operads — forgetting equivariance turns `E_∞` into `E_1` and `E_2` into `E_1` plus
    pure-braid actions; the braiding is the equivariance. Disposition: D-SP-09 (new);
    D-CH-05 note; M7.
11. **Augmentation at ∞.** Want: Koudenburg's formal theory at ∞. Problem: nullary-target
    cells have no output face; elegance and Segal cores of `Θ^aug_fc` are new. Disposition:
    unchanged (already AT-KR-6 with generalized-Reedy fallback in the risk register).
12. **Inverting DK-equivalences.** Want: canonical inverses. Problem: discrete object sets,
    Bergner's cylinder nontrivial. Disposition: an interface theorem once fibrancy is
    exported (D-CH-13); AT-RT-5 extended at M6.
13. **Strict layer.** Want: strict ω-categories, computads. Problem: nothing strict past
    the seal. Disposition: recorded as a non-goal in the charter.

## What could still sink it
Items 1 and 5. Item 1 is now a checklist (the closure and rectification theorems of
D-RT-13 and D-CH-13) that can be verified at M3 and M6. Item 5 is a scheduled theorem
with a named route and a fallback.
