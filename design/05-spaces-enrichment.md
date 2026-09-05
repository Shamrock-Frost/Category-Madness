# 05 · Spaces and enrichment — revision 1

A small nondiscrete matrix example is required at M-F. The full universe of spaces,
all needed limits/colimits, and general enrichment are M6 work. These are comparison
and construction targets, not results established by revising the prose.

### D-SP-10 · A classifier and its universal family
**Decision.** A proposed `U.{v}` classifies small Kan complexes with a universal family
`Ũ → U`; its simplex sets occupy a larger universe than its small fibres. Give a
normalization/size construction and prove its Kan and classification properties.
If paths in U are used to encode equivalences of represented spaces, prove the exact
path-to-equivalence comparison required; it is not supplied by Kan fibrancy alone.
Path spaces of U represent equivalences under that comparison, not arbitrary maps.
The family of maps between fibres is built separately from the universal family and
must have the required boundary fibration theorem.
**Rationale.** A classifier is useful but not needed to begin with a small explicit
space-enriched example, and its paths must have the advertised meaning.
**Rejected.** Inferring all matrix boundary fibrancy from `U^Δ[1] → U×U` alone;
assuming a small collection of all small objects without a universe increase.
**Acceptance.** AT-SP-1: classifier, universality, size, Kan properties, and the exact
equivalence comparison used by Mat; AT-FD-1 for signatures, AT-FD-8 for a small model.
**Status.** provisional construction route; full proof M6.

### D-SP-11 · The category of spaces
**Decision.** Start with the strict simplicial category of small Kan complexes whose
mapping objects are `L^K`. Construct its categorical Segal/complete presentation using
the proved framing/comparison of D-RT-23. Export `Kan` with maps equivalent to `L^K`,
compatible composition, and the actual fibrancy certificates. A second universe-family
implementation may be compared later. Distinguish Reedy replacement of a presentation
from categorical completion. Identify this bootstrap `Kan` with the root monad form
through AT-SP-2/3, rather than defining it circularly using itself.
**Rationale.** This gives a named construction route and a separately proved self-hosting bridge.
**Rejected.** Declaring a Kan object classifier already to be the category of spaces;
using paths between its points as all maps.
**Acceptance.** AT-SP-2: the root representation and classical homotopy category;
AT-FD-4 and AT-FD-8 for the early categorical comparison.
**Status.** provisional; small test early, full category M6.

### D-SP-12 · Initial enrichment scope
**Decision.** Start with cartesian Set and Kan; matrix multicells use products and maps.
General monoidal enrichment is later. Theories are exported only with universe bounds,
existence hypotheses, and the appropriate comparison proofs.
**Rationale.** The matrix examples test the central reuse claim with limited extra structure.
**Rejected.** Requiring every monoidal base before testing the root.
**Acceptance.** AT-RT-2, AT-FD-8, AT-RT-8.
**Status.** frozen initial scope.

### D-SP-13 · `Mat(Kan)` and categorical algebras
**Decision.** For labels all `A : Type u` and small entries at level v, construct a
matrix root with vertical arrows functions and horizontal space at `(A,B)` modeled by
families `A×B → U.{v}`. Its collection universes follow D-RT-27. A fibre of a cell
boundary map is the space of families of maps from the product of input fibres to
the output fibre. Empty targets use the equality matrix as in the discrete test.
Build this as one coherent presheaf with the corrected augmented arities; prove the
boundary fibration, Segal, and required replacement results. Elementary-value formulas
are comparisons, not a substitute for presheaf functoriality.
`InfCategory A := Monad (Mat Kan) A`, and `Cat_∞ := Mod(Mat Kan)`, after the coherent
construction is proved. AT-SP-3 identifies this with the bootstrap Segal-category
presentation on object set A. `VertCore(Cat_∞)` is the intended (∞,1)-category of
∞-categories, functors, and natural equivalences; `Vert₂` retains transformations.
`VertRaw` is not used as that categorical ambient.
**Rationale.** Correct relative monads and categorical extraction are both necessary.
**Rejected.** Recovering natural equivalences between different object functions by
ordinary fixed-label simplicial homotopy alone.
**Acceptance.** AT-RT-8; AT-SP-3; AT-FD-8's small end-to-end example. AT-SP-8 is the
specified rigidification theorem to an equivalent strict simplicial category, allowing
the model to change. Any surjectivity theorem for strict maps into a fixed target is
separate and is not promised generally.
**Status.** provisional research construction; M6 full proof after M-F feasibility.

### D-SP-14 · Spans and category objects in spaces
**Decision.** For S with specified finite-limit existence, construct `Span(S)` from a
functorial twisted-arrow-type diagram recipe with designated pullback conditions.
State the variance of `Tw`, label objects and whole boundary spans explicitly, and
prove preservation of designated squares under each shape map. Values are relative
diagram spaces over their labelled data, not unrestricted spaces of all diagrams.
If direct restrictions do not preserve the condition, supply the necessary Kan
extension construction with coherence. Prove fibrancy where needed and invariance
under the chosen categorical equivalences. Category objects in spaces arise as monads;
their complete presentation is a further construction.
**Rationale.** The span construction is a plausible shape-based approach, but its
virtual/augmented version needs an actual construction and proof.
**Rejected.** Arbitrary pullback choices at individual shapes; direct identification of
all Segal spaces with complete Segal spaces; inheriting a VDC comparison solely from
a comparison of categories of category objects.
**Acceptance.** AT-SP-4: span root and its cell/boundary formulas. AT-SP-5 is split into
(a) the known-model categorical comparison after appropriate localization and
(b) a full augmented-VDC equivalence with modules and cells, which is a stronger,
separately proved target.
**Status.** provisional; construct at M5/M6, full comparison later if necessary.

### D-SP-15 · Operadic nerve comparisons
**Decision.** Planar and symmetric Segal-operadic presentations are comparison models
in Root/ until connected to the root algebra construction. Specify reduced colour
values or the required completeness/localization, homotopy Segal limits, and the
actual equivariant/cofibrancy conventions for Ω. Their discrete nerves recover the
ordinary operads. These are not imposed as a second permanent public definition.
**Rationale.** A meaningful comparison includes morphisms and equivalences as well as objects.
**Rejected.** Unqualified strict Segal limits for arbitrary space-valued Ω-presheaves.
**Acceptance.** AT-SP-6 for discrete nerves; AT-SP-7 for planar root algebras;
AT-SP-10 for the full symmetric comparison when proved.
**Status.** later than M-F; staged with the relevant operad construction.

### D-SP-18 · Symmetry on a profunctor ambient
**Decision.** The free list/monoid construction may begin on `Mat(V)`. For the free
symmetric and braided monoidal category constructions use the profunctor ambient
`Prof(V) := Mod(Mat V)` once its coherent construction has been established.
For discrete colour categories A, `T_Σ A` is a category with finite lists as objects
and permutations as morphisms; `T_𝔹 A` retains braids. These are not objects of the
set-labelled matrix ambient merely by taking their sets of objects.

Implement the horizontal Kleisli construction with the variance conventions of the
chosen profunctors stated explicitly. In the Cruttwell–Shulman convention its
horizontals are X-horizontals `A ⇸ T B`; translate that convention through the matrix
bridge rather than silently changing input/output variance. Define unit, multiplication,
and cells coherently in the ∞-case; a strict model is allowed with a proved comparison.
The conditions under which `H-Kl` and its `Mod` have the required restrictions, units,
or composites are individual theorem hypotheses.

The one-colour collection category must recover functors from the finite-set groupoid
with the appropriate variance, hence `Σ_n`-actions in arity n. The braided case recovers
braid actions. Prove the substitution product, then the algebra/operad comparison.
Do not assert a general Kleisli composite theorem without the necessary colimits and
preservation hypotheses. There are virtual-equipment results that do not imply all
horizontal composites exist.

`E_1`, `E_2`, and `E_∞` examples and finite-n configuration-space models are later
comparisons with stated equivariance/freeness hypotheses. Symmetric monoidal
∞-categories as algebras in `Cat_∞` additionally need the relevant colimits there;
`HasColimits Kan` alone is not that theorem.
**Rationale.** An action needs morphisms in its indexing category, not just labels.
**Rejected.** The former free symmetric/braided monoidal category monads directly on
`Mat(Kan)`; treating families over a set as equivariant symmetric sequences.
**Acceptance.** AT-FD-9: discrete arity-two action test; AT-SP-9: classical symmetric
operads in the corrected profunctor ambient; AT-SP-10: coherent operadic comparison;
AT-SP-11: precisely stated E_n examples; AT-SP-13: scoped Kleisli/Mod preservation.
**Status.** ambient correction adopted; ∞-construction provisional, full development M7.

### D-SP-16 · General monoidal enrichment
**Decision.** Define a monoidal Segal-category presentation and its unbiased tensor
multimaps through the chosen categorical interface. Construct Mat(V) with its explicit
size, coherence, and map comparisons; identify its monads with enriched categories.
**Rationale.** Cartesian examples should validate the shared infrastructure first.
**Rejected.** Treating a weak tensor presentation as a strict functor without comparison.
**Acceptance.** A precisely stated Gepner–Haugseng comparison, assigned an acceptance
ID when this later track is activated.
**Status.** later (M7+).

### D-SP-17 · Limits, colimits, and model comparisons
**Decision.** Prove `HasLimits Kan` and `HasColimits Kan` for indexing categories within
explicit universe bounds. Compare derived homotopy (co)limits with the categorical
universal properties of D-UP-13. This supports presheaves, coends, and later substitution
products. It is a substantial M6 theorem target, not an implication of the classifier.
The small model-theoretic lemmas needed for M-F's `MapCat`, `MapRel`, replacement, and
walking constructions occur at M-F; their broader reusable packaging may follow at M2.
General strictification, Kan–Quillen, Bergner/Rezk, Joyal–Tierney, and operadic
comparisons are scheduled by their actual dependencies. A claimed comparison must
name its model and precise statement; full style-A comparison remains AT-RT-9.
**Rationale.** Moving a dependency later on the schedule does not eliminate it.
**Rejected.** Requiring “model structures are only later theorems” when a current
construction already needs their lifting or localization results.
**Acceptance.** AT-SP-12 with sizes explicit; AT-SP-8 for rigidification to an
equivalent model; scoped AT-SP-5/10 and AT-RT-9 as above.
**Status.** provisional routes; full (co)completeness M6.

## Status and open questions

All AT-SP tests are proposed, not proved in this revision. The test numbers retain their
subjects but their changed scopes are recorded in `12-revision-notes.md`.
OQ-SP-1: compile classifier/matrix/monad universe signatures, including new collection
levels. OQ-SP-2: select a precise universe construction at M6. OQ-SP-3: choose the
full coherent matrix presentation; the small M-F example is mandatory first.
OQ-SP-4: establish the stronger span/profunctor VDC comparison beyond the categorical
object comparison. OQ-SP-5: determine the exact monad/preservation hypotheses for the
∞-Kleisli construction on the corrected profunctor ambient.
