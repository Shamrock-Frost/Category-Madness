# 04 · Formal category theory — revision 1

Develop the coherent formal theory in the augmented root using cell spaces and their
composition. The discrete specialization is a comparison test. There is no requirement
to route proofs through a universally available `hP`.

### D-FT-06 · Restrictions, units, and equipments
**Decision.** Specify a cartesian restriction by the equivalences it induces on cell
spaces over every admissible boundary. `HasRestrictions P` asserts existence of the
required unary restrictions. `HasUnitAt P a` is a separate property, with the augmented
nullary-restriction characterization and its equivalence to the appropriate universal
unit cell proved in the discrete test and then coherently. An augmented virtual
equipment need not have all units. A unital augmented virtual equipment has both
properties. State each theorem's actual unitality requirements.
Companions and conjoints are represented by the appropriate nullary restrictions;
when a target unit exists, compare them with its ordinary restrictions.
**Rationale.** Missing units are part of the point of augmentation and its size handling.
**Rejected.** Simultaneously requiring units in the definition and allowing them to be absent.
**Acceptance.** AT-FT-1: exact discrete comparison; AT-FT-2 for matrices and profunctors;
AT-FT-3: the precisely stated hypotheses under which `Mod` preserves restrictions
and supplies units. Its ∞-version is a theorem target, not automatic.
**Status.** provisional until transcribed and proved; no unspecified axioms are frozen.

### D-FT-07 · Horizontal composites and the double nerve
**Decision.** `HasComposites P` is existence of the required opcartesian universal cells,
including specified treatment of the empty path. When the hypotheses hold, construct
a double Segal nerve by coherent diagrams of paths and composite witnesses. Prove
that its witness choices are contractible and that it has the relevant invariance and
comparison with a double ∞-category model. This is a construction, not restriction
along an assumed inclusion of `Δ×Δ` into the virtual arity category.
**Rationale.** A virtual path can have many horizontal arrows but no specified composite.
**Rejected.** Obtaining a double nerve merely by saying horizontal composites exist.
**Acceptance.** AT-FT-4: comparison with the precisely named Ruit model after any required
completion; AT-FT-5: ordinary profunctor coends and their classical double category.
**Status.** provisional. The set-level instance precedes the full ∞-comparison.

### D-FT-08 · Coherent theorem targets
**Decision.** The targets below use explicit witness spaces and only the hypotheses
needed by each item. Every statement is compared with its discrete counterpart.
1. Representable horizontals, companion/conjoint cells, and the relation between
   equivalence of companions and invertible vertical 2-cells.
2. Yoneda embeddings with the relevant augmented universal cells. Their existence
   is an additional property; presheaf targets and allowable sizes are explicit.
3. Extensions and liftings of horizontals, with pointwise and absolute versions
   distinguished through restriction and stability properties.
4. Weighted limits and colimits as representability of the appropriate modules.
   A conical limit uses the constant terminal-valued weight with the correctly typed
   variance, not an unspecified identity profunctor called a unit weight.
5. Adjunctions via companions and conjoints, with the correct equivalence notion for
   adjunction data; mates retain noninvertible vertical 2-cells.
6. Root monads, Kleisli and Eilenberg–Moore witnesses, and monadicity under the
   required composite and existence hypotheses.
7. Full faithfulness and other justified properties of vertical morphisms through
   their universal cells; no general essential-surjectivity characterization is
   assumed without its hypotheses and comparison.
8. Absolute liftings and the comparison of formal limits with the cone-terminal
   limits of D-UP-13, in the specified vertical categorical ambient.
**Rationale.** A common cell-space API is a plausible route to reuse, but each claim
still needs a precise theorem and a valid instance.
**Rejected.** Inferring all coherent universal properties from equality on `π₀`.
**Acceptance.** AT-FT-1 for the discrete statements; AT-FT-6 for conical weights;
AT-FT-7 for absolute-lifting/cone comparison, with model hypotheses stated.
**Status.** provisional theorem list; exact Lean statements required before proof assignment.

### D-FT-09 · Optional homotopy-level proof routes
**Decision.** Prove discrete instances early. A nondiscrete proof may use a homotopy
2-category or a module equipment only after a comparison witness is built for that
specific ambient. It specifies retained 1-cells, cell components, composition,
transport, and the properties reflected by the comparison. Taking the homotopy
category of each proved hom ∞-category retains its objects; it is not quotienting all
boundary arrows by components. A bicategorical intermediate is acceptable.
There is no general export called `hP` and no theorem that all universal properties
reflect through an arbitrary truncation. Where no comparison exists, prove the result
coherently in the root interface.
**Rationale.** Boundary monodromy invalidates the former shortcut.
**Rejected.** The original schedule “every result in hP first, then lift.”
**Acceptance.** AT-FD-6; AT-FT-8 is retired in its unconditional form. Each concrete
homotopy-equipment comparison receives a new test ID and explicit scope.
**Status.** frozen restriction on the proof route; constructions later as justified.

### D-FT-10 · Cosmoi
**Decision.** A cosmos comparison is optional later work. Specify the enriched model,
limits, isofibrations, and module construction precisely, then compare its homotopy
2-category with a proved part of `Vert₂` or a suitable module equipment.
**Rationale.** Existing formal machinery may help once its hypotheses have been ported.
**Rejected.** Assuming a cosmos or its homotopy equipment comes for free from the root.
**Acceptance.** AT-FT-9, newly stated with exact scope before implementation.
**Status.** later (M7+).

AT-FT-1 through AT-FT-7 remain proposed comparison tests with the revised scopes above.
AT-FT-8's former arbitrary-root claim is retired. AT-FT-9 remains later.
OQ-FT-1 is now the exact coherent restriction/unit transcription. OQ-FT-2 is which
specific homotopy-equipment comparisons repay their construction cost; none is mandatory
for the direct coherent route.
