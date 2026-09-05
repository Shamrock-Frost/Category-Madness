# 03 · Universal properties — revision 1

This layer uses the sealed Segal-category interface and categorical functor objects.
Its bootstrap implementation is in Root/; agreement with monads in `Mat(Kan)` is
AT-SP-3. `MapCat` is the core of a categorical functor object. `MapRel` is used only
inside explicit presentation-level constructions and comparison proofs.

### D-UP-10 · Terminal objects and coherent choices
**Decision.** `IsTerminal t : Prop := ∀ x, Contractible (C(x,t))`, with
`Terminal C := {t // IsTerminal t}` and `HasTerminal C := Nonempty (Terminal C)`.
The full subcategory on terminal objects is empty or a contractible ∞-groupoid.
For a specified terminal `t`, prove that the space of cones with vertex t over any
K-diagram maps equivalently to `MapCat(K,C)`. At the presentation level, a restriction
map is a trivial fibration only after its Kan-fibration hypotheses are proved.
Choosing a section coherent over a parameter diagram requires a lifting theorem in
that diagram category. Separate pointwise choices are not that theorem.
**Rationale.** The universal property supplies uniqueness; existence and model-level
lifting are separate premises.
**Rejected.** An unconditional claim of contractibility when there may be no witness;
trivial fibrancy inferred from an equivalence of abstract spaces alone.
**Acceptance.** AT-UP-1: classical terminal objects and unique isomorphism; AT-FD-3;
AT-UP-6 for a genuinely coherent parameterized construction.
**Status.** provisional implementation; mathematical specification fixed.

### D-UP-11 · Diagrams
**Decision.** A diagram is an object of the categorical functor object `Fun(J,C)`;
its core is `MapCat(J,C)`. A chosen strict presentation may represent that diagram
through a proved comparison with relative maps. Natural equivalences between diagrams
are retained, including equivalences between functors with different object functions.
**Rationale.** Discrete source and target categories can still have nontrivial diagram cores.
**Rejected.** A fixed-label presheaf mapping space as the entire diagram ∞-groupoid.
**Acceptance.** AT-FD-4; the discrete functor-category comparison.
**Status.** provisional until the bootstrap `Fun` comparison is proved at M-F.

### D-UP-12 · Cone categories and slices
**Decision.** For `F : Fun(J,C)`, define `Cone(C,F)` using a derived fibre over F of
`Fun(J^leftcone,C) → Fun(J,C)`, where `J^leftcone = [0] ⋆ J` and the vertex is the
cone apex. Construct a reduced Segal presentation by choosing its object labels to
be the cone data, including the restriction identification with F.
In a shape formula using `[n] ⋆ J`, fix F and the *entire selected cone* at each
vertex. A fibre that fixes only the apex objects is insufficient. At `[0]` the fibre
fixing that cone is a point. Use one functorial replacement/framing for the whole
restriction diagram; strict fibres require proved fibrations. Define commas by a
specified derived comma construction with its own comparison, not an unnamed join.
**Rationale.** The slice's objects contain maps as well as objects of C.
**Rejected.** Full cone spaces at each chosen cone label; independent fibrant
replacement at each simplex.
**Acceptance.** AT-UP-2: classical cone/slice category; AT-UP-3: reduction, fibrancy,
Segal condition, and categorical invariance; the point/edge calculation in AT-FD-8.
**Status.** provisional construction; M4 export only after these proofs.

### D-UP-13 · Limits and related witnesses
**Decision.** `Limit F := Terminal (Cone(C,F))`, with `HasLimit F := Nonempty (Limit F)`.
Products use discrete indexing categories. Representability uses a terminal object in
the relevant category of elements. `RightAdjointAt F y` uses a terminal object of
`F ↓ y`; constructing a whole right adjoint from these witnesses requires the proved
coherent-choice argument. Pointwise right Kan extensions use limits over `(j' ↓ i)`;
left extensions use the dual comma orientation and colimits.
All diagram-size bounds, functoriality, and existence hypotheses are explicit.
**Rationale.** Many universal properties can share terminal-object theory after the
appropriate witness category has been constructed.
**Rejected.** Treating pointwise existence alone as already a coherent functor;
unspecified universe-size quantification over all diagram categories.
**Acceptance.** AT-UP-4: discrete comparisons and pointwise Kan-extension formula.
**Status.** provisional until M4 proofs.

### D-UP-14 · Duality
**Decision.** Generate dual statements for Segal categories where the registered `op`
and transport lemmas apply. Horizontal opposite is available for the augmented planar
root once its shape operation is proved. Vertical opposite and transpose are not
assumed to preserve the augmented virtual presentation. Hand-proved dual results in
the equipment theory may be registered as corresponding statements.
**Rationale.** A translation tool needs a mathematical duality with proved laws.
**Rejected.** A total automatic duality for structures whose shapes are not closed under it.
**Acceptance.** AT-UP-5: generated classical colimit comparison and involution transport.
**Status.** provisional tool scope; mathematical domains explicit.

### D-UP-15 · Witness discipline
**Decision.** Quantify over witnesses. An operation using a universal witness provides
functoriality on its witness category, and equivalences between outputs follow from
that functoriality. Choice bridges may choose an object from proved nonemptiness or a
section from proved lifting. Coherence across a diagram of problems is established in
the parameterized construction before choice is applied; it is not inferred from
one independently chosen section for each parameter.
**Rationale.** Contractibility controls choices only in the correctly constructed space.
**Rejected.** Global chosen-limit constants and hidden data typeclass choices.
**Acceptance.** AT-UP-1, AT-UP-6; the witness-transport client at M4.
**Status.** frozen policy; instances proved individually.

### D-UP-16 · Shape extensions
**Decision.** For a shape inclusion `i`, use `Lan_i ⊣ i* ⊣ Ran_i` with existence
hypotheses. For a full truncation inclusion, `sk_n = Lan_i i*` and `cosk_n = Ran_i i*`
are endofunctors with `sk_n ⊣ cosk_n`, not the reverse. The Čech nerve of `x → s` is
`cosk₀` in augmented simplicial objects over s, when the required finite limits exist.
Prove its levels, augmentation, simplicial identities, and functoriality in the map.
Other shape extensions are added only for established indexing functors.
**Rationale.** Shape language packages the result after existence and coherence are proved.
**Rejected.** Producing only a family of level objects and calling it a simplicial diagram.
**Acceptance.** AT-UP-6: the Čech construction; AT-UP-7: the three adjunctions and
correct skeleton/coskeleton orientation.
**Status.** provisional until M4.

### D-UP-17 · Discrete comparisons
**Decision.** Compare the general theory with ordinary terminal objects, cone categories,
limits, adjoints, and Kan extensions. The comparison is through the exported interface,
with kernel implementations used only to establish the bridge.
**Rationale.** The discrete test checks meaning and the swap build checks abstraction.
**Rejected.** Treating either check as a substitute for the other.
**Acceptance.** AT-UP-1 through AT-UP-7.
**Status.** required M4 acceptance suite.

### D-UP-18 · Universal properties involving categories
**Decision.** Use `VertCore(Cat)` and later `VertCore(Cat_∞)` for categorical mapping
spaces and (∞,1)-universal properties. For ordinary categories these mapping spaces are
cores of functor categories. Construct exponentials/functor objects and verify their
core-valued universal property; use their full functor categories when 2-dimensional
information is required. Products and homotopy pullbacks here are understood in the
(∞,1)-sense. A lax comma object is a separate 2-dimensional construction in `Vert₂`
or the equipment. Do not identify it with a strict or homotopy pullback by terminology.
**Rationale.** The ambient dimension determines the universal property being asserted.
**Rejected.** Calling `VertRaw(Cat)` mapping spaces functor cores.
**Acceptance.** AT-UP-8: for ordinary C,D the chosen exponential is the functor category
and `MapCat(E,Fun(C,D)) ≃ MapCat(E×C,D)`, naturally in E; AT-FD-4's walking-isomorphism test.
**Status.** provisional until M4; AT-UP-8 is mandatory in its exit criteria.

OQ-UP-1: choose the concrete derived comma/framing construction and prove its discrete
comparison. OQ-UP-2: Prop-valued existence classes are allowed; chosen witnesses are
passed explicitly. No data-valued chosen-limit instance is introduced.
