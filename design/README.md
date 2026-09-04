# Design documents — phase −1

Working name: **TBD** (placeholder: "the library"). Lean 4 + Mathlib (pinned at M0).

These documents are the phase −1 artifact: human-written markdown, to be ported by an
agent into a forester v5 forest at M0 (see `07-forest-workflow.md`). After the port the
forest is primary and these files are frozen as history.

## How to read

- `00-charter.md` — principles, the three-stage bootstrap, the seal, layering. Read first.
- `01-kernel.md` — stage 0: mathlib scaffolding, shape categories, patterns, Reedy/EZ, Kan machinery.
- `02-root.md` — stage 1: the VDC∞ definition, `Mod`/`Mat`, `Category` as an instance, the seal.
- `03-universal-properties.md` — terminal objects, slices, limits, Kan extensions, witnesses.
- `04-formal-theory.md` — augmented virtual ∞-equipments and formal category theory.
- `05-spaces-enrichment.md` — universe, the Segal category of spaces, `Mat(Kan)`, ∞-operads.
- `06-tooling.md` — generated APIs, attributes, tactics, the seal linter.
- `07-forest-workflow.md` — forester forest, generated nodes, decision registry, retrieval MCP, agent loop.
- `08-roadmap.md` — milestones, freezes, acceptance criteria, risk register.
- `09-bibliography.md` — annotated references keyed to decisions.
- `10-adversarial-review.md` — the adversarial pass on the design and how each item was disposed into decisions.

## Conventions

- **Decisions** carry IDs `D-<AREA>-<nn>` (CH charter, KR kernel, RT root, UP universal
  properties, FT formal theory, SP spaces, TL tooling, WF workflow, RM roadmap). Each has
  *Decision / Rationale / Rejected / Acceptance / Status*.
- **Status** is `frozen` (changes require a superseding decision), `provisional`
  (agents may propose amendments, see D-TL-01), or `later` (not before the stated milestone).
- **Acceptance tests** carry IDs `AT-<AREA>-<n>`. An acceptance test is a Lean statement
  (or a small family of them) whose proof is the evidence that a definition is right.
  Every definition-level decision names at least one.
- **Open questions** for the human are marked `OQ`.
- Cross-references are written `→ D-RT-03`, `→ AT-KR-2`.
- Mathematical claims marked **(verify)** are expected but not yet checked against the
  literature or by proof; they are tasks, not facts.

## Porting instructions (for the M0 agent)

One tree per decision, per acceptance test, per milestone, per open question. Map
`D-RT-03` to the nested address scheme in `07-forest-workflow.md`. Preserve rationale
and rejected alternatives verbatim; they are the part agents will most need later.
Do not check in build artifacts.
