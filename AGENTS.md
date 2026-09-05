# AGENTS.md — operating manual

Category Madness is built against an explicit, versioned specification. Design revision
1 is active. Read `forest/index.tree`, `forest/fd-0000.tree`, and the relevant current
decision before changing code. D-WF-12 requires retrieval instead of re-derivation.

## 1. Active decisions and history

Decision IDs map directly to forest addresses: D-RT-16 is
`forest/dec-rt-0016.tree`, AT-FD-1 is `forest/at-fd-0001.tree`, and M-F is
`forest/ms-foundation.tree`. Search with `python3 mcp/server.py` or inspect
`forest/registry.json`.

A `frozen` decision changes only through a fresh superseding decision. A `provisional`
decision may change with recorded rationale and reset evidence. `later` means its named
milestone has not activated it. Never cite a `superseded` decision as authority. Exact
historical sources live in `design/history/v0/` and `forest/history/v0/`; they are not
active work.

## 2. Acceptance evidence

Acceptance statuses are `proposed`, `stated`, `proved`, `failed`, `blocked`, `deferred`,
or `retired` (D-WF-10). Only a checked proof of the current statement with approved
axioms earns `proved`. A scope change increments `statement-version` and resets the
status. Tooling gates require reproducible check records. Retired tests do not count as
passed.

M-F is the current queue. Follow the dependency order in `forest/fd-0000.tree`; do not
freeze the root or interface based on an unpassed gate.

## 3. Change requirements

Every PR and commit body cites the active decisions it relies on. CI rejects missing,
unknown, or superseded citations. When a change states or proves a test, update its
forest record in the same revision. Add no sealed constant without an active decision.
Regenerate `forest/registry.json`, keep the forest checks green, and never hand-edit
`Generated/`.

Before submitting, run:

```sh
python3 scripts/forest_check.py
python3 scripts/check_imports.py
python3 scripts/check_unfolding.py
python3 scripts/check_statement_hygiene.py
python3 mcp/server.py --selftest
```

When Lean sources exist, also run `lake build` and `bash scripts/swap_test.sh`.

## 4. Seal and trust boundary

`Theory/` imports only `Interface.*` and approved tactic libraries. It may not import
Mathlib category implementations, `Kernel.*`, or `Root.*`, and it may not unfold sealed
constants. Universal objects are witnesses of proposition-valued specifications.
Everything is universe-polymorphic with `autoImplicit false`.

Kernel-backed and stub builds use identical public signatures. Acceptance evidence must
exclude `sorryAx`, stub axioms in the implementation build, project axioms outside the
allowlist, and private implementation leaks. Keep negative fixtures outside certified
imports (D-TL-17, AT-FD-2, AT-FD-11).

## 5. Layout

```text
design/            active revision source; immutable snapshots under history/
forest/            primary active forest and derived registry; history/ is excluded
Prototype/         minimal M-F experiments and negative fixtures
Kernel/            Mathlib-backed scaffolding, shapes, and homotopy machinery
Root/              candidate VDC∞, relative constructions, examples
Interface/         bundled opaque specification and proved public laws
Interface-Stub/    identical public statements with bodiless test axioms
Theory/{UP,FT,SP}  clients using Interface vocabulary only
Generated/         generated notation and thin APIs
scripts/           validation, porting, seal, citation, and trust tooling
mcp/               read-only active registry retrieval
```

Name structures and theorems for their mathematical conclusions. Definitional equality
is confined to `Kernel/` and `Root/`. Keep generated presentation separate from proved
mathematical laws.

## 6. Commit messages

Cite current IDs in the body, for example:

```text
Cites: D-FD-01, D-WF-10, AT-FD-2
```

Do not put model identifiers in commits, PR text, or code comments.
