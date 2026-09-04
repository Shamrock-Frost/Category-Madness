# Category Madness

A Lean 4 library of category theory whose only primitive is the **virtual double
∞-category**. Ordinary categories, ∞-categories, enriched and internal categories, and
equipments are instances of one definition, and every theorem is proved once against a
sealed interface, never against an implementation.

The library is built by agents against definitions frozen by a human. The definitions,
their acceptance tests, and the interface are the product; proofs are the cost of goods.

**Status: M0 (skeleton).** No Lean has been written. The design is complete and ported
into the forest; the repository layout, CI, and retrieval tooling exist so that the
pipeline is in place before any mathematics is.

## Where things are

| Path | What | Design reference |
|---|---|---|
| `design/` | The phase −1 design documents. **Frozen as history**; the forest is primary. | `design/README.md` |
| `forest/` | The forester forest: one tree per decision (`dec-*`), acceptance test (`at-*`), open question (`oq-*`), milestone (`ms-*`), reference (`bib-*`), plus chapter prose. Start at `forest/index.tree`. | D-WF-01…07 |
| `forest/registry.json` | Machine-readable decision registry, derived from the trees by `scripts/build_registry.py`. | D-WF-02 |
| `Kernel/` `Root/` `Interface/` `Interface-Stub/` `Theory/` `Generated/` | The three-stage bootstrap and the seal. Empty at M0; each has a README stating its rules. | D-CH-08, D-RT-13, D-TL-08 |
| `scripts/` | Seal linter (`check_imports`, `check_unfolding`, `check_statement_hygiene`, `swap_test.sh`), forest checks, citation check, the one-shot port script. | D-TL-06, D-WF-02 |
| `mcp/server.py` | Read-only retrieval MCP over the forest (search / get / neighbors / open_tasks / decision / acceptance). | D-WF-05 |
| `lakefile.toml`, `lean-toolchain` | Lean `v4.33.1`, Mathlib pinned at `v4.33.1`. | D-CH-11, D-KR-02 |
| `.github/workflows/ci.yml` | All checks, blocking. Lean build gated on the presence of Lean sources. | D-TL-06 |

## Working here

- Read `AGENTS.md` first. It is the operating manual: how to find a decision, what a PR
  must cite, what the seal forbids.
- Decisions are cited by ID (`D-RT-03`) or address (`dec-rt-0003`); both resolve. A PR that
  cites no decision fails CI.
- Run the checks locally:

```sh
python3 scripts/forest_check.py
python3 scripts/check_imports.py && python3 scripts/check_unfolding.py && python3 scripts/check_statement_hygiene.py
python3 mcp/server.py --selftest
```

- Attach the retrieval MCP to Claude Code:

```sh
claude mcp add category-madness -- python3 "$PWD/mcp/server.py"
```

## Next steps (M0 → M1)

1. Human sign-off on the port (`forest/wf-0001.tree` lists the judgment calls).
2. Mathlib inventory node, AT-KR-0 (needs a Mathlib checkout at the pinned tag).
3. `forest-export` (D-WF-01) and the `to_dual` skeleton (D-TL-03): the first Lean.
4. M1: shapes and patterns (`forest/ms-0001.tree`).
