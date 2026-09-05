# Prototype

Small, disposable Lean experiments for the M-F foundation-feasibility gates live here.
A prototype may use kernel scaffolding, but it does not become part of the sealed public API
until its acceptance evidence is recorded and the corresponding interface fragment passes the
kernel-backed and stub builds.

Keep negative fixtures outside certified imports. Cite the active decision and acceptance-test
nodes for every experiment.

The matrix experiment is in `Universes/Matrix.lean` and `Universes/Reindex.lean`, with
explicit universe examples in `Universes/Examples.lean`. It covers entry lifts,
object-label lifts, and their comparisons. See `Universes/README.md` for its universe
table, validation commands, and remaining AT-FD-1 work. `lake build` includes all three
modules.
