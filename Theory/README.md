# Theory/ — stage 2 (D-CH-08, D-CH-09)

Everything else, in interface terms only. CI rejects any file here importing
`Mathlib.CategoryTheory.*`, `Mathlib.AlgebraicTopology.*`, `Kernel.*`, or `Root.*`
(scripts/check_imports.py); tactics are allowed everywhere. Unfolding of sealed
constants is banned (scripts/check_unfolding.py). Builds with `autoImplicit false`.

Sub-areas mirror the design chapters: `UP/` universal properties (M4), `FT/` formal
theory (M5), `SP/` spaces and enrichment (M6).

Empty at M0.
