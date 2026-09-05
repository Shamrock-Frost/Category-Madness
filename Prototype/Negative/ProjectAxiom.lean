import Theory.Category
-- Cites: D-TL-17, AT-FD-11. Never imported by a certified target.
axiom Theory.testFalse : False
theorem Theory.unsound : False := Theory.testFalse
