import Theory.Category
-- Cites: D-TL-17, AT-FD-11. A private implementation dependency hidden by an alias.
private def Root.hiddenImplementation : Nat := 0
abbrev Interface.leakyAlias := Root.hiddenImplementation
def Theory.illegalImplementationUse : Nat := Interface.leakyAlias
