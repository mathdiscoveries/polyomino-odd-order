module

-- The library root is the proved library: the definitions (`Basic`) and the
-- frozen statements with their proofs (`Main`). It no longer imports `Spec`,
-- `Sanity` or `Verify`. `Spec` and `Main` declare the same names, so they can
-- never be imported together, and `Sanity` and `Verify` now import `Main`, so
-- they are built as modules of their own (`check-lean` builds them by name).
-- This is the switch from the statement-first increment; see `BLUEPRINT.md`,
-- section "Comparator".
public import PolyominoOddOrder.Basic
public import PolyominoOddOrder.Main
