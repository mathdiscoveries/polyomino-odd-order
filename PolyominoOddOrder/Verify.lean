module

public import PolyominoOddOrder.Main
public import PolyominoOddOrder.Witness

/-!
# `PolyominoOddOrder` verification entrypoint

Every theorem exported by this library has its axiom footprint printed below;
the allowed set is `{propext, Classical.choice, Quot.sound}`
(`allow_native_decide: false`).

This file imports `Main`, the proved library, and no longer the Spec, whose
theorems have `sorry` bodies. The lines below therefore report the axioms of
the proofs, and a line shows `sorryAx` exactly when that proof still rests on
an open node. It also imports `Witness`, for the two closed equalities at the
end.
-/

#print axioms PolyominoOddOrder.corollary1a_crossing
#print axioms PolyominoOddOrder.lemma2_no_opposite_corners
#print axioms PolyominoOddOrder.lemma3_adjacent_corners_full_row
#print axioms PolyominoOddOrder.theorem62_no_three_copy_tiling
#print axioms PolyominoOddOrder.theorem21_search_bridge
#print axioms PolyominoOddOrder.theoremA18_no_case_one_tiling
#print axioms PolyominoOddOrder.corollaryA19_no_five_copy_tiling

-- Internal theorems that the paper cites as steps. Their statements were frozen
-- in the second increment and retired from the Spec in the third (see
-- `SPEC-CHANGES.md`); their proofs stay in the library.
#print axioms PolyominoOddOrder.corners_in_distinct_tiles
#print axioms PolyominoOddOrder.sides_are_intervals
#print axioms PolyominoOddOrder.corner_tile_sides
#print axioms PolyominoOddOrder.free_tile_one_side

-- Two closed equalities of `Witness.lean`, proved by `decide` (checked by the
-- kernel), for the paper's sanity examples: the rectangle `R 2 6` has 12
-- cells, and its corner 2, the corner opposite (0, 0), is the cell (1, 5).
#print axioms PolyominoOddOrder.Witness.R_card
#print axioms PolyominoOddOrder.Witness.corner_sample
