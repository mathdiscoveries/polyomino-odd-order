module

public import PolyominoOddOrder.CaseII2
public import PolyominoOddOrder.CaseII3

/-!
# Case (II) of five copies is empty (`CaseII.lean`)

No blueprint unit: the one statement of this file is proved from the entry
statements of the units before it. It is Corollary 63 of `report-4.md`
section 8 in its internal form, used by the frozen statement
`corollary63_corners_in_distinct_tiles` and by `SearchBridge.lean`.

Source: `report-4.md`, section 8, Corollary 63 (lines 595-600). Commit `e5ca51d`.
-/

@[expose] public section

namespace PolyominoOddOrder

/-- Corollary 63: in a 5-copy tiling by a non-rectangular polyomino the four
corner cells lie in four distinct tiles. Source: `report-4.md`, Corollary 63
(lines 595-600). A tile with two corners gives, by Lemmas 2 and 3, a tiling with
a tile on row 0 (`row_tiling_of_two_corners`); Theorem 6 (`theorem6_five`)
leaves a 3-copy tiling (`three_copy`), type H1 (`corollary39`) or the setting of
case (II.3) (`theorem55`). -/
theorem corners_in_distinct_tiles (P : Finset Cell) (hP : IsPolyomino P)
    (hnr : ¬ IsRectangular P) (a b : ℤ) (t : Fin 5 → Finset Cell)
    (ht : IsTiling P a b t) : CornersInDistinctTiles a b t := by
  intro i j j' hj hj'
  by_contra hne
  obtain ⟨ha, hb⟩ := ht.two_le hP hnr (by norm_num)
  obtain ⟨a', b', t', ht', hrow⟩ :=
    row_tiling_of_two_corners P hP 5 (by norm_num) a b ha hb t ht i j j' hne hj hj'
  rcases theorem6_five P hP hnr a' b' t' ht' i hrow with
    ⟨c, t'', h3⟩ | ⟨d, κ, H⟩ | ⟨d, κ, i₁, H⟩
  · exact three_copy P hP hnr a' c t'' h3
  · exact corollary39 H
  · exact theorem55 H

end PolyominoOddOrder
