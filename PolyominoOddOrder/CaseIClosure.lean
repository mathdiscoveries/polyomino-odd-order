module

public import PolyominoOddOrder.FourCorners
public import PolyominoOddOrder.ThreeN
public import PolyominoOddOrder.ThreeOWide
public import PolyominoOddOrder.AdjacentO
public import PolyominoOddOrder.OppositeO
public import PolyominoOddOrder.CaseII

/-!
# Case (I) of five copies is empty (`CaseIClosure.lean`)

No blueprint unit (third increment): every statement of this file is proved
from the entry statements of the units. `report-A2.md`, section 8: "|S| is 1,
2, 3 or 4. |S| = 1: section 3, (3). |S| = 4: section 4. |S| = 3: section 5.
|S| = 2: sections 6 and 7."

A frame (`exists_frame`) is of pattern N or O. The symmetries of `P`
(`flipPX`, `flipPY`, `transposeP`) move the occupied corners of `box(P)` into
one of the normal forms `Four`, `Three`, `Adjacent`, `Opposite`, and
`transposeP` makes `q ≤ p` where an entry statement asks for it:

| occupied corners of `box(P)` (with `(0, 0)`, after `frame_absurd`) | normal form | entry statements |
|---|---|---|
| all four | `Four` | `four_N`, `four_O` |
| all but `(p - 1, q - 1)` | `Three` | `three_N`, `three_O` |
| all but `(0, q - 1)` / `(p - 1, 0)` | `Three` after `flipPX` / `flipPY` | the same |
| `(0, 0)`, `(p - 1, 0)` | `Adjacent` | `adj_N`, `adj_O` |
| `(0, 0)`, `(0, q - 1)` | `Adjacent` after `transposeP` | the same |
| `(0, 0)`, `(p - 1, q - 1)` | `Opposite` | `opp_N`, `opp_O` |
| `(0, 0)` only | all marks equal | `allEqual_N`, `allEqual_O` |

The two targets are `case_one_absurd` (Theorem A18) and `no_five_copy`
(Corollary A19); the second uses Corollary 63 (`corners_in_distinct_tiles`).

Source: `theoretician/report-A2.md` (goals lab, commit `076d663`), section 8.
-/

@[expose] public section

namespace PolyominoOddOrder

open Orient (cornerP)

variable {P : Finset Cell} {p q a b : ℤ} {t : Fin 5 → Finset Cell} {o : Fin 5 → Orient}
  {x5 y5 : ℤ}

/-! ## The normal forms from the corners -/

theorem Three.of_corners (h1 : cornerP p q false false ∈ P) (h2 : cornerP p q true false ∈ P)
    (h3 : cornerP p q false true ∈ P) (h4 : cornerP p q true true ∉ P) : Three P p q :=
  ⟨by simpa [cornerP] using h1, by simpa [cornerP] using h2, by simpa [cornerP] using h3,
    by simpa [cornerP] using h4⟩

theorem Adjacent.of_corners (h1 : cornerP p q false false ∈ P)
    (h2 : cornerP p q true false ∈ P) (h3 : cornerP p q false true ∉ P)
    (h4 : cornerP p q true true ∉ P) : Adjacent P p q :=
  ⟨by simpa [cornerP] using h1, by simpa [cornerP] using h2, by simpa [cornerP] using h3,
    by simpa [cornerP] using h4⟩

theorem Opposite.of_corners (h1 : cornerP p q false false ∈ P)
    (h2 : cornerP p q true true ∈ P) (h3 : cornerP p q true false ∉ P)
    (h4 : cornerP p q false true ∉ P) : Opposite P p q :=
  ⟨by simpa [cornerP] using h1, by simpa [cornerP] using h2, by simpa [cornerP] using h3,
    by simpa [cornerP] using h4⟩

/-! ## Frames of either pattern -/

theorem frame_toFrame5 (h : FrameN P p q a b t o x5 y5 ∨ FrameO P p q a b t o x5 y5) :
    Frame5 P p q a b t o x5 y5 :=
  h.elim (fun F => F.toFrame5) (fun F => F.toFrame5)

theorem frame_flipPX (h : FrameN P p q a b t o x5 y5 ∨ FrameO P p q a b t o x5 y5) :
    FrameN (P.image (GridIso.flipX p).apply) p q a b t (fun i => (o i).pX) x5 y5 ∨
      FrameO (P.image (GridIso.flipX p).apply) p q a b t (fun i => (o i).pX) x5 y5 :=
  h.imp (fun F => F.flipPX) (fun F => F.flipPX)

theorem frame_flipPY (h : FrameN P p q a b t o x5 y5 ∨ FrameO P p q a b t o x5 y5) :
    FrameN (P.image (GridIso.flipY q).apply) p q a b t (fun i => (o i).pY) x5 y5 ∨
      FrameO (P.image (GridIso.flipY q).apply) p q a b t (fun i => (o i).pY) x5 y5 :=
  h.imp (fun F => F.flipPY) (fun F => F.flipPY)

theorem frame_transposeP (h : FrameN P p q a b t o x5 y5 ∨ FrameO P p q a b t o x5 y5) :
    FrameN (P.image GridIso.transpose.apply) q p a b t (fun i => (o i).pT) x5 y5 ∨
      FrameO (P.image GridIso.transpose.apply) q p a b t (fun i => (o i).pT) x5 y5 :=
  h.imp (fun F => F.transposeP) (fun F => F.transposeP)

/-! ## The four numbers of occupied corners -/

/-- `|S| = 4`: `report-A2.md`, section 4. -/
theorem frame_four (h : FrameN P p q a b t o x5 y5 ∨ FrameO P p q a b t o x5 y5)
    (S : Four P p q) : False := by
  rcases le_total q p with hpq | hpq
  · exact h.elim (fun F => four_N F S hpq) (fun F => four_O F S hpq)
  · exact h.elim (fun F => four_N F.transposeP S.transposeP hpq)
      (fun F => four_O F.transposeP S.transposeP hpq)

/-- `|S| = 3`: `report-A2.md`, section 5. -/
theorem frame_three (h : FrameN P p q a b t o x5 y5 ∨ FrameO P p q a b t o x5 y5)
    (S : Three P p q) : False := by
  rcases le_total q p with hpq | hpq
  · exact h.elim (fun F => three_N F S hpq) (fun F => three_O F S hpq)
  · exact h.elim (fun F => three_N F.transposeP S.transposeP hpq)
      (fun F => three_O F.transposeP S.transposeP hpq)

/-- `|S| = 2`, adjacent: `report-A2.md`, section 6. -/
theorem frame_adjacent (h : FrameN P p q a b t o x5 y5 ∨ FrameO P p q a b t o x5 y5)
    (S : Adjacent P p q) : False :=
  h.elim (fun F => adj_N F S) (fun F => adj_O F S)

/-- `|S| = 2`, opposite: `report-A2.md`, section 7. -/
theorem frame_opposite (h : FrameN P p q a b t o x5 y5 ∨ FrameO P p q a b t o x5 y5)
    (S : Opposite P p q) : False := by
  rcases le_total q p with hpq | hpq
  · exact h.elim (fun F => opp_N F S hpq) (fun F => opp_O F S hpq)
  · exact h.elim (fun F => opp_N F.transposeP S.transposeP hpq)
      (fun F => opp_O F.transposeP S.transposeP hpq)

/-- `|S| = 1`: `report-A2.md`, section 3, (3). All marks are equal, so `P` has
all four corners (pattern N) or a reflection that moves the corner (pattern
O). -/
theorem frame_single (h : FrameN P p q a b t o x5 y5 ∨ FrameO P p q a b t o x5 y5)
    (h00 : cornerP p q false false ∈ P) (h10 : cornerP p q true false ∉ P)
    (h01 : cornerP p q false true ∉ P) (h11 : cornerP p q true true ∉ P) : False := by
  have F5 := frame_toFrame5 h
  have hmark : ∀ i : Fin 5, i ≠ 4 → (o i).negX = false ∧ (o i).negY = false := by
    intro i hi
    have hm := F5.mark_mem hi
    cases hx : (o i).negX <;> cases hy : (o i).negY <;> rw [hx, hy] at hm
    · exact ⟨rfl, rfl⟩
    · exact absurd hm h01
    · exact absurd hm h10
    · exact absurd hm h11
  have hm : SameMarks o := fun i hi => by
    obtain ⟨hx, hy⟩ := hmark i hi
    obtain ⟨hx0, hy0⟩ := hmark 0 (by decide)
    exact ⟨hx.trans hx0.symm, hy.trans hy0.symm⟩
  rcases h with F | F
  · exact h10 (by simpa [cornerP] using (allEqual_N F hm).c10)
  · rcases allEqual_O F hm with hs | hs
    · exact h10 (by simpa [cornerP] using (hs (0, 0)).1 (by simpa [cornerP] using h00))
    · exact h01 (by simpa [cornerP] using (hs (0, 0)).1 (by simpa [cornerP] using h00))

/-- `report-A2.md`, section 8, with the corner `(0, 0)` of `box(P)` occupied. -/
theorem frame_absurd_c00 (h : FrameN P p q a b t o x5 y5 ∨ FrameO P p q a b t o x5 y5)
    (h00 : cornerP p q false false ∈ P) : False := by
  by_cases h10 : cornerP p q true false ∈ P <;> by_cases h01 : cornerP p q false true ∈ P <;>
    by_cases h11 : cornerP p q true true ∈ P
  · exact frame_four h (Four.of_corners fun X Y => by cases X <;> cases Y <;> assumption)
  · exact frame_three h (Three.of_corners h00 h10 h01 h11)
  · exact frame_three (frame_flipPX h)
      (Three.of_corners (cornerP_mem_flipPX.2 (by simpa using h10))
        (cornerP_mem_flipPX.2 (by simpa using h00)) (cornerP_mem_flipPX.2 (by simpa using h11))
        (fun hc => h01 (by simpa using cornerP_mem_flipPX.1 hc)))
  · exact frame_adjacent h (Adjacent.of_corners h00 h10 h01 h11)
  · exact frame_three (frame_flipPY h)
      (Three.of_corners (cornerP_mem_flipPY.2 (by simpa using h01))
        (cornerP_mem_flipPY.2 (by simpa using h11)) (cornerP_mem_flipPY.2 (by simpa using h00))
        (fun hc => h10 (by simpa using cornerP_mem_flipPY.1 hc)))
  · exact frame_adjacent (frame_transposeP h)
      (Adjacent.of_corners (cornerP_mem_transposeP.2 h00) (cornerP_mem_transposeP.2 h01)
        (fun hc => h10 (cornerP_mem_transposeP.1 hc))
        (fun hc => h11 (cornerP_mem_transposeP.1 hc)))
  · exact frame_opposite h (Opposite.of_corners h00 h11 h10 h01)
  · exact frame_single h h00 h10 h01 h11

/-- **`report-A2.md`, section 8.** No frame of pattern N or O exists: the mark of
`T_1` is an occupied corner of `box(P)`, and a symmetry of `P` moves it to
`(0, 0)`. -/
theorem frame_absurd (h : FrameN P p q a b t o x5 y5 ∨ FrameO P p q a b t o x5 y5) : False := by
  have hm := (frame_toFrame5 h).mark_mem (i := 0) (by decide)
  cases hx : (o 0).negX <;> cases hy : (o 0).negY <;> rw [hx, hy] at hm
  · exact frame_absurd_c00 h hm
  · exact frame_absurd_c00 (frame_flipPY h) (cornerP_mem_flipPY.2 (by simpa using hm))
  · exact frame_absurd_c00 (frame_flipPX h) (cornerP_mem_flipPX.2 (by simpa using hm))
  · exact frame_absurd_c00 (frame_flipPY (frame_flipPX h))
      (cornerP_mem_flipPY.2 (cornerP_mem_flipPX.2 (by simpa using hm)))

/-! ## The two targets -/

/-- **Theorem A18** (`report-A2.md`, section 8): a 5-copy tiling by a
non-rectangular polyomino does not have its four corner cells in four distinct
tiles. -/
theorem case_one_absurd (P : Finset Cell) (hP : IsPolyomino P) (hnr : ¬ IsRectangular P)
    (a b : ℤ) (t : Fin 5 → Finset Cell) (ht : IsTiling P a b t) :
    ¬ CornersInDistinctTiles a b t := by
  intro hI
  obtain ⟨P', p, q, a', b', t', o, x5, y5, h⟩ := exists_frame hP hnr ht hI
  exact frame_absurd h

/-- **Corollary A19** (`report-A2.md`, section 8): a non-rectangular polyomino
does not tile a rectangle with five copies. Theorem A18 with Corollary 63
(`corners_in_distinct_tiles`). -/
theorem no_five_copy (P : Finset Cell) (hP : IsPolyomino P) (hnr : ¬ IsRectangular P)
    (a b : ℤ) (t : Fin 5 → Finset Cell) : ¬ IsTiling P a b t :=
  fun ht => case_one_absurd P hP hnr a b t ht (corners_in_distinct_tiles P hP hnr a b t ht)

end PolyominoOddOrder
