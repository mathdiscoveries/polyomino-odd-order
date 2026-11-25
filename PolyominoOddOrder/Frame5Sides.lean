module

public import PolyominoOddOrder.Frame5

/-!
# Case (I), foundation 2: runs, sides, (T1), existence of a frame (`Frame5Sides.lean`)

Blueprint unit A0b (third increment). `report-A2.md`, section 1.2 ((R), (Full)),
the side equations (1) of section 1.1, the tool (T1) of section 2, the bottom
side of pattern O, and the step from a 5-copy tiling in case (I) to a frame in
pattern N or O (section 1.1, by (F3)).

Every statement about a side of `R a b` is given for all the sides it is used
at. The versions for the top, the left and the right side follow from the one
for the bottom side through `Frame5.flipY` and `Frame5.transpose`.

| report | Lean |
|---|---|
| (R): the cells of a corner tile on its sides of `R a b` | `Frame5.hside`, `Frame5.vside` |
| `1 ≤ u_i ≤ W_i`, `1 ≤ v_i ≤ H_i` | `Frame5.hrun_bounds`, `Frame5.vrun_bounds` |
| (Full) | `Frame5.hrun_eq_iff`, `Frame5.vrun_eq_iff` |
| (1) | `Frame5.side_bottom`, `side_top`, `side_left`, `side_right`, `FrameO.side_bottom` |
| "the bottom row reads `T_1`, `T_5`, `T_2`" | `FrameO.bottom4` |
| (T1) mirror partners | `mirror_lt`, `Frame5.T1_bottom`, `T1_top`, `T1_left`, `T1_right` |
| patterns N and O exist | `Frame5.exists_of_tiling`, `Frame5.pattern`, `exists_frame` |

Source: `theoretician/report-A2.md` (goals lab, commit `076d663`), sections 1, 2.
-/

@[expose] public section

namespace PolyominoOddOrder

variable {P : Finset Cell} {p q a b : ℤ} {t : Fin 5 → Finset Cell} {o : Fin 5 → Orient}
  {x5 y5 : ℤ}

/-! ## Connected sets: leaving a region -/

/-- A connected set with a cell in a region and a cell outside it has two
adjacent cells, one in the region and one outside. Used wherever the report says
"to enter ... it would have to enter a cell of ...". -/
theorem EdgeConnected.exists_adj_leaving {S : Finset Cell} (hS : EdgeConnected S)
    (A : Cell → Prop) {c d : Cell} (hc : c ∈ S) (hd : d ∈ S) (hcA : A c) (hdA : ¬ A d) :
    ∃ u v : Cell, u ∈ S ∧ v ∈ S ∧ Adj u v ∧ A u ∧ ¬ A v := by
  have h := hS c hc d hd
  clear hc
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact absurd hcA hdA
  | @head u v huv _ ih =>
    by_cases hv : A v
    · exact ih hv
    · exact ⟨u, v, huv.1, huv.2.1, huv.2.2, hcA, hv⟩

/-! ## Intervals of cells and their number -/

/-- A non-empty interval of integers starts somewhere and is as long as its
number of elements. -/
private theorem sides_int_interval {A : Finset ℤ} (hne : A.Nonempty)
    (h : ∀ x₁ x₂ x₃ : ℤ, x₁ ≤ x₂ → x₂ ≤ x₃ → x₁ ∈ A → x₃ ∈ A → x₂ ∈ A) :
    ∃ l : ℤ, ∀ x : ℤ, x ∈ A ↔ l ≤ x ∧ x < l + A.card := by
  have hA : A = Finset.Icc (A.min' hne) (A.max' hne) := by
    ext x
    rw [Finset.mem_Icc]
    exact ⟨fun hx => ⟨A.min'_le x hx, A.le_max' x hx⟩,
      fun hx => h _ _ _ hx.1 hx.2 (A.min'_mem hne) (A.max'_mem hne)⟩
  have hle : A.min' hne ≤ A.max' hne := A.min'_le _ (A.max'_mem hne)
  have hcard : (A.card : ℤ) = A.max' hne + 1 - A.min' hne := by
    conv_lhs => rw [hA]
    rw [Int.card_Icc]
    omega
  refine ⟨A.min' hne, fun x => ?_⟩
  rw [hcard]
  conv_lhs => rw [hA]
  rw [Finset.mem_Icc]
  omega

/-- A set that meets a row in a non-empty interval: where the interval starts and
how long it is. -/
private theorem sides_rowInterval_count {S : Finset Cell} {y x₀ : ℤ} (h : RowInterval S y)
    (h0 : (x₀, y) ∈ S) :
    ∃ l : ℤ, ∀ x : ℤ, (x, y) ∈ S ↔ l ≤ x ∧ x < l + rowCount S y := by
  have hm : ∀ x : ℤ, x ∈ (S.filter fun c => c.2 = y).image Prod.fst ↔ (x, y) ∈ S := by
    intro x
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨x', y'⟩, ⟨hc, rfl⟩, rfl⟩
      exact hc
    · intro hx
      exact ⟨_, ⟨hx, rfl⟩, rfl⟩
  have hcard : ((S.filter fun c => c.2 = y).image Prod.fst).card =
      (S.filter fun c => c.2 = y).card := by
    refine Finset.card_image_of_injOn ?_
    rintro ⟨x, y₁⟩ hc ⟨x', y₂⟩ hd (hxx : x = x')
    have h1 : y₁ = y := (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
    have h2 : y₂ = y := (Finset.mem_filter.1 (Finset.mem_coe.1 hd)).2
    rw [hxx, h1, h2]
  obtain ⟨l, hl⟩ := sides_int_interval ⟨x₀, (hm x₀).2 h0⟩ (fun x₁ x₂ x₃ h12 h23 h1 h3 =>
    (hm x₂).2 (h x₁ x₂ x₃ h12 h23 ((hm x₁).1 h1) ((hm x₃).1 h3)))
  refine ⟨l, fun x => ?_⟩
  rw [← hm x, hl x, hcard]
  rfl

/-! ## The sides of the box of a code -/

/-- A cell of `P` at its local position. -/
private theorem sides_exists_back {P : Finset Cell} {c : Orient} {p q : ℤ} {d : Cell} (hd : d ∈ P) :
    c.back p q (c.fwd p q d) ∈ P := by
  rwa [Orient.back_fwd]

/-- `P` meets the first local column of its box, whatever the code. -/
private theorem sides_exists_col_first {P : Finset Cell} {p q : ℤ} (hl : ∃ y : ℤ, (0, y) ∈ P)
    (hr : ∃ y : ℤ, (p - 1, y) ∈ P) (hb : ∃ x : ℤ, (x, 0) ∈ P) (ht : ∃ x : ℤ, (x, q - 1) ∈ P)
    (c : Orient) : ∃ y : ℤ, c.back p q (0, y) ∈ P := by
  obtain ⟨yl, hl⟩ := hl
  obtain ⟨yr, hr⟩ := hr
  obtain ⟨xb, hb⟩ := hb
  obtain ⟨xt, ht⟩ := ht
  rcases c with ⟨_ | _, _ | _, _ | _⟩
  · exact ⟨_, by simpa [Orient.fwd] using
      sides_exists_back (c := ⟨false, false, false⟩) (q := q) (p := p) hl⟩
  · exact ⟨_, by simpa [Orient.fwd] using
      sides_exists_back (c := ⟨false, false, true⟩) (q := q) (p := p) hl⟩
  · exact ⟨_, by simpa [Orient.fwd] using
      sides_exists_back (c := ⟨false, true, false⟩) (q := q) (p := p) hr⟩
  · exact ⟨_, by simpa [Orient.fwd] using
      sides_exists_back (c := ⟨false, true, true⟩) (q := q) (p := p) hr⟩
  · exact ⟨_, by simpa [Orient.fwd] using
      sides_exists_back (c := ⟨true, false, false⟩) (q := q) (p := p) hb⟩
  · exact ⟨_, by simpa [Orient.fwd] using
      sides_exists_back (c := ⟨true, false, true⟩) (q := q) (p := p) ht⟩
  · exact ⟨_, by simpa [Orient.fwd] using
      sides_exists_back (c := ⟨true, true, false⟩) (q := q) (p := p) hb⟩
  · exact ⟨_, by simpa [Orient.fwd] using
      sides_exists_back (c := ⟨true, true, true⟩) (q := q) (p := p) ht⟩

/-- `P` meets the last local column of its box. -/
private theorem sides_exists_col_last {P : Finset Cell} {p q : ℤ} (hl : ∃ y : ℤ, (0, y) ∈ P)
    (hr : ∃ y : ℤ, (p - 1, y) ∈ P) (hb : ∃ x : ℤ, (x, 0) ∈ P) (ht : ∃ x : ℤ, (x, q - 1) ∈ P)
    (c : Orient) : ∃ y : ℤ, c.back p q (c.W p q - 1, y) ∈ P := by
  obtain ⟨y, hy⟩ := sides_exists_col_first hl hr hb ht c.reflX
  rw [Orient.back_reflX] at hy
  exact ⟨y, by simpa using hy⟩

/-- `P` meets the first local row of its box. -/
private theorem sides_exists_row_first {P : Finset Cell} {p q : ℤ} (hl : ∃ y : ℤ, (0, y) ∈ P)
    (hr : ∃ y : ℤ, (p - 1, y) ∈ P) (hb : ∃ x : ℤ, (x, 0) ∈ P) (ht : ∃ x : ℤ, (x, q - 1) ∈ P)
    (c : Orient) : ∃ x : ℤ, c.back p q (x, 0) ∈ P := by
  obtain ⟨x, hx⟩ := sides_exists_col_first hl hr hb ht c.tr
  rw [Orient.back_tr] at hx
  exact ⟨x, hx⟩

/-- `P` meets the last local row of its box. -/
private theorem sides_exists_row_last {P : Finset Cell} {p q : ℤ} (hl : ∃ y : ℤ, (0, y) ∈ P)
    (hr : ∃ y : ℤ, (p - 1, y) ∈ P) (hb : ∃ x : ℤ, (x, 0) ∈ P) (ht : ∃ x : ℤ, (x, q - 1) ∈ P)
    (c : Orient) : ∃ x : ℤ, c.back p q (x, c.H p q - 1) ∈ P := by
  obtain ⟨x, hx⟩ := sides_exists_row_first hl hr hb ht c.reflY
  rw [Orient.back_reflY] at hx
  exact ⟨x, by simpa using hx⟩

namespace Frame5

private theorem sides_two_le_W (F : Frame5 P p q a b t o x5 y5) (c : Orient) : 2 ≤ c.W p q := by
  have h1 := F.two_le_p
  have h2 := F.two_le_q
  rcases c with ⟨_ | _, _, _⟩ <;> simpa [Orient.W]

private theorem sides_two_le_H (F : Frame5 P p q a b t o x5 y5) (c : Orient) : 2 ≤ c.H p q := by
  have h1 := F.two_le_p
  have h2 := F.two_le_q
  rcases c with ⟨_ | _, _, _⟩ <;> simpa [Orient.H]

/-! ## Runs: (R) and (Full) of `report-A2.md`, section 1.2 -/

/-- (R), horizontal side: the cells of a corner tile on its horizontal side of
`R a b` are the first `u_i` cells from the corner. In local coordinates, for the
code `o i`. Source: section 1.1 ("By (F1) these are the first u_i, v_i cells of
the side, counted from the corner") and (R) of section 1.2. -/
theorem hside (F : Frame5 P p q a b t o x5 y5) {i : Fin 5} (hi : i ≠ 4) (x : ℤ) :
    (o i).back p q (x, 0) ∈ P ↔ 0 ≤ x ∧ x < (o i).rowLine p q P 0 := by
  have ha := F.two_le_a
  have hI := fun i => sides_are_intervals P F.poly 5 a b t F.tiling i
  fin_cases i
  · obtain ⟨l, hl⟩ := sides_rowInterval_count (hI 0).1 F.corner0
    have hc : rowCount (t 0) 0 = (o 0).rowLine p q P 0 := by simpa [loc] using F.rowCount_tile 0 0
    have h0 := (hl 0).1 F.corner0
    have hl0 : (l, (0 : ℤ)) ∈ t 0 := (hl l).2 ⟨le_rfl, by omega⟩
    have := (mem_R.1 (F.sub_R 0 hl0)).1
    have hx := hl x
    rw [F.mem0, hc] at hx
    simp only at this
    obtain rfl : l = 0 := by omega
    simpa using hx
  · obtain ⟨l, hl⟩ := sides_rowInterval_count (hI 1).1 F.corner1
    have hc : rowCount (t 1) 0 = (o 1).rowLine p q P 0 := by simpa [loc] using F.rowCount_tile 1 0
    have h0 := (hl (a - 1)).1 F.corner1
    have hl0 : (l + rowCount (t 1) 0 - 1, (0 : ℤ)) ∈ t 1 := (hl _).2 ⟨by omega, by omega⟩
    have := (mem_R.1 (F.sub_R 1 hl0)).1
    have hx := hl (a - 1 - x)
    rw [F.mem1] at hx
    simp only [sub_sub_cancel] at this hx
    rw [hc] at this h0 hx
    show (o 1).back p q (x, 0) ∈ P ↔ 0 ≤ x ∧ x < (o 1).rowLine p q P 0
    rw [hx]
    omega
  · obtain ⟨l, hl⟩ := sides_rowInterval_count (hI 2).2.1 F.corner2
    have hc : rowCount (t 2) (b - 1) = (o 2).rowLine p q P 0 := by
      simpa [loc] using F.rowCount_tile 2 (b - 1)
    have h0 := (hl (a - 1)).1 F.corner2
    have hl0 : (l + rowCount (t 2) (b - 1) - 1, b - 1) ∈ t 2 := (hl _).2 ⟨by omega, by omega⟩
    have := (mem_R.1 (F.sub_R 2 hl0)).1
    have hx := hl (a - 1 - x)
    rw [F.mem2] at hx
    simp only [sub_sub_cancel, sub_self] at this hx
    rw [hc] at this h0 hx
    show (o 2).back p q (x, 0) ∈ P ↔ 0 ≤ x ∧ x < (o 2).rowLine p q P 0
    rw [hx]
    omega
  · obtain ⟨l, hl⟩ := sides_rowInterval_count (hI 3).2.1 F.corner3
    have hc : rowCount (t 3) (b - 1) = (o 3).rowLine p q P 0 := by
      simpa [loc] using F.rowCount_tile 3 (b - 1)
    have h0 := (hl 0).1 F.corner3
    have hl0 : (l, b - 1) ∈ t 3 := (hl l).2 ⟨le_rfl, by omega⟩
    have := (mem_R.1 (F.sub_R 3 hl0)).1
    have hx := hl x
    rw [F.mem3] at hx
    simp only [sub_self] at this hx
    rw [hc] at h0 hx
    show (o 3).back p q (x, 0) ∈ P ↔ 0 ≤ x ∧ x < (o 3).rowLine p q P 0
    rw [hx]
    omega
  · exact absurd rfl hi

/-- (R), vertical side: the cells of a corner tile on its vertical side of `R a b`
are the first `v_i` cells from the corner. -/
theorem vside (F : Frame5 P p q a b t o x5 y5) {i : Fin 5} (hi : i ≠ 4) (y : ℤ) :
    (o i).back p q (0, y) ∈ P ↔ 0 ≤ y ∧ y < (o i).colLine p q P 0 := by
  obtain ⟨t', F'⟩ := F.transpose
  fin_cases i
  · simpa [Orient.back_tr, Orient.rowLine_tr] using F'.hside (i := 0) (by decide) y
  · simpa [Orient.back_tr, Orient.rowLine_tr] using F'.hside (i := 3) (by decide) y
  · simpa [Orient.back_tr, Orient.rowLine_tr] using F'.hside (i := 2) (by decide) y
  · simpa [Orient.back_tr, Orient.rowLine_tr] using F'.hside (i := 1) (by decide) y
  · exact absurd rfl hi

/-- `1 ≤ u_i ≤ W_i` (section 1.1); for `i = 4` the same bounds hold for the lowest
row of `box(T_5)`. -/
theorem hrun_bounds (F : Frame5 P p q a b t o x5 y5) (i : Fin 5) :
    1 ≤ (o i).rowLine p q P 0 ∧ (o i).rowLine p q P 0 ≤ (o i).W p q := by
  have hH := F.sides_two_le_H (o i)
  exact ⟨F.rowLine_pos (o i) le_rfl (by omega), F.rowLine_le (o i) 0⟩

/-- `1 ≤ v_i ≤ H_i` (section 1.1). -/
theorem vrun_bounds (F : Frame5 P p q a b t o x5 y5) (i : Fin 5) :
    1 ≤ (o i).colLine p q P 0 ∧ (o i).colLine p q P 0 ≤ (o i).H p q := by
  have hW := F.sides_two_le_W (o i)
  exact ⟨F.colLine_pos (o i) le_rfl (by omega), F.colLine_le (o i) 0⟩

/-- (Full), horizontal: the run of the mark of a corner tile along its horizontal
side is the whole side exactly when the other end of that side of `box(P)` is
occupied. Source: section 1.2, (Full). -/
theorem hrun_eq_iff (F : Frame5 P p q a b t o x5 y5) {i : Fin 5} (hi : i ≠ 4) :
    (o i).rowLine p q P 0 = (o i).W p q ↔ (o i).back p q ((o i).W p q - 1, 0) ∈ P := by
  have h1 := F.hrun_bounds i
  rw [F.hside hi]
  omega

/-- (Full), vertical. -/
theorem vrun_eq_iff (F : Frame5 P p q a b t o x5 y5) {i : Fin 5} (hi : i ≠ 4) :
    (o i).colLine p q P 0 = (o i).H p q ↔ (o i).back p q (0, (o i).H p q - 1) ∈ P := by
  have h1 := F.vrun_bounds i
  rw [F.vside hi]
  omega

/-- Some cell of the box of a tile is not in the tile ("T_i is not a rectangle"),
for any code. -/
theorem exists_hole (F : Frame5 P p q a b t o x5 y5) (c : Orient) :
    ∃ l : Cell, ((0 ≤ l.1 ∧ l.1 < c.W p q) ∧ 0 ≤ l.2 ∧ l.2 < c.H p q) ∧ c.back p q l ∉ P := by
  obtain ⟨d, hd, hdP⟩ := exists_hole_of_not_isRectangular F.notRect
  refine ⟨c.fwd p q d, ?_, by rwa [Orient.back_fwd]⟩
  rw [← Orient.back_mem_R, Orient.back_fwd]
  exact boundingBox_subset_R F.sub hd

/-! ## The side equations (1) of `report-A2.md`, section 1.1 -/

/-- (1) for a free bottom side: `u_1 + u_2 = a`. -/
theorem side_bottom (F : Frame5 P p q a b t o x5 y5) (h : 1 ≤ y5) :
    (o 0).rowLine p q P 0 + (o 1).rowLine p q P 0 = a := by
  have hb := F.two_le_b
  have hs := F.row_sum (y := 0) le_rfl (by omega)
  have h2 := F.H_le (i := 2) (by decide)
  have h3 := F.H_le (i := 3) (by decide)
  rw [F.rowLine_zero (o 2) (Or.inr (by omega)), F.rowLine_zero (o 3) (Or.inr (by omega)),
    F.rowLine_zero (o 4) (Or.inl (by omega))] at hs
  omega

/-- (1) for a free top side: `u_3 + u_4 = a`. -/
theorem side_top (F : Frame5 P p q a b t o x5 y5) (h : y5 + (o 4).H p q ≤ b - 1) :
    (o 2).rowLine p q P 0 + (o 3).rowLine p q P 0 = a := by
  have hb := F.two_le_b
  have hs := F.row_sum (y := b - 1) (by omega) (by omega)
  have h0 := F.H_le (i := 0) (by decide)
  have h1 := F.H_le (i := 1) (by decide)
  rw [F.rowLine_zero (o 0) (Or.inr (by omega)), F.rowLine_zero (o 1) (Or.inr (by omega)),
    F.rowLine_zero (o 4) (Or.inr (by omega)), sub_self] at hs
  omega

/-- (1) for a free left side: `v_1 + v_4 = b`. -/
theorem side_left (F : Frame5 P p q a b t o x5 y5) (h : 1 ≤ x5) :
    (o 0).colLine p q P 0 + (o 3).colLine p q P 0 = b := by
  have ha := F.two_le_a
  have hs := F.col_sum (x := 0) le_rfl (by omega)
  have h1 := F.W_le (i := 1) (by decide)
  have h2 := F.W_le (i := 2) (by decide)
  rw [F.colLine_zero (o 1) (Or.inr (by omega)), F.colLine_zero (o 2) (Or.inr (by omega)),
    F.colLine_zero (o 4) (Or.inl (by omega))] at hs
  omega

/-- (1) for a free right side: `v_2 + v_3 = b`. -/
theorem side_right (F : Frame5 P p q a b t o x5 y5) (h : x5 + (o 4).W p q ≤ a - 1) :
    (o 1).colLine p q P 0 + (o 2).colLine p q P 0 = b := by
  have ha := F.two_le_a
  have hs := F.col_sum (x := a - 1) (by omega) (by omega)
  have h0 := F.W_le (i := 0) (by decide)
  have h3 := F.W_le (i := 3) (by decide)
  rw [F.colLine_zero (o 0) (Or.inr (by omega)), F.colLine_zero (o 3) (Or.inr (by omega)),
    F.colLine_zero (o 4) (Or.inr (by omega)), sub_self] at hs
  omega

end Frame5

/-! ## (T1) Mirror partners -/

/-- The core of (T1): a connected set `T` on the cell `(0, 0)` that is disjoint
from its mirror image `T'` in the vertical midline of `R a b` lies strictly left
of the midline. Source: `report-A2.md`, section 2, (T1), proof ("2x - (a-1) does
not change sign along a path in T_1"). -/
theorem mirror_lt {a : ℤ} {T T' : Finset Cell} (hT : EdgeConnected T)
    (h0 : ((0, 0) : Cell) ∈ T) (hmir : ∀ c : Cell, c ∈ T' ↔ (a - 1 - c.1, c.2) ∈ T)
    (hd : Disjoint T T') (ha : 2 ≤ a) : ∀ c ∈ T, 2 * c.1 < a - 1 := by
  intro c hc
  by_contra hcon
  obtain ⟨⟨ux, uy⟩, ⟨vx, vy⟩, hu, hv, hadj, hA, hB⟩ :=
    hT.exists_adj_leaving (fun c => 2 * c.1 < a - 1) h0 hc (by simp only; omega) hcon
  simp only [adj_iff] at hadj
  simp only at hA hB
  have hvx : vx = ux + 1 ∧ vy = uy := by omega
  obtain ⟨rfl, rfl⟩ := hvx
  rcases (by omega : a - 1 = 2 * ux + 1 ∨ a - 1 = 2 * ux + 2) with h | h
  · refine Finset.disjoint_left.1 hd hu ((hmir _).2 ?_)
    have : a - 1 - ux = ux + 1 := by omega
    simpa [this] using hv
  · refine Finset.disjoint_left.1 hd hv ((hmir _).2 ?_)
    have : a - 1 - (ux + 1) = ux + 1 := by omega
    simpa [this] using hv

namespace Frame5

/-- (T1) at a free bottom side: two corner tiles with the same code have a run as
long as their box, and it is half the side. Source: `report-A2.md`, section 2,
(T1). "Same mark and same direction of box(P) along the side" is `o 0 = o 1`. -/
theorem T1_bottom (F : Frame5 P p q a b t o x5 y5) (hfree : 1 ≤ y5) (h : o 0 = o 1) :
    (o 0).rowLine p q P 0 = (o 0).W p q ∧ a = 2 * (o 0).W p q := by
  have hlt := mirror_lt (F.conn 0) F.corner0 (T' := t 1) (a := a)
    (fun c => by rw [F.mem1, F.mem0, h]) (F.tiling.disjoint 0 1 (by decide)) F.two_le_a
  obtain ⟨y, hy⟩ := sides_exists_col_last F.left F.right F.bottom F.top (o 0)
  have hW := hlt _ ((F.mem0 _).2 hy)
  have hs := F.side_bottom hfree
  have hu := F.hrun_bounds 0
  rw [← h] at hs
  simp only at hW
  omega

/-- (T1) at a free top side. -/
theorem T1_top (F : Frame5 P p q a b t o x5 y5) (hfree : y5 + (o 4).H p q ≤ b - 1)
    (h : o 2 = o 3) : (o 2).rowLine p q P 0 = (o 2).W p q ∧ a = 2 * (o 2).W p q := by
  obtain ⟨t', F'⟩ := F.flipY
  have := F'.T1_bottom (by omega) (by simpa using h.symm)
  rw [h]
  simpa using this

/-- (T1) at a free left side. -/
theorem T1_left (F : Frame5 P p q a b t o x5 y5) (hfree : 1 ≤ x5) (h : o 0 = o 3) :
    (o 0).colLine p q P 0 = (o 0).H p q ∧ b = 2 * (o 0).H p q := by
  obtain ⟨t', F'⟩ := F.transpose
  have := F'.T1_bottom hfree (by simpa using congrArg Orient.tr h)
  simpa [Orient.rowLine_tr] using this

/-- (T1) at a free right side. -/
theorem T1_right (F : Frame5 P p q a b t o x5 y5) (hfree : x5 + (o 4).W p q ≤ a - 1)
    (h : o 1 = o 2) : (o 1).colLine p q P 0 = (o 1).H p q ∧ b = 2 * (o 1).H p q := by
  obtain ⟨t', F'⟩ := F.transpose
  have := F'.T1_top (by simpa using hfree) (by simpa using congrArg Orient.tr h.symm)
  rw [h]
  simpa [Orient.rowLine_tr] using this

end Frame5

/-! ## The two patterns: sides -/

namespace FrameN

theorem side_bottom (F : FrameN P p q a b t o x5 y5) :
    (o 0).rowLine p q P 0 + (o 1).rowLine p q P 0 = a :=
  F.toFrame5.side_bottom F.y5_pos

theorem side_top (F : FrameN P p q a b t o x5 y5) :
    (o 2).rowLine p q P 0 + (o 3).rowLine p q P 0 = a :=
  F.toFrame5.side_top F.y5_le

theorem side_left (F : FrameN P p q a b t o x5 y5) :
    (o 0).colLine p q P 0 + (o 3).colLine p q P 0 = b :=
  F.toFrame5.side_left F.x5_pos

theorem side_right (F : FrameN P p q a b t o x5 y5) :
    (o 1).colLine p q P 0 + (o 2).colLine p q P 0 = b :=
  F.toFrame5.side_right F.x5_le

end FrameN

namespace FrameO

theorem y5_le (F : FrameO P p q a b t o x5 y5) : y5 + (o 4).H p q ≤ b - 1 := by
  have h1 := F.y5_eq
  have h2 := F.h5_le
  omega

theorem side_top (F : FrameO P p q a b t o x5 y5) :
    (o 2).rowLine p q P 0 + (o 3).rowLine p q P 0 = a :=
  F.toFrame5.side_top F.y5_le

theorem side_left (F : FrameO P p q a b t o x5 y5) :
    (o 0).colLine p q P 0 + (o 3).colLine p q P 0 = b :=
  F.toFrame5.side_left F.x5_pos

theorem side_right (F : FrameO P p q a b t o x5 y5) :
    (o 1).colLine p q P 0 + (o 2).colLine p q P 0 = b :=
  F.toFrame5.side_right F.x5_le

/-- (1) in pattern O, bottom side: `u_1 + mu + u_2 = a`, where `mu` is the number
of cells of `T_5` in row 0. Source: `report-A2.md`, section 1.1. -/
theorem side_bottom (F : FrameO P p q a b t o x5 y5) :
    (o 0).rowLine p q P 0 + (o 4).rowLine p q P 0 + (o 1).rowLine p q P 0 = a := by
  have hb := F.toFrame5.two_le_b
  have hs := F.toFrame5.row_sum (y := 0) le_rfl (by omega)
  have h2 := F.toFrame5.H_le (i := 2) (by decide)
  have h3 := F.toFrame5.H_le (i := 3) (by decide)
  rw [F.toFrame5.rowLine_zero (o 2) (Or.inr (by omega)),
    F.toFrame5.rowLine_zero (o 3) (Or.inr (by omega)), F.y5_eq, sub_self] at hs
  omega

/-- `mu ≥ 1`. -/
theorem mu_pos (F : FrameO P p q a b t o x5 y5) : 1 ≤ (o 4).rowLine p q P 0 :=
  (F.toFrame5.hrun_bounds 4).1

/-- The bottom row reads `T_1`, `T_5`, `T_2`: the cells of `T_5` in row 0 are the
`mu` cells after the `u_1` cells of `T_1`. Source: `report-A2.md`, section 1.1,
pattern O ("By (F1), (F2) the bottom row reads T_1, T_5, T_2; T_5 has mu >= 1
cells there, an interval"). -/
theorem bottom4 (F : FrameO P p q a b t o x5 y5) (x : ℤ) :
    ((x, 0) : Cell) ∈ t 4 ↔
      (o 0).rowLine p q P 0 ≤ x ∧ x < (o 0).rowLine p q P 0 + (o 4).rowLine p q P 0 := by
  have F' := F.toFrame5
  have hb := F'.two_le_b
  have hs := F.side_bottom
  have hr := F.mu_pos
  have hu0 := F'.hrun_bounds 0
  have hu1 := F'.hrun_bounds 1
  have hm0 : (((x, 0) : Cell) ∈ t 0) ↔ 0 ≤ x ∧ x < (o 0).rowLine p q P 0 := by
    rw [F'.mem0, F'.hside (by decide)]
  have hm1 : (((x, 0) : Cell) ∈ t 1) ↔ 0 ≤ a - 1 - x ∧ a - 1 - x < (o 1).rowLine p q P 0 := by
    rw [F'.mem1, F'.hside (by decide)]
  constructor
  · intro h4
    have hR := (mem_R.1 (F'.sub_R 4 h4)).1
    simp only at hR
    have n0 : ((x, 0) : Cell) ∉ t 0 := fun h => absurd (F'.tile_unique h h4) (by decide)
    have n1 : ((x, 0) : Cell) ∉ t 1 := fun h => absurd (F'.tile_unique h h4) (by decide)
    rw [hm0] at n0
    rw [hm1] at n1
    omega
  · intro hx
    have h2 := F'.H_le (i := 2) (by decide)
    have h3 := F'.H_le (i := 3) (by decide)
    have hR : ((x, 0) : Cell) ∈ R a b := mem_R.2 ⟨⟨by simp only; omega, by simp only; omega⟩,
      by simp only; omega, by simp only; omega⟩
    rcases F'.cover_cases hR with h | h | h | h | h
    · have := hm0.1 h.1
      omega
    · have := hm1.1 h.1
      omega
    · have := h.2.2
      simp only at this
      omega
    · have := h.2.2
      simp only at this
      omega
    · exact h.1

end FrameO

/-! ## From a tiling to a frame (`report-A2.md`, section 1.1) -/

/-- The inverse of a grid isometry, read through a code: the code comes from the
switches, and `(X, Y)` is the lower left cell of the image of `R p q`. -/
private theorem sides_exists_code (g : GridIso) (p q : ℤ) :
    ∃ (c : Orient) (X Y : ℤ), ∀ d : Cell, g.inv.apply d = c.back p q (d.1 - X, d.2 - Y) := by
  obtain ⟨gs, gx, gy, u, w⟩ := g
  refine ⟨⟨gs, if gs then gy else gx, if gs then gx else gy⟩,
    if gx then u - ((if gs then q else p) - 1) else u,
    if gy then w - ((if gs then p else q) - 1) else w, fun d => ?_⟩
  cases gs <;> cases gx <;> cases gy <;>
    simp [GridIso.inv, GridIso.apply, Orient.back, Prod.ext_iff] <;> omega

/-- A copy of `P` (with `box(P) = R p q`) inside `R a b`: its code and the lower
left cell of its box, and the box lies in `R a b`. -/
private theorem sides_exists_placed {P T : Finset Cell} {p q a b : ℤ} (hl : ∃ y : ℤ, (0, y) ∈ P)
    (hr : ∃ y : ℤ, (p - 1, y) ∈ P) (hb : ∃ x : ℤ, (x, 0) ∈ P) (ht : ∃ x : ℤ, (x, q - 1) ∈ P)
    (hsub : P ⊆ R p q) (hT : Congruent P T) (hTR : T ⊆ R a b) :
    ∃ (c : Orient) (X Y : ℤ), (∀ d : Cell, d ∈ T ↔ c.back p q (d.1 - X, d.2 - Y) ∈ P) ∧
      (0 ≤ X ∧ X + c.W p q ≤ a) ∧ (0 ≤ Y ∧ Y + c.H p q ≤ b) ∧
      ∀ d ∈ T, (X ≤ d.1 ∧ d.1 < X + c.W p q) ∧ Y ≤ d.2 ∧ d.2 < Y + c.H p q := by
  obtain ⟨g, rfl⟩ := hT
  obtain ⟨c, X, Y, hg⟩ := sides_exists_code g p q
  have hm : ∀ d : Cell, d ∈ P.image g.apply ↔ c.back p q (d.1 - X, d.2 - Y) ∈ P := by
    intro d
    rw [GridIso.mem_image_iff, hg]
  have hin : ∀ x y : ℤ, c.back p q (x, y) ∈ P → (x + X, y + Y) ∈ R a b := by
    intro x y h
    refine hTR ((hm _).2 ?_)
    simpa using h
  obtain ⟨y0, h0⟩ := sides_exists_col_first hl hr hb ht c
  obtain ⟨y1, h1⟩ := sides_exists_col_last hl hr hb ht c
  obtain ⟨x0, h2⟩ := sides_exists_row_first hl hr hb ht c
  obtain ⟨x1, h3⟩ := sides_exists_row_last hl hr hb ht c
  have k0 := (mem_R.1 (hin _ _ h0)).1
  have k1 := (mem_R.1 (hin _ _ h1)).1
  have k2 := (mem_R.1 (hin _ _ h2)).2
  have k3 := (mem_R.1 (hin _ _ h3)).2
  simp only at k0 k1 k2 k3
  refine ⟨c, X, Y, hm, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, fun d hd => ?_⟩
  have h := (Orient.back_mem_R c p q _).1 (hsub ((hm d).1 hd))
  simp only at h
  omega

/-- A 5-copy tiling in case (I) is a frame: the tiles are renamed so that
`t' 0, ..., t' 3` hold the corner cells, `P` is moved so that its box is
`R p q`, and each isometry `g_i` becomes a code. Source: `report-A2.md`,
section 1.1, first paragraph. -/
theorem Frame5.exists_of_tiling {P : Finset Cell} (hP : IsPolyomino P)
    (hnr : ¬ IsRectangular P) {a b : ℤ} {t : Fin 5 → Finset Cell} (ht : IsTiling P a b t)
    (hI : CornersInDistinctTiles a b t) :
    ∃ (P' : Finset Cell) (p q : ℤ) (t' : Fin 5 → Finset Cell) (o : Fin 5 → Orient)
      (x5 y5 : ℤ), Frame5 P' p q a b t' o x5 y5 := by
  obtain ⟨ha, hb⟩ := ht.two_le hP hnr (by norm_num)
  obtain ⟨e, he⟩ := ht.exists_corner_order ha hb hI
  have ht' := ht.reindex e
  set t' : Fin 5 → Finset Cell := fun i => t (e i) with ht'def
  have c0 : ((0, 0) : Cell) ∈ t' 0 := he 0
  have c1 : ((a - 1, 0) : Cell) ∈ t' 1 := he 1
  have c2 : ((a - 1, b - 1) : Cell) ∈ t' 2 := he 2
  have c3 : ((0, b - 1) : Cell) ∈ t' 3 := he 3
  have hpoly := ht'.tile_isPolyomino hP 0
  have hnr' := ht'.tile_not_isRectangular hnr 0
  have htt := ht'.of_tile 0
  have hbox := ht'.corner_tile_subset_box c0
  set Q := t' 0 with hQ
  set p := width Q with hp
  set q := height Q with hq
  have hsub : Q ⊆ R p q := hbox ▸ subset_boundingBox Q
  have hpos := mem_R.1 (hsub c0)
  simp only at hpos
  obtain ⟨hl, hr⟩ := exists_cols_of_width_eq hsub (by omega) hp.symm
  obtain ⟨hbt, htp⟩ : (∃ x, (x, (0 : ℤ)) ∈ Q) ∧ ∃ x, (x, q - 1) ∈ Q := by
    refine ⟨⟨0, c0⟩, ?_⟩
    have hs := ySpan_eq_of_height_eq hsub (by omega) hq.symm
    have h1 : q - 1 ∈ ySpan Q := by rw [hs, Finset.mem_Ico]; omega
    obtain ⟨_, _, d, hd, _, hle⟩ := mem_ySpan.1 h1
    have hdR := mem_R.1 (hsub hd)
    have : d.2 = q - 1 := by omega
    exact ⟨d.1, by rw [← this]; exact hd⟩
  have hpl := fun i => sides_exists_placed hl hr hbt htp hsub (htt.congruent i) (htt.subset_R i)
  obtain ⟨o0, X0, Y0, m0, hX0, hY0, b0⟩ := hpl 0
  obtain ⟨o1, X1, Y1, m1, hX1, hY1, b1⟩ := hpl 1
  obtain ⟨o2, X2, Y2, m2, hX2, hY2, b2⟩ := hpl 2
  obtain ⟨o3, X3, Y3, m3, hX3, hY3, b3⟩ := hpl 3
  obtain ⟨o4, X4, Y4, m4, hX4, hY4, b4⟩ := hpl 4
  have k0 := b0 _ c0
  have k1 := b1 _ c1
  have k2 := b2 _ c2
  have k3 := b3 _ c3
  simp only at k0 k1 k2 k3
  have hmem : ∀ (i : Fin 5) (c : Cell), c ∈ t' i ↔
      ((![o0, o1.reflX, o2.turn, o3.reflY, o4] : Fin 5 → Orient) i).back p q
        (loc a b X4 Y4 i c) ∈ Q := by
    intro i c
    fin_cases i
    · show c ∈ t' 0 ↔ o0.back p q (c.1, c.2) ∈ Q
      rw [m0, show c.1 - X0 = c.1 by omega, show c.2 - Y0 = c.2 by omega]
    · show c ∈ t' 1 ↔ o1.reflX.back p q (a - 1 - c.1, c.2) ∈ Q
      rw [m1, Orient.back_reflX, show c.1 - X1 = o1.W p q - 1 - (a - 1 - c.1) by omega,
        show c.2 - Y1 = c.2 by omega]
    · show c ∈ t' 2 ↔ o2.turn.back p q (a - 1 - c.1, b - 1 - c.2) ∈ Q
      rw [m2, Orient.back_turn, show c.1 - X2 = o2.W p q - 1 - (a - 1 - c.1) by omega,
        show c.2 - Y2 = o2.H p q - 1 - (b - 1 - c.2) by omega]
    · show c ∈ t' 3 ↔ o3.reflY.back p q (c.1, b - 1 - c.2) ∈ Q
      rw [m3, Orient.back_reflY, show c.1 - X3 = c.1 by omega,
        show c.2 - Y3 = o3.H p q - 1 - (b - 1 - c.2) by omega]
    · exact m4 c
  refine ⟨Q, p, q, t', _, X4, Y4, hpoly, hnr', hsub, hl, hr, hbt, htp, htt, hmem, ?_⟩
  intro i hi
  fin_cases i
  · simpa [loc] using (hmem 0 _).1 c0
  · simpa [loc] using (hmem 1 _).1 c1
  · simpa [loc] using (hmem 2 _).1 c2
  · simpa [loc] using (hmem 3 _).1 c3
  · exact absurd rfl hi

/-- (F3) for the box of `T_5`: at most one of the four sides of `R a b` holds a
side of `box(T_5)`. -/
private theorem Frame5.sides_one_side (F : Frame5 P p q a b t o x5 y5) :
    ¬ ∃ s s' : Fin 4, s ≠ s' ∧ Meets (t 4) (side a b s) ∧ Meets (t 4) (side a b s') := by
  refine free_tile_one_side P F.poly F.notRect a b t F.tiling F.cornersDistinct 4 fun j hj => ?_
  fin_cases j
  · exact absurd (F.tile_unique F.corner0 hj) (by decide)
  · exact absurd (F.tile_unique F.corner1 hj) (by decide)
  · exact absurd (F.tile_unique F.corner2 hj) (by decide)
  · exact absurd (F.tile_unique F.corner3 hj) (by decide)

private theorem Frame5.sides_mem4 (F : Frame5 P p q a b t o x5 y5) {x y : ℤ}
    (h : (o 4).back p q (x, y) ∈ P) : ((x + x5, y + y5) : Cell) ∈ t 4 := by
  rw [F.mem4]
  simpa using h

private theorem Frame5.sides_meets_bottom (F : Frame5 P p q a b t o x5 y5) (h : y5 = 0) :
    Meets (t 4) (side a b 0) := by
  obtain ⟨x, hx⟩ := sides_exists_row_first F.left F.right F.bottom F.top (o 4)
  have hm := F.sides_mem4 hx
  exact ⟨_, hm, mem_bottomRow.2 ⟨F.sub_R 4 hm, by simp only; omega⟩⟩

private theorem Frame5.sides_meets_right (F : Frame5 P p q a b t o x5 y5)
    (h : x5 + (o 4).W p q = a) : Meets (t 4) (side a b 1) := by
  obtain ⟨y, hy⟩ := sides_exists_col_last F.left F.right F.bottom F.top (o 4)
  have hm := F.sides_mem4 hy
  exact ⟨_, hm, mem_rightCol.2 ⟨F.sub_R 4 hm, by simp only; omega⟩⟩

private theorem Frame5.sides_meets_top (F : Frame5 P p q a b t o x5 y5)
    (h : y5 + (o 4).H p q = b) : Meets (t 4) (side a b 2) := by
  obtain ⟨x, hx⟩ := sides_exists_row_last F.left F.right F.bottom F.top (o 4)
  have hm := F.sides_mem4 hx
  exact ⟨_, hm, mem_topRow.2 ⟨F.sub_R 4 hm, by simp only; omega⟩⟩

private theorem Frame5.sides_meets_left (F : Frame5 P p q a b t o x5 y5) (h : x5 = 0) :
    Meets (t 4) (side a b 3) := by
  obtain ⟨y, hy⟩ := sides_exists_col_first F.left F.right F.bottom F.top (o 4)
  have hm := F.sides_mem4 hy
  exact ⟨_, hm, mem_leftCol.2 ⟨F.sub_R 4 hm, by simp only; omega⟩⟩

/-- A frame whose `T_5` meets the bottom side is in pattern O. -/
private theorem Frame5.sides_patternO (F : Frame5 P p q a b t o x5 y5) (h : y5 = 0) :
    FrameO P p q a b t o x5 y5 := by
  have hs := F.sides_one_side
  have hb := F.box4_in
  have h0 := F.sides_meets_bottom h
  refine ⟨F, h, ?_, ?_, ?_⟩
  · by_contra hc
    exact hs ⟨0, 3, by decide, h0, F.sides_meets_left (by omega)⟩
  · by_contra hc
    exact hs ⟨0, 1, by decide, h0, F.sides_meets_right (by omega)⟩
  · by_contra hc
    exact hs ⟨0, 2, by decide, h0, F.sides_meets_top (by omega)⟩

/-- After a symmetry of the grid (which may exchange `a` and `b`) one of the two
patterns holds. Source: `report-A2.md`, section 1.1 ("By (F3), after a symmetry
of the grid (which may exchange a and b), one of two patterns holds"); (F3) is
`free_tile_one_side`. -/
theorem Frame5.pattern (F : Frame5 P p q a b t o x5 y5) :
    ∃ (a' b' : ℤ) (t' : Fin 5 → Finset Cell) (o' : Fin 5 → Orient) (x5' y5' : ℤ),
      FrameN P p q a' b' t' o' x5' y5' ∨ FrameO P p q a' b' t' o' x5' y5' := by
  have hb := F.box4_in
  by_cases h0 : y5 = 0
  · exact ⟨a, b, t, o, x5, y5, Or.inr (F.sides_patternO h0)⟩
  by_cases h2 : y5 + (o 4).H p q = b
  · obtain ⟨t', F'⟩ := F.flipY
    exact ⟨a, b, t', _, _, _, Or.inr (F'.sides_patternO (by omega))⟩
  by_cases h3 : x5 = 0
  · obtain ⟨t', F'⟩ := F.transpose
    exact ⟨b, a, t', _, _, _, Or.inr (F'.sides_patternO h3)⟩
  by_cases h1 : x5 + (o 4).W p q = a
  · obtain ⟨t', F'⟩ := F.flipX
    obtain ⟨t'', F''⟩ := F'.transpose
    exact ⟨b, a, t'', _, _, _, Or.inr (F''.sides_patternO (by omega))⟩
  exact ⟨a, b, t, o, x5, y5, Or.inl ⟨F, by omega, by omega, by omega, by omega⟩⟩

/-- A 5-copy tiling in case (I) gives a frame in pattern N or in pattern O. -/
theorem exists_frame {P : Finset Cell} (hP : IsPolyomino P) (hnr : ¬ IsRectangular P)
    {a b : ℤ} {t : Fin 5 → Finset Cell} (ht : IsTiling P a b t)
    (hI : CornersInDistinctTiles a b t) :
    ∃ (P' : Finset Cell) (p q a' b' : ℤ) (t' : Fin 5 → Finset Cell) (o : Fin 5 → Orient)
      (x5 y5 : ℤ), FrameN P' p q a' b' t' o x5 y5 ∨ FrameO P' p q a' b' t' o x5 y5 := by
  obtain ⟨P', p, q, t', o, x5, y5, F⟩ := Frame5.exists_of_tiling hP hnr ht hI
  obtain ⟨a', b', t'', o', x5', y5', h⟩ := F.pattern
  exact ⟨P', p, q, a', b', t'', o', x5', y5', h⟩

end PolyominoOddOrder
