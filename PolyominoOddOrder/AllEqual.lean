module

public import PolyominoOddOrder.Frame5Lemmas

/-!
# Case (I), all marks equal (`AllEqual.lean`)

Blueprint unit C1 (third increment), with `FourCorners.lean`. `report-A2.md`,
section 3: if the four corner tiles have the same mark, then in pattern N all
four corners of `box(P)` are occupied (3.1), and in pattern O the polyomino has
a reflection in an axis-parallel line as a symmetry (3.2).

The report's `e_i` (which direction of `box(P)` is horizontal at `T_i`) is
`(o i).swap`; with equal marks, `e_i = e_j` is `o i = o j`
(`SameMarks.eq_of_swap`).

Entry statements (binding): `allEqual_N`, `allEqual_O`. The other nodes are the
steps of the report; a proof unit may reshape those marked PROVISIONAL.

Source: `theoretician/report-A2.md` (goals lab, commit `076d663`), section 3.
-/

@[expose] public section

namespace PolyominoOddOrder

open Orient (cornerP)

variable {P : Finset Cell} {p q a b : ℤ} {t : Fin 5 → Finset Cell} {o : Fin 5 → Orient}
  {x5 y5 : ℤ}

/-! ## 3.1 Pattern N -/

/-- `report-A2.md`, 3.1 (ii): `e_1 = e_3`, `e_2 = e_4`, `e_1 ≠ e_2`. By (1)
`a = u + v = b`, the quarter turn of `R a b` takes each corner tile to the next
one, and (T4) gives `|S| = 4`. -/
theorem n31_ii (F : FrameN P p q a b t o x5 y5) (hm : SameMarks o)
    (h02 : (o 0).swap = (o 2).swap) (h13 : (o 1).swap = (o 3).swap)
    (h01 : (o 0).swap ≠ (o 1).swap) : Four P p q := by
  have e2 : o 2 = o 0 := hm.eq_of_swap (by decide) (by decide) h02.symm
  have e3 : o 3 = o 1 := hm.eq_of_swap (by decide) (by decide) h13.symm
  have e1 : o 1 = (o 0).tr := by
    obtain ⟨hx, hy⟩ := hm 1 (by decide)
    apply Orient.ext
    · revert h01
      simp only [Orient.tr_swap]
      cases (o 0).swap <;> cases (o 1).swap <;> simp
    · simpa using hx
    · simpa using hy
  have hab : a = b := by
    have hb := F.side_bottom
    have hl := F.side_left
    rw [e1, Orient.rowLine_tr] at hb
    rw [e3, e1, Orient.colLine_tr] at hl
    omega
  obtain ⟨hpq, hQ⟩ := F.toFrame5.T4_quarter hab e1 e2 e3
  exact Four.of_quarter hpq (F.toFrame5.mark_mem (i := 0) (by decide)) hQ

/-- `report-A2.md`, 3.1 (iii): all `e_i` equal. The two reflections of `R a b`
in its midlines permute the corner tiles; by (T4) `S` is invariant under both
reflections of `box(P)`. -/
theorem n31_iii (F : FrameN P p q a b t o x5 y5) (hm : SameMarks o)
    (h : ∀ i : Fin 5, i ≠ 4 → (o i).swap = (o 0).swap) : Four P p q := by
  have e1 : o 0 = o 1 := hm.eq_of_swap (by decide) (by decide) (h 1 (by decide)).symm
  have e2 : o 0 = o 2 := hm.eq_of_swap (by decide) (by decide) (h 2 (by decide)).symm
  have e3 : o 0 = o 3 := hm.eq_of_swap (by decide) (by decide) (h 3 (by decide)).symm
  obtain ⟨-, hX⟩ := F.toFrame5.T4_flipX e1 (e2.symm.trans e3)
  obtain ⟨-, hY⟩ := F.toFrame5.T4_flipY e3 (e1.symm.trans e2)
  have h0 := F.toFrame5.mark_mem (i := 0) (by decide)
  cases h4 : (o 4).swap
  · exact Four.of_reflections h0 (fun c => by simpa [h4] using hX c)
      (fun c => by simpa [h4] using hY c)
  · exact Four.of_reflections h0 (fun c => by simpa [h4] using hY c)
      (fun c => by simpa [h4] using hX c)

/-- `report-A2.md`, 3.1 (iv), first half ("Otherwise ... So box(P) is u x u, the
two corners next to m are occupied, and the boxes of T_1, ..., T_4 are the four
quadrants of R"). If the `e_i` are neither as in (ii) nor as in (iii), the side
equations (1) give `u = v` and `a = b = 2u`, and (i) (that is (T1) at the sides
whose two tiles have the same `e`) gives that both runs of the mark are whole
sides. The six remaining patterns of `e` each have two such sides, one for each
direction of `box(P)`. -/
theorem n31_iv_square (F : FrameN P p q a b t o x5 y5) (hm : SameMarks o)
    (hne : ¬ ((o 0).swap = (o 2).swap ∧ (o 1).swap = (o 3).swap)) :
    p = q ∧ a = 2 * p ∧ b = 2 * p ∧ (o 0).rowLine p q P 0 = (o 0).W p q ∧
      (o 0).colLine p q P 0 = (o 0).H p q := by
  -- with equal marks a corner tile has the code of `T_1` or its transpose
  have hcode : ∀ i : Fin 5, i ≠ 4 → o i = o 0 ∨ o i = (o 0).tr := by
    intro i hi
    obtain ⟨hx, hy⟩ := hm i hi
    by_cases h : (o i).swap = (o 0).swap
    · exact Or.inl (Orient.ext h hx hy)
    · refine Or.inr (Orient.ext ?_ hx hy)
      rw [Orient.tr_swap]
      revert h
      cases (o i).swap <;> cases (o 0).swap <;> simp
  have hb := F.side_bottom
  have ht := F.side_top
  have hl := F.side_left
  have hr := F.side_right
  have T1b := F.toFrame5.T1_bottom F.y5_pos
  have T1t := F.toFrame5.T1_top F.y5_le
  have T1l := F.toFrame5.T1_left F.x5_pos
  have T1r := F.toFrame5.T1_right F.x5_le
  have hWH : ((o 0).W p q = p ∧ (o 0).H p q = q) ∨ ((o 0).W p q = q ∧ (o 0).H p q = p) := by
    unfold Orient.W Orient.H
    cases (o 0).swap <;> simp
  have htr : (o 0 = (o 0).tr) = False := eq_false fun h => by
    have h' := congrArg Orient.swap h
    rw [Orient.tr_swap] at h'
    revert h'
    cases (o 0).swap <;> simp
  have htr' : ((o 0).tr = o 0) = False := by rw [← htr]; exact propext eq_comm
  -- the eight positions of the codes of `T_2, T_3, T_4`: `hne` excludes two; in
  -- the other six, (1) gives `u = v` and (T1) applies at one horizontal and one
  -- vertical side
  rcases hcode 1 (by decide) with e1 | e1 <;> rcases hcode 2 (by decide) with e2 | e2 <;>
    rcases hcode 3 (by decide) with e3 | e3 <;>
    simp only [e1, e2, e3, Orient.tr_swap, Orient.rowLine_tr, Orient.colLine_tr, Orient.W_tr,
      Orient.H_tr, forall_const, htr, htr', false_implies, and_self, not_true_eq_false]
      at hne hb ht hl hr T1b T1t T1l T1r <;>
    rcases hWH with ⟨hW, hH⟩ | ⟨hW, hH⟩ <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- A code whose mark is `(0, 0)` reads `box(P)` directly or transposed. -/
private theorem back_ff {c : Orient} (hx : c.negX = false) (hy : c.negY = false) (p q : ℤ)
    (d : Cell) : c.back p q d = if c.swap then (d.2, d.1) else d := by
  rcases c with ⟨_ | _, nx, ny⟩ <;> simp only at hx hy <;> subst hx hy <;> simp [Orient.back]

/-- The inverse of `back_ff`. -/
private theorem fwd_ff {c : Orient} (hx : c.negX = false) (hy : c.negY = false) (p q : ℤ)
    (d : Cell) : c.fwd p q d = if c.swap then (d.2, d.1) else d := by
  rcases c with ⟨_ | _, nx, ny⟩ <;> simp only at hx hy <;> subst hx hy <;> simp [Orient.fwd]

/-! ### 3.1 (iv), second half: the cell argument

The setting of `n31_iv_three_ll` after `q = p` and `a = b = 2 p` (the report's
`k` is `p`): the boxes of the corner tiles are the quadrants `Q_1, ..., Q_4` of
`R a b`, and a code whose mark is `(0, 0)` reads `box(P)` directly or
transposed (`back_ff`). -/

private theorem ll_W (c : Orient) (p : ℤ) : c.W p p = p := ite_self p

private theorem ll_H (c : Orient) (p : ℤ) : c.H p p = p := ite_self p

/-- 3.1 (iv), step (1): "T_i misses the corner of its quadrant Q_i at the
centre of R"; for `T_1` this is the cell `(k - 1, k - 1)`, so it lies in `T_5`
and `x5, y5 ≤ k - 1`. -/
private theorem ll_centre (F : FrameN P p p (2 * p) (2 * p) t o x5 y5)
    (h0 : (o 0).negX = false ∧ (o 0).negY = false) (hD : ((p - 1, p - 1) : Cell) ∉ P) :
    x5 ≤ p - 1 ∧ y5 ≤ p - 1 := by
  have hp := F.toFrame5.two_le_p
  rcases F.toFrame5.cover_cases (c := (p - 1, p - 1)) (mem_R.2 (by omega)) with
    h | h | h | h | h <;> simp only [ll_W, ll_H] at h
  · have h' := (F.toFrame5.mem0 _).1 h.1
    rw [back_ff h0.1 h0.2] at h'
    split at h' <;> exact (hD h').elim
  all_goals omega

/-- 3.1 (iv): "the two corners next to m are occupied", so the runs of the mark
are whole sides: row 0 and column 0 of `P` are full. -/
private theorem ll_full (F : Frame5 P p p a b t o x5 y5)
    (h0 : (o 0).negX = false ∧ (o 0).negY = false) (hA : ((p - 1, 0) : Cell) ∈ P)
    (hB : ((0, p - 1) : Cell) ∈ P) :
    ∀ x, 0 ≤ x → x < p → ((x, 0) : Cell) ∈ P ∧ ((0, x) : Cell) ∈ P := by
  have hu : (o 0).rowLine p p P 0 = (o 0).W p p := F.hrun_of_far (i := 0) (by decide) (by
    cases hs : (o 0).swap <;> simp [cornerP, h0.1, h0.2, hA, hB])
  have hv : (o 0).colLine p p P 0 = (o 0).H p p := F.vrun_of_far (i := 0) (by decide) (by
    cases hs : (o 0).swap <;> simp [cornerP, h0.1, h0.2, hA, hB])
  intro x hx0 hx1
  have e1 := (F.hside (i := 0) (by decide) x).2 ⟨hx0, by rw [hu, ll_W]; exact hx1⟩
  have e2 := (F.vside (i := 0) (by decide) x).2 ⟨hx0, by rw [hv, ll_H]; exact hx1⟩
  rw [back_ff h0.1 h0.2] at e1 e2
  cases hs : (o 0).swap <;> simp only [hs, ↓reduceIte, Bool.false_eq_true] at e1 e2
  · exact ⟨e1, e2⟩
  · exact ⟨e2, e1⟩

/-- 3.1 (iv), step (2): "T_5 contains {x_5} x [y_5, y_5+k) and
[x_5, x_5+k) x {y_5}". -/
private theorem ll_seg (F : Frame5 P p p a b t o x5 y5)
    (h4 : (o 4).negX = false ∧ (o 4).negY = false)
    (hrow : ∀ x, 0 ≤ x → x < p → ((x, 0) : Cell) ∈ P ∧ ((0, x) : Cell) ∈ P) :
    ∀ c : Cell, (c.2 = y5 ∧ x5 ≤ c.1 ∧ c.1 < x5 + p) ∨
      (c.1 = x5 ∧ y5 ≤ c.2 ∧ c.2 < y5 + p) → c ∈ t 4 := by
  rintro ⟨cx, cy⟩ h
  rw [F.mem4, back_ff h4.1 h4.2]
  simp only at h ⊢
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · obtain ⟨r1, r2⟩ := hrow (cx - x5) (by omega) (by omega)
    rw [h1, sub_self]
    split <;> simp [r1, r2]
  · obtain ⟨r1, r2⟩ := hrow (cy - y5) (by omega) (by omega)
    rw [h1, sub_self]
    split <;> simp [r1, r2]

/-- 3.1 (iv), step (3): "T_1 is connected, contains (0, 0), and to reach a cell
with x >= x_5 and y >= y_5 it would have to enter a cell of one of these two
segments". -/
private theorem ll_miss (F : FrameN P p p a b t o x5 y5)
    (hseg : ∀ c : Cell, (c.2 = y5 ∧ x5 ≤ c.1 ∧ c.1 < x5 + p) ∨
      (c.1 = x5 ∧ y5 ≤ c.2 ∧ c.2 < y5 + p) → c ∈ t 4) :
    ∀ c ∈ t 0, ¬ (x5 ≤ c.1 ∧ y5 ≤ c.2) := by
  have hx5 := F.x5_pos
  have hy5 := F.y5_pos
  intro c hc hcA
  obtain ⟨⟨ux, uy⟩, ⟨vx, vy⟩, -, hv, hadj, hAu, hAv⟩ :=
    (F.toFrame5.conn 0).exists_adj_leaving (fun c : Cell => ¬ (x5 ≤ c.1 ∧ y5 ≤ c.2))
      F.toFrame5.corner0 hc (show ¬ (x5 ≤ 0 ∧ y5 ≤ 0) by omega) (fun h => h hcA)
  have hb0 := F.toFrame5.box0 hv
  rw [ll_W, ll_H] at hb0
  simp only [adj_iff] at hadj
  simp only [not_not] at hAu hAv
  have h4v : ((vx, vy) : Cell) ∈ t 4 := hseg _ (by simp only; omega)
  exact absurd (F.toFrame5.tile_unique hv h4v) (by decide)

/-- 3.1 (iv), steps (3) and (4): "Q_1 \ T_1 = D_1, as T_5 is in its box", so `P`
is `box(P)` without `D_1` read through the code of `T_1`; written for the
cell at the local position `(x, y)` of a box of any code. -/
private theorem ll_desc (F : FrameN P p p (2 * p) (2 * p) t o x5 y5)
    (hmiss : ∀ c ∈ t 0, ¬ (x5 ≤ c.1 ∧ y5 ≤ c.2)) :
    ∀ (c : Orient) (x y : ℤ), 0 ≤ x → x < p → 0 ≤ y → y < p →
      (c.back p p (x, y) ∈ P ↔ ¬ (x5 ≤ ((o 0).fwd p p (c.back p p (x, y))).1 ∧
        y5 ≤ ((o 0).fwd p p (c.back p p (x, y))).2)) := by
  have hP0 : ∀ c : Cell, c ∈ R p p → ((o 0).back p p c ∈ P ↔ ¬ (x5 ≤ c.1 ∧ y5 ≤ c.2)) := by
    intro c hc
    rw [← F.toFrame5.mem0]
    obtain ⟨⟨c1, c2⟩, c3, c4⟩ := mem_R.1 hc
    refine ⟨hmiss c, fun hn => ?_⟩
    rcases F.toFrame5.cover_cases (c := c) (mem_R.2 (by omega)) with h | h | h | h | h <;>
      simp only [ll_W, ll_H] at h
    · exact h.1
    all_goals omega
  intro c x y h1 h2 h3 h4
  have hc := (Orient.back_mem_R c p p (x, y)).2 ⟨⟨h1, by rw [ll_W]; exact h2⟩, h3,
    by rw [ll_H]; exact h4⟩
  have hf := (Orient.back_mem_R (o 0) p p ((o 0).fwd p p (c.back p p (x, y)))).1
    (by rw [Orient.back_fwd]; exact hc)
  rw [ll_W, ll_H] at hf
  have h' := hP0 _ (mem_R.2 hf)
  rwa [Orient.back_fwd] at h'

/-- 3.1 (iv), step (5), in `Q_2`: "Q_2 \ T_2 has y_5 as its lowest row" and "row
y_5 of T_5 is [x_5, x_5+k)": the cells `(k, y5 - 1)` and `(k + x5, y5)` lie in
`T_2`, the cell `(k + x5 - 1, y5)` does not. -/
private theorem ll_Q2 (F : FrameN P p p (2 * p) (2 * p) t o x5 y5)
    (hc1 : x5 ≤ p - 1 ∧ y5 ≤ p - 1)
    (hseg : ∀ c : Cell, (c.2 = y5 ∧ x5 ≤ c.1 ∧ c.1 < x5 + p) ∨
      (c.1 = x5 ∧ y5 ≤ c.2 ∧ c.2 < y5 + p) → c ∈ t 4) :
    ((p, y5 - 1) : Cell) ∈ t 1 ∧ ((p + x5, y5) : Cell) ∈ t 1 ∧
      ((p + x5 - 1, y5) : Cell) ∉ t 1 := by
  have hp := F.toFrame5.two_le_p
  have hx5 := F.x5_pos
  have hy5 := F.y5_pos
  refine ⟨?_, ?_, fun h => absurd (F.toFrame5.tile_unique h
    (hseg _ (Or.inl ⟨rfl, by dsimp only; omega, by dsimp only; omega⟩))) (by decide)⟩
  · rcases F.toFrame5.cover_cases (c := (p, y5 - 1)) (mem_R.2 (by omega)) with
      h | h | h | h | h <;> simp only [ll_W, ll_H] at h
    all_goals first | exact h.1 | omega
  · rcases F.toFrame5.cover_cases (c := (p + x5, y5)) (mem_R.2 (by omega)) with
      h | h | h | h | h <;> simp only [ll_W, ll_H] at h
    all_goals first | exact h.1 | omega

/-- 3.1 (iv), step (5), in `Q_4` ("in the same way (with Q_4)"): the cells
`(x5 - 1, k)` and `(x5, k + y5)` lie in `T_4`, the cell `(x5, k + y5 - 1)` does
not. -/
private theorem ll_Q4 (F : FrameN P p p (2 * p) (2 * p) t o x5 y5)
    (hc1 : x5 ≤ p - 1 ∧ y5 ≤ p - 1)
    (hseg : ∀ c : Cell, (c.2 = y5 ∧ x5 ≤ c.1 ∧ c.1 < x5 + p) ∨
      (c.1 = x5 ∧ y5 ≤ c.2 ∧ c.2 < y5 + p) → c ∈ t 4) :
    ((x5 - 1, p) : Cell) ∈ t 3 ∧ ((x5, p + y5) : Cell) ∈ t 3 ∧
      ((x5, p + y5 - 1) : Cell) ∉ t 3 := by
  have hp := F.toFrame5.two_le_p
  have hx5 := F.x5_pos
  have hy5 := F.y5_pos
  refine ⟨?_, ?_, fun h => absurd (F.toFrame5.tile_unique h
    (hseg _ (Or.inr ⟨rfl, by dsimp only; omega, by dsimp only; omega⟩))) (by decide)⟩
  · rcases F.toFrame5.cover_cases (c := (x5 - 1, p)) (mem_R.2 (by omega)) with
      h | h | h | h | h <;> simp only [ll_W, ll_H] at h
    all_goals first | exact h.1 | omega
  · rcases F.toFrame5.cover_cases (c := (x5, p + y5)) (mem_R.2 (by omega)) with
      h | h | h | h | h <;> simp only [ll_W, ll_H] at h
    all_goals first | exact h.1 | omega

/-- 3.1 (iv), step (6): the corner `(k, k)` of `Q_3` at the centre is not in
`T_3`, so it is a cell of `T_5`. -/
private theorem ll_Q3 (F : FrameN P p p (2 * p) (2 * p) t o x5 y5)
    (h2 : (o 2).negX = false ∧ (o 2).negY = false) (hD : ((p - 1, p - 1) : Cell) ∉ P) :
    (o 4).back p p (p - x5, p - y5) ∈ P := by
  have hp := F.toFrame5.two_le_p
  rcases F.toFrame5.cover_cases (c := (p, p)) (mem_R.2 (by omega)) with h | h | h | h | h <;>
    simp only [ll_W, ll_H] at h
  · omega
  · omega
  · have h' := (F.toFrame5.mem2 _).1 h.1
    rw [back_ff h2.1 h2.2] at h'
    have e : 2 * p - 1 - p = p - 1 := by ring
    split at h' <;> simp only [e] at h' <;> exact (hD h').elim
  · omega
  · exact (F.toFrame5.mem4 _).1 h.1

/-- `report-A2.md`, 3.1 (iv), second half ("Suppose |S| = 3. Put k = u ...
P is a rectangle. Contradiction."), after the reflection of `R a b` that puts
the two full sides of `T_5` at the lower left corner of its box. The marks are
the corner `(0, 0)` of `box(P)`; `box(P)` is `k x k`, `R a b` is `2k x 2k`, the
boxes of the corner tiles are the quadrants, and the two corners next to the
mark are occupied. Then the fourth corner is occupied.

Steps of the report: (1) `T_5` is the union of the sets `Q_i \ T_i`, and
`1 ≤ x5, y5 ≤ k - 1`; (2) `T_5` contains `{x5} x [y5, y5 + k)` and
`[x5, x5 + k) x {y5}`; (3) `Q_1 \ T_1 = [x5, k) x [y5, k)` (a path of `T_1` from
`(0, 0)` cannot pass the two segments); (4) every `Q_i \ T_i` is a rectangle
with sides `k - x5`, `k - y5` at the centre; (5) from `Q_2` and `Q_4`,
`k = 2 x5 = 2 y5`; (6) `T_5` is a `k x k` square, so `P` is a rectangle.
PROVISIONAL: the unit may split this node along these steps.

Route of the proof: steps (1) to (3) are `ll_centre`, `ll_full`, `ll_seg`,
`ll_miss`; with them `P` is `box(P)` without `D_1` read through the code of
`T_1` (`ll_desc`). Instead of the shapes of all four sets `Q_i \ T_i`, three
cells of `Q_2` (`ll_Q2`) and three of `Q_4` (`ll_Q4`) give `k = 2 x5 = 2 y5`
as linear conditions, and the contradiction is the centre cell `(k, k)`: it is
a cell of `T_5` (`ll_Q3`), but its place in `T_5` is a cell of `D_1`. -/
theorem n31_iv_three_ll (F : FrameN P p q a b t o x5 y5)
    (hm0 : ∀ i : Fin 5, i ≠ 4 → (o i).negX = false ∧ (o i).negY = false) (hpq : p = q)
    (ha : a = 2 * p) (hb : b = 2 * p) (hA : ((p - 1, 0) : Cell) ∈ P)
    (hB : ((0, q - 1) : Cell) ∈ P) (h4 : (o 4).negX = false ∧ (o 4).negY = false) :
    ((p - 1, q - 1) : Cell) ∈ P := by
  subst hpq ha hb
  have G := F.toFrame5
  obtain ⟨h0x, h0y⟩ := hm0 0 (by decide)
  obtain ⟨h1x, h1y⟩ := hm0 1 (by decide)
  obtain ⟨h3x, h3y⟩ := hm0 3 (by decide)
  have hp := G.two_le_p
  have hx5 := F.x5_pos
  have hy5 := F.y5_pos
  by_contra hD
  have hc1 := ll_centre F (hm0 0 (by decide)) hD
  have hseg := ll_seg G h4 (ll_full G (hm0 0 (by decide)) hA hB)
  have hP := ll_desc F (ll_miss F hseg)
  obtain ⟨hA1, hA2, hA3⟩ := ll_Q2 F hc1 hseg
  obtain ⟨hB1, hB2, hB3⟩ := ll_Q4 F hc1 hseg
  have hC := ll_Q3 F (hm0 2 (by decide)) hD
  -- each cell gives a linear condition through the description of `P`
  have m1 := (G.mem1 _).1 hA1
  have m2 := (G.mem1 _).1 hA2
  have m3 := mt (G.mem1 _).2 hA3
  have m4 := (G.mem3 _).1 hB1
  have m5 := (G.mem3 _).1 hB2
  have m6 := mt (G.mem3 _).2 hB3
  simp only at m1 m2 m3 m4 m5 m6
  have k1 := (hP _ _ _ (by omega) (by omega) (by omega) (by omega)).1 m1
  have k2 := (hP _ _ _ (by omega) (by omega) (by omega) (by omega)).1 m2
  have k3 := not_not.1 (mt (hP _ _ _ (by omega) (by omega) (by omega) (by omega)).2 m3)
  have k4 := (hP _ _ _ (by omega) (by omega) (by omega) (by omega)).1 m4
  have k5 := (hP _ _ _ (by omega) (by omega) (by omega) (by omega)).1 m5
  have k6 := not_not.1 (mt (hP _ _ _ (by omega) (by omega) (by omega) (by omega)).2 m6)
  have k7 := (hP _ _ _ (by omega) (by omega) (by omega) (by omega)).1 hC
  -- the sixteen positions of the codes of `T_1, T_2, T_4, T_5`: in each, `Q_2` gives
  -- `k = 2 x5` or `x5 = y5`, `Q_4` gives `k = 2 y5` or `x5 = y5`, and then the
  -- centre `(k, k)` lies in `D` read through `T_5`
  clear hP hseg hA1 hA2 hA3 hB1 hB2 hB3 hC m1 m2 m3 m4 m5 m6
  simp only [fwd_ff h0x h0y, back_ff h1x h1y, back_ff h3x h3y, back_ff h4.1 h4.2]
    at k1 k2 k3 k4 k5 k6 k7
  cases hs0 : (o 0).swap <;> cases hs1 : (o 1).swap <;> cases hs3 : (o 3).swap <;>
    cases hs4 : (o 4).swap <;>
    simp only [hs0, hs1, hs3, hs4, ↓reduceIte, Bool.false_eq_true] at k1 k2 k3 k4 k5 k6 k7 <;>
    omega

/-- `n31_iv_three_ll` without the condition on the second switch of `T_5`: a
reflection of `R a b` reverses the second direction of `box(P)` in `T_5`
(`report-A2.md`, 3.1 (iv): "reflect R so that it is the lower left one"). -/
theorem n31_iv_three_x (F : FrameN P p q a b t o x5 y5)
    (hm0 : ∀ i : Fin 5, i ≠ 4 → (o i).negX = false ∧ (o i).negY = false) (hpq : p = q)
    (ha : a = 2 * p) (hb : b = 2 * p) (hA : ((p - 1, 0) : Cell) ∈ P)
    (hB : ((0, q - 1) : Cell) ∈ P) (h4 : (o 4).negX = false) :
    ((p - 1, q - 1) : Cell) ∈ P := by
  cases hy : (o 4).negY
  · exact n31_iv_three_ll F hm0 hpq ha hb hA hB ⟨h4, hy⟩
  · cases hs : (o 4).swap
    · obtain ⟨t', F'⟩ := F.flipY
      refine n31_iv_three_ll F'
        (marks_perm hm0 3 2 1 0 (by decide) (by decide) (by decide) (by decide) _)
        hpq ha hb hA hB ?_
      simp [Orient.reflY, hs, h4, hy]
    · obtain ⟨t', F'⟩ := F.flipX
      refine n31_iv_three_ll F'
        (marks_perm hm0 1 0 3 2 (by decide) (by decide) (by decide) (by decide) _)
        hpq ha hb hA hB ?_
      simp [Orient.reflX, hs, h4, hy]

/-- `report-A2.md`, 3.1 (iv), second half, for any position of `T_5`: with all
marks at `(0, 0)`, a `k x k` box in a `2k x 2k` rectangle and the two corners
next to the mark occupied, the fourth corner is occupied. -/
theorem n31_iv_three (F : FrameN P p q a b t o x5 y5)
    (hm0 : ∀ i : Fin 5, i ≠ 4 → (o i).negX = false ∧ (o i).negY = false) (hpq : p = q)
    (ha : a = 2 * p) (hb : b = 2 * p) (hA : ((p - 1, 0) : Cell) ∈ P)
    (hB : ((0, q - 1) : Cell) ∈ P) : ((p - 1, q - 1) : Cell) ∈ P := by
  cases hx : (o 4).negX
  · exact n31_iv_three_x F hm0 hpq ha hb hA hB hx
  · cases hs : (o 4).swap
    · obtain ⟨t', F'⟩ := F.flipX
      refine n31_iv_three_x F'
        (marks_perm hm0 1 0 3 2 (by decide) (by decide) (by decide) (by decide) _)
        hpq ha hb hA hB ?_
      simp [Orient.reflX, hs, hx]
    · obtain ⟨t', F'⟩ := F.flipY
      refine n31_iv_three_x F'
        (marks_perm hm0 3 2 1 0 (by decide) (by decide) (by decide) (by decide) _)
        hpq ha hb hA hB ?_
      simp [Orient.reflY, hs, hx]

/-- `report-A2.md`, 3.1, with the marks at the corner `(0, 0)` of `box(P)`. -/
theorem allEqual_N_norm (F : FrameN P p q a b t o x5 y5)
    (hm0 : ∀ i : Fin 5, i ≠ 4 → (o i).negX = false ∧ (o i).negY = false) : Four P p q := by
  have hm : SameMarks o := fun i hi => by
    obtain ⟨h1, h2⟩ := hm0 i hi
    obtain ⟨h3, h4⟩ := hm0 0 (by decide)
    exact ⟨h1.trans h3.symm, h2.trans h4.symm⟩
  by_cases hne : (o 0).swap = (o 2).swap ∧ (o 1).swap = (o 3).swap
  · by_cases h01 : (o 0).swap = (o 1).swap
    · refine n31_iii F hm fun i hi => ?_
      fin_cases i
      · rfl
      · exact h01.symm
      · exact hne.1.symm
      · exact (h01.trans hne.2).symm
      · exact absurd rfl hi
    · exact n31_ii F hm hne.1 hne.2 h01
  · obtain ⟨hpq, ha, hb, hu, hv⟩ := n31_iv_square F hm hne
    obtain ⟨h0x, h0y⟩ := hm0 0 (by decide)
    have h00 : ((0, 0) : Cell) ∈ P := by
      have h := F.toFrame5.mark_mem (i := 0) (by decide)
      simpa [cornerP, h0x, h0y] using h
    have hfh := F.toFrame5.far_h (i := 0) (by decide) hu
    have hfv := F.toFrame5.far_v (i := 0) (by decide) hv
    have hAB : ((p - 1, 0) : Cell) ∈ P ∧ ((0, q - 1) : Cell) ∈ P := by
      cases hs : (o 0).swap
      · exact ⟨by simpa [cornerP, h0x, h0y, hs] using hfh,
          by simpa [cornerP, h0x, h0y, hs] using hfv⟩
      · exact ⟨by simpa [cornerP, h0x, h0y, hs] using hfv,
          by simpa [cornerP, h0x, h0y, hs] using hfh⟩
    exact ⟨h00, hAB.1, hAB.2, n31_iv_three F hm0 hpq ha hb hAB.1 hAB.2⟩

/-- `allEqual_N` when the first switch of the marks is already off; the second
is turned off by the mirror image of `P` in the horizontal midline of its box. -/
theorem allEqual_N_x (F : FrameN P p q a b t o x5 y5) (hm : SameMarks o)
    (hx : (o 0).negX = false) : Four P p q := by
  cases hy : (o 0).negY
  · exact allEqual_N_norm F fun i hi => ⟨(hm i hi).1.trans hx, (hm i hi).2.trans hy⟩
  · refine Four.of_flipPY (allEqual_N_norm F.flipPY fun i hi => ?_)
    simp [(hm i hi).1, (hm i hi).2, hx, hy]

/-- **`report-A2.md`, 3.1.** Pattern N with all marks equal: `|S| = 4`. The mark
is moved to the corner `(0, 0)` of `box(P)` by the mirror images of `P`
(`FrameN.flipPX`, `FrameN.flipPY`). -/
theorem allEqual_N (F : FrameN P p q a b t o x5 y5) (hm : SameMarks o) : Four P p q := by
  cases hx : (o 0).negX
  · exact allEqual_N_x F hm hx
  · refine Four.of_flipPX (allEqual_N_x F.flipPX (fun i hi => ?_) (by simp [hx]))
    simp [(hm i hi).1, (hm i hi).2]

/-! ## 3.2 Pattern O -/

/-- `report-A2.md`, 3.2, the count: with equal marks in pattern O the side
equations (1) force `e_1 = e_2` and `e_3 = e_4`. Of the 8 positions of
`e_2, e_3, e_4` relative to `e_1`, seven contradict (1) with `mu ≥ 1`. -/
theorem allEqual_O_codes (F : FrameO P p q a b t o x5 y5) (hm : SameMarks o) :
    o 0 = o 1 ∧ o 2 = o 3 := by
  have hb := F.side_bottom
  have ht := F.side_top
  have hl := F.side_left
  have hr := F.side_right
  have hmu := F.mu_pos
  obtain ⟨h1x, h1y⟩ := hm 1 (by decide)
  obtain ⟨h2x, h2y⟩ := hm 2 (by decide)
  obtain ⟨h3x, h3y⟩ := hm 3 (by decide)
  rw [Orient.rowLine_zero_of_marks h1x h1y] at hb
  rw [Orient.rowLine_zero_of_marks h2x h2y, Orient.rowLine_zero_of_marks h3x h3y] at ht
  rw [Orient.colLine_zero_of_marks h3x h3y] at hl
  rw [Orient.colLine_zero_of_marks h1x h1y, Orient.colLine_zero_of_marks h2x h2y] at hr
  by_cases h1 : (o 1).swap = (o 0).swap <;> by_cases h2 : (o 2).swap = (o 0).swap <;>
    by_cases h3 : (o 3).swap = (o 0).swap <;>
    simp only [h1, h2, h3, ite_true, ite_false] at hb ht hl hr <;>
    first
    | omega
    | exact ⟨hm.eq_of_swap (by decide) (by decide) h1.symm,
        hm.eq_of_swap (by decide) (by decide) (bool_eq_of_ne h2 h3)⟩

/-- **`report-A2.md`, 3.2.** Pattern O with all marks equal: `P` has a reflection
in an axis-parallel line as a symmetry. The reflection of `R a b` in its vertical
midline exchanges `T_1`, `T_2` and `T_3`, `T_4`; apply (T4). -/
theorem allEqual_O (F : FrameO P p q a b t o x5 y5) (hm : SameMarks o) :
    (∀ c : Cell, c ∈ P ↔ (p - 1 - c.1, c.2) ∈ P) ∨
      (∀ c : Cell, c ∈ P ↔ (c.1, q - 1 - c.2) ∈ P) := by
  obtain ⟨h01, h23⟩ := allEqual_O_codes F hm
  obtain ⟨-, hsym⟩ := F.toFrame5.T4_flipX h01 h23
  cases h : (o 4).swap
  · exact Or.inl fun c => by simpa [h] using hsym c
  · exact Or.inr fun c => by simpa [h] using hsym c

end PolyominoOddOrder
