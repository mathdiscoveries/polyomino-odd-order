module

public import PolyominoOddOrder.AdjacentN

/-!
# Case (I), two adjacent occupied corners, pattern O (`AdjacentO.lean`)

Blueprint unit C6 (third increment). `report-A2.md`, section 6.3. By Lemma 6.1
at the left, the top and the right side the types of `T_1, ..., T_4` are, up to
the reflection of `R a b` in its vertical midline, `(h, v, h, v)`,
`(v, v, h, h)` or `(v, v, h, v)` (`o63_types`).

| report | Lean |
|---|---|
| type `(h, v, h, v)` | swaps `(false, true, false, true)` |
| type `(v, v, h, h)` | swaps `(true, true, false, false)` |
| type `(v, v, h, v)` | swaps `(true, true, false, true)` |
| `F` of `T_5` vertical / at the bottom / on top of `box(T_5)` | `(o 4).swap = true` / `(o 4).swap = false ∧ (o 4).negY = false` / `... ∧ (o 4).negY = true` |
| (11) | `o63_eleven` |
| (12) | `Setup12`, `o63_vvhh_12` |
| profiles are 0 outside the box | `Frame5.colCount_zero`, `Frame5.rowCount_zero` |

Entry statement (binding): `adj_O`. A proof unit may reshape the nodes marked
PROVISIONAL.

Source: `theoretician/report-A2.md` (goals lab, commit `076d663`), section 6.3.
-/

@[expose] public section

namespace PolyominoOddOrder

open Orient (cornerP)

variable {P : Finset Cell} {p q a b : ℤ} {t : Fin 5 → Finset Cell} {o : Fin 5 → Orient}
  {x5 y5 : ℤ}

/-- `report-A2.md`, 6.3, first paragraph: the types of the corner tiles, from
Lemma 6.1 at the left, the top and the right side. The second and the fifth
pattern are the mirror images of the first and the fourth. -/
theorem o63_types (F : FrameO P p q a b t o x5 y5) (S : AdjFull P p q) :
    ((o 0).swap = false ∧ (o 1).swap = true ∧ (o 2).swap = false ∧ (o 3).swap = true) ∨
    ((o 0).swap = true ∧ (o 1).swap = false ∧ (o 2).swap = true ∧ (o 3).swap = false) ∨
    ((o 0).swap = true ∧ (o 1).swap = true ∧ (o 2).swap = false ∧ (o 3).swap = false) ∨
    ((o 0).swap = true ∧ (o 1).swap = true ∧ (o 2).swap = false ∧ (o 3).swap = true) ∨
    ((o 0).swap = true ∧ (o 1).swap = true ∧ (o 2).swap = true ∧ (o 3).swap = false) := by
  have ht := lemma61_top F.toFrame5 S F.y5_le
  have hl := lemma61_left F.toFrame5 S F.x5_pos
  have hr := lemma61_right F.toFrame5 S F.x5_le
  revert ht hl hr
  cases (o 0).swap <;> cases (o 1).swap <;> cases (o 2).swap <;> cases (o 3).swap <;> simp

/-- **`report-A2.md`, 6.3, (11).** If the number of cells of `T_1, ..., T_4`
together in a column is invariant under `c ↦ a - 1 - c`, then `F` of `T_5` is
horizontal, `box(T_5)` is centred, and `X_A = X_C`. By (2) the column counts of
`T_5` are invariant; a vertical `F` would give `lambda(0) = lambda(M - 1)`, that
is `L = f`. -/
theorem o63_eleven (F : FrameO P p q a b t o x5 y5) (S : AdjFull P p q)
    (hsym : ∀ x : ℤ, 0 ≤ x → x < a →
      (o 0).colLine p q P x + (o 1).colLine p q P (a - 1 - x) +
        (o 2).colLine p q P (a - 1 - x) + (o 3).colLine p q P x =
      (o 0).colLine p q P (a - 1 - x) + (o 1).colLine p q P x + (o 2).colLine p q P x +
        (o 3).colLine p q P (a - 1 - x)) :
    (o 4).swap = false ∧ a = 2 * x5 + p ∧ ∀ c : ℤ, colCount P c = colCount P (p - 1 - c) := by
  have F' := F.toFrame5
  have hx5 := F.x5_pos
  have hx5' := F.x5_le
  have hp := F'.two_le_p
  have hq := F'.two_le_q
  -- by (2) the column counts of `T_5` are invariant
  have h5 : ∀ x : ℤ, 0 ≤ x → x < a →
      (o 4).colLine p q P (x - x5) = (o 4).colLine p q P (a - 1 - x - x5) := by
    intro x h0 h1
    have e1 := F'.col_sum h0 h1
    have e2 := F'.col_sum (x := a - 1 - x) (by omega) (by omega)
    rw [show a - 1 - (a - 1 - x) = x by ring] at e2
    have hs := hsym x h0 h1
    linarith
  have hW : 2 ≤ (o 4).W p q := by
    unfold Orient.W
    split <;> omega
  -- `box(T_5)` is centred
  have hc : a = 2 * x5 + (o 4).W p q := by
    have k1 := h5 x5 (by omega) (by omega)
    have k2 := h5 (x5 + (o 4).W p q - 1) (by omega) (by omega)
    have p1 := F'.colLine_pos (o 4) (x := 0) le_rfl (by omega)
    have p2 := F'.colLine_pos (o 4) (x := (o 4).W p q - 1) (by omega) (by omega)
    rw [sub_self] at k1
    rw [show x5 + (o 4).W p q - 1 - x5 = (o 4).W p q - 1 by ring] at k2
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have z := F'.colLine_zero (o 4)
        (x := a - 1 - (x5 + (o 4).W p q - 1) - x5) (Or.inl (by omega))
      omega
    · have z := F'.colLine_zero (o 4) (x := a - 1 - x5 - x5) (Or.inr (by omega))
      omega
  have hrev : ∀ c : ℤ, 0 ≤ c → c < (o 4).W p q →
      (o 4).colLine p q P c = (o 4).colLine p q P ((o 4).W p q - 1 - c) := by
    intro c h0 h1
    have k := h5 (x5 + c) (by omega) (by omega)
    rw [show x5 + c - x5 = c by ring,
      show a - 1 - (x5 + c) - x5 = (o 4).W p q - 1 - c by omega] at k
    exact k
  cases h4 : (o 4).swap
  · have hWp : (o 4).W p q = p := by simp [Orient.W, h4]
    refine ⟨rfl, by rw [hc, hWp], fun c => ?_⟩
    by_cases hc0 : 0 ≤ c ∧ c < p
    · have k := hrev c hc0.1 (by omega)
      rw [hWp] at k
      cases hx : (o 4).negX <;> simp [Orient.colLine, h4, hx] at k
      · exact k
      · exact k.symm
    · rw [F'.colCount_zero (x := c) (by omega), F'.colCount_zero (x := p - 1 - c) (by omega)]
  · -- a vertical `F`: the first and the last column of `T_5` are layers `0` and `M - 1`
    exfalso
    have hWq : (o 4).W p q = q := by simp [Orient.W, h4]
    have k := hrev 0 le_rfl (by omega)
    rw [hWq] at k
    have hf := S.fullF
    have hfl := S.f_le
    cases hy : (o 4).negY <;> simp [Orient.colLine, h4, hy] at k <;> omega

/-! ## Type `(h, v, h, v)` -/

/-- A corner tile of type h: its local columns are the positions from its mark. -/
private theorem oa_colLine_h {c : Orient} (hs : c.swap = false) (x : ℤ) :
    c.colLine p q P x = colCount P (if c.negX then p - 1 - x else x) := by
  simp [Orient.colLine, hs]

/-- A corner tile of type h: its local rows are the layers. -/
private theorem oa_rowLine_h {c : Orient} (hs : c.swap = false) (hy : c.negY = false) (y : ℤ) :
    c.rowLine p q P y = rowCount P y := by
  simp [Orient.rowLine, hs, hy]

/-- A corner tile of type v: its local columns are the layers. -/
private theorem oa_colLine_v {c : Orient} (hs : c.swap = true) (hy : c.negY = false) (x : ℤ) :
    c.colLine p q P x = rowCount P x := by
  simp [Orient.colLine, hs, hy]

/-- A corner tile of type v: its local rows are the positions from its mark. -/
private theorem oa_rowLine_v {c : Orient} (hs : c.swap = true) (y : ℤ) :
    c.rowLine p q P y = colCount P (if c.negX then p - 1 - y else y) := by
  simp [Orient.rowLine, hs]

/-- **`report-A2.md`, 6.3, type (h, v, h, v).** By (1) `m_4 ≠ m_2`, so `A` and `C`
are used, `r_A ≠ r_C` and `m_1 = m_3`; the column counts of the corner tiles are
symmetric, and (11) gives `r_A = X_A(0) = X_C(0) = r_C`. -/
theorem o63_hvhv (F : FrameO P p q a b t o x5 y5) (S : AdjFull P p q)
    (h0 : (o 0).swap = false) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) : False := by
  have F' := F.toFrame5
  have m0 := S.toAdjacent.mark F' (i := 0) (by decide)
  have m1 := S.toAdjacent.mark F' (i := 1) (by decide)
  have m2 := S.toAdjacent.mark F' (i := 2) (by decide)
  have m3 := S.toAdjacent.mark F' (i := 3) (by decide)
  have ht := F.side_top
  have hb := F.side_bottom
  have hl := F.side_left
  have hr := F.side_right
  have hmu := F.mu_pos
  have hF := S.fullF
  rw [oa_rowLine_h h2 m2, oa_rowLine_v h3] at ht
  rw [oa_rowLine_h h0 m0, oa_rowLine_v h1] at hb
  rw [oa_colLine_h h0, oa_colLine_v h3 m3] at hl
  rw [oa_colLine_v h1 m1, oa_colLine_h h2] at hr
  by_cases hrr : colCount P 0 = colCount P (p - 1)
  · -- `L + r_{m_4} = a = L + mu + r_{m_2}` with `r_A = r_C`
    cases hx1 : (o 1).negX <;> cases hx3 : (o 3).negX <;> simp [hx1, hx3] at ht hb <;> omega
  · -- `r_{m_1} = r_{m_3}` gives `m_1 = m_3`, and (11) gives `r_A = r_C`
    have hx02 : (o 2).negX = (o 0).negX := by
      cases hx0 : (o 0).negX <;> cases hx2 : (o 2).negX <;> simp [hx0, hx2] at hl hr <;>
        first | rfl | (exfalso; omega)
    have k := (o63_eleven F S fun x _ _ => by
      simp only [oa_colLine_h h0, oa_colLine_v h1 m1, oa_colLine_h h2, oa_colLine_v h3 m3, hx02]
      ring).2.2 0
    rw [sub_zero] at k
    exact hrr k

/-! ## Type `(v, v, h, h)` -/

/-- The facts of `report-A2.md`, 6.3, type (v, v, h, h), up to "So u_1 = u_2 = r
and mu = 2L - 2r": (1) and (12), with `r = r_A = r_C` written as
`colCount P 0`. -/
structure Setup12 (P : Finset Cell) (p q a b : ℤ) (o : Fin 5 → Orient) : Prop where
  /-- (1), top. -/
  ha : a = 2 * p
  /-- (1), left and right: `b = L + r`. -/
  hb : b = p + colCount P 0
  /-- (12): `X_C(0) = X_A(0) = r`. -/
  hr : colCount P (p - 1) = colCount P 0
  /-- (12): on the side of `box(P)` at `A` the cells of `P` are the `r` cells next
  to `F`. -/
  colA : ∀ y : ℤ, ((0, y) : Cell) ∈ P ↔ 0 ≤ y ∧ y < colCount P 0
  /-- (12): the same on the side at `C`. -/
  colC : ∀ y : ℤ, ((p - 1, y) : Cell) ∈ P ↔ 0 ≤ y ∧ y < colCount P 0
  /-- `u_1 = r`. -/
  hu1 : (o 0).rowLine p q P 0 = colCount P 0
  /-- `u_2 = r`. -/
  hu2 : (o 1).rowLine p q P 0 = colCount P 0
  /-- `mu = 2L - 2r`. -/
  hmu : (o 4).rowLine p q P 0 = 2 * p - 2 * colCount P 0
  /-- (12): if `m_3 = m_4`, then `X_A = X_C`. -/
  hsym : (o 2).negX = (o 3).negX → ∀ c : ℤ, colCount P c = colCount P (p - 1 - c)

/-- (R) for a used corner (`report-A2.md`, 1.2), at two adjacent occupied corners:
the cells of `P` on the side of `box(P)` at the mark of a corner tile,
perpendicular to `F`, are the first `r` cells from the mark. -/
private theorem oa_run (F : Frame5 P p q a b t o x5 y5) (S : Adjacent P p q) {i : Fin 5}
    (hi : i ≠ 4) (y : ℤ) :
    ((if (o i).negX then p - 1 else 0, y) : Cell) ∈ P ↔
      0 ≤ y ∧ y < colCount P (if (o i).negX then p - 1 else 0) := by
  have hy := S.mark F hi
  cases hs : (o i).swap
  · have h := F.vside hi y
    cases hx : (o i).negX <;> simpa [Orient.back, Orient.colLine, hs, hy, hx] using h
  · have h := F.hside hi y
    cases hx : (o i).negX <;> simpa [Orient.back, Orient.rowLine, hs, hy, hx] using h

/-- At two adjacent occupied corners either both `A` and `C` are used, or all
marks are equal. -/
private theorem oa_marks (F : Frame5 P p q a b t o x5 y5) (S : Adjacent P p q) :
    (∃ i j : Fin 5, i ≠ 4 ∧ j ≠ 4 ∧ (o i).negX = false ∧ (o j).negX = true) ∨ SameMarks o := by
  by_cases h : ∀ i : Fin 5, i ≠ 4 → (o i).negX = (o 0).negX
  · right
    intro i hi
    exact ⟨h i hi, by rw [S.mark F hi, S.mark F (i := 0) (by decide)]⟩
  · left
    push Not at h
    obtain ⟨i, hi, hne⟩ := h
    cases h0 : (o 0).negX
    · exact ⟨0, i, by decide, hi, h0, by simpa [h0] using hne⟩
    · exact ⟨i, 0, hi, by decide, by simpa [h0] using hne, h0⟩

/-- All marks equal, pattern O, two adjacent occupied corners: section 3.2
(`allEqual_O`) gives a reflection of `P`; a reflection in the horizontal midline
would put the corner above `A` into `P`, so it is the one that exchanges `A`
and `C`. -/
private theorem oa_reflect (F : FrameO P p q a b t o x5 y5) (S : Adjacent P p q)
    (hm : SameMarks o) : ∀ c : Cell, c ∈ P ↔ (p - 1 - c.1, c.2) ∈ P := by
  rcases allEqual_O F hm with h | h
  · exact h
  · exact absurd (by simpa using (h (0, 0)).1 S.hA) S.h01

/-- **`report-A2.md`, 6.3, type (v, v, h, h), (12).** If `m_3 ≠ m_4`, both `A` and
`C` are used and (R) gives the claim. If `m_3 = m_4`, (11) gives `X_A = X_C`;
then either both are used, or all marks are equal and section 3.2
(`allEqual_O`) gives a reflection of `P` that exchanges `A` and `C`. -/
theorem o63_vvhh_12 (F : FrameO P p q a b t o x5 y5) (S : AdjFull P p q)
    (h0 : (o 0).swap = true) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = false) : Setup12 P p q a b o := by
  have F' := F.toFrame5
  have m0 := S.toAdjacent.mark F' (i := 0) (by decide)
  have m1 := S.toAdjacent.mark F' (i := 1) (by decide)
  have m2 := S.toAdjacent.mark F' (i := 2) (by decide)
  have m3 := S.toAdjacent.mark F' (i := 3) (by decide)
  have hF := S.fullF
  have ht := F.side_top
  have hl := F.side_left
  have hr := F.side_right
  rw [oa_rowLine_h h2 m2, oa_rowLine_h h3 m3] at ht
  rw [oa_colLine_v h0 m0, oa_colLine_h h3] at hl
  rw [oa_colLine_v h1 m1, oa_colLine_h h2] at hr
  -- (11) when `m_3 = m_4`
  have hsym : (o 2).negX = (o 3).negX → ∀ c : ℤ, colCount P c = colCount P (p - 1 - c) := by
    intro h23
    refine (o63_eleven F S fun x _ _ => ?_).2.2
    simp only [oa_colLine_v h0 m0, oa_colLine_v h1 m1, oa_colLine_h h2, oa_colLine_h h3, h23]
    ring
  -- `r_A = r_C`
  have hrr : colCount P (p - 1) = colCount P 0 := by
    by_cases h23 : (o 2).negX = (o 3).negX
    · have k := hsym h23 0
      rw [sub_zero] at k
      exact k.symm
    · cases hx2 : (o 2).negX <;> cases hx3 : (o 3).negX <;> simp [hx2, hx3] at h23 hl hr <;>
        omega
  -- (12): the two sides perpendicular to `F`
  have hrun : (∀ y : ℤ, ((0, y) : Cell) ∈ P ↔ 0 ≤ y ∧ y < colCount P 0) ∧
      (∀ y : ℤ, ((p - 1, y) : Cell) ∈ P ↔ 0 ≤ y ∧ y < colCount P (p - 1)) := by
    rcases oa_marks F' S.toAdjacent with ⟨i, j, hi, hj, hxi, hxj⟩ | hm
    · exact ⟨by simpa [hxi] using oa_run F' S.toAdjacent hi,
        by simpa [hxj] using oa_run F' S.toAdjacent hj⟩
    · have hR := oa_reflect F S.toAdjacent hm
      have hrun0 := oa_run F' S.toAdjacent (i := 0) (by decide)
      have e1 : ∀ y : ℤ, ((0, y) : Cell) ∈ P ↔ ((p - 1, y) : Cell) ∈ P := fun y => by
        simpa using hR (0, y)
      cases hx : (o 0).negX
      · simp only [hx, Bool.false_eq_true, ite_false] at hrun0
        exact ⟨hrun0, fun y => by rw [← e1, hrun0, hrr]⟩
      · simp only [hx, ite_true] at hrun0
        exact ⟨fun y => by rw [e1, hrun0, hrr], hrun0⟩
  have hu1 : (o 0).rowLine p q P 0 = colCount P 0 := by
    rw [oa_rowLine_v h0]
    cases (o 0).negX <;> simp [hrr]
  have hu2 : (o 1).rowLine p q P 0 = colCount P 0 := by
    rw [oa_rowLine_v h1]
    cases (o 1).negX <;> simp [hrr]
  have hbot := F.side_bottom
  rw [hu1, hu2] at hbot
  refine ⟨by omega, ?_, hrr, hrun.1, fun y => by rw [hrun.2, hrr], hu1, hu2, by omega, hsym⟩
  cases hx3 : (o 3).negX <;> simp [hx3] at hl <;> omega

/-- Widths and heights of the boxes of the two types. -/
private theorem oa_W_h {c : Orient} (hs : c.swap = false) : c.W p q = p := by simp [Orient.W, hs]

private theorem oa_H_h {c : Orient} (hs : c.swap = false) : c.H p q = q := by simp [Orient.H, hs]

private theorem oa_W_v {c : Orient} (hs : c.swap = true) : c.W p q = q := by simp [Orient.W, hs]

private theorem oa_H_v {c : Orient} (hs : c.swap = true) : c.H p q = p := by simp [Orient.H, hs]

/-- `report-A2.md`, 6.3, type (v, v, h, h), (i): `F` of `T_5` vertical. (T3) with
`h = L = H_1 = H_2` gives `M ≤ x*` and `M ≤ 2L - 1 - x*`; but `x* = u_1 = r < M`
or `2L - 1 - x* = u_2 = r < M`. -/
theorem o63_vvhh_i (F : FrameO P p q a b t o x5 y5) (S : AdjFull P p q)
    (h0 : (o 0).swap = true) (h1 : (o 1).swap = true) (_h2 : (o 2).swap = false)
    (_h3 : (o 3).swap = false) (K : Setup12 P p q a b o) (h4 : (o 4).swap = true) : False := by
  have F' := F.toFrame5
  have hy5 := F.y5_eq
  have hrlt := S.rA_lt
  have hmu := F.mu_pos
  have hs := F.side_bottom
  rw [K.hu1, K.hu2] at hs
  have hrow0 : ∀ x : ℤ, 0 ≤ x → x < p → ((x, 0) : Cell) ∈ P := (F'.rowCount_eq_iff 0).1 S.fullF
  have hW4 : (o 4).W p q = q := oa_W_v h4
  have hb0 : ∀ x : ℤ, ((x, 0) : Cell) ∈ t 4 ↔
      colCount P 0 ≤ x ∧ x < colCount P 0 + (o 4).rowLine p q P 0 := by
    intro x
    rw [F.bottom4, K.hu1]
  -- `F` of `T_5` is the column `x*` of `R a b`, in the rows `[0, L)`
  have hcol : ∀ X : ℤ, X = x5 + (if (o 4).negY then q - 1 else 0) →
      ∀ y : ℤ, 0 ≤ y → y < p → ((X, y) : Cell) ∈ t 4 := by
    intro X hX y h0 h1
    rw [F'.mem4]
    have := hrow0 (if (o 4).negX then p - 1 - y else y) (by split <;> omega) (by split <;> omega)
    convert this using 1
    subst hX
    cases hy : (o 4).negY <;> cases hx : (o 4).negX <;> simp [Orient.back, h4, hy, hx, hy5]
  cases hy : (o 4).negY
  · -- `x* = x5`: (T3) on the left, and `x5 ≤ u_1 = r`
    have hT := F.T3_left (x := x5) (h := p) (hcol x5 (by simp [hy])) (by rw [oa_H_v h0])
    rw [oa_W_v h0] at hT
    have c := (hb0 (colCount P 0)).2 ⟨le_rfl, by omega⟩
    have := (F'.box4 c).1.1
    simp only at this
    omega
  · -- `x* = x5 + M - 1`: (T3) on the right, and `a - 1 - x* ≤ u_2 = r`
    have hT := F.T3_right (x := x5 + (q - 1)) (h := p) (hcol _ (by simp [hy]))
      (by rw [oa_H_v h1])
    rw [oa_W_v h1] at hT
    have c := (hb0 (colCount P 0 + (o 4).rowLine p q P 0 - 1)).2 ⟨by omega, by omega⟩
    have := (F'.box4 c).1.2
    rw [hW4] at this
    simp only at this
    omega

/-- In pattern O with the mark of `T_5` on `F`, the lowest row of `T_5` starts at
its box: `x5 = u_1`. -/
private theorem oa_x5 (F : FrameO P p q a b t o x5 y5) (S : Adjacent P p q)
    (h4y : (o 4).negY = false) : x5 = (o 0).rowLine p q P 0 := by
  have F' := F.toFrame5
  have hy5 := F.y5_eq
  have hm : (o 4).back p q (0, 0) ∈ P := by
    rw [Orient.back_zero, h4y]
    cases (o 4).negX
    · simpa [cornerP] using S.hA
    · simpa [cornerP] using S.hC
  have h1 : ((x5, 0) : Cell) ∈ t 4 := by
    rw [F'.mem4]
    simpa [hy5] using hm
  have h2 := (F.bottom4 x5).1 h1
  have h3 : (((o 0).rowLine p q P 0, 0) : Cell) ∈ t 4 :=
    (F.bottom4 _).2 ⟨le_rfl, by linarith [F.mu_pos]⟩
  have h4 := (F'.box4 h3).1.1
  simp only at h4
  omega

/-- A tall tile whose mark is on `F`: its local cell `(x, y)` is in `P` when
`x` is in a full layer. -/
private theorem oa_back_v {c : Orient} (hs : c.swap = true) (hy : c.negY = false) {r : ℤ}
    (hR : ∀ x y : ℤ, 0 ≤ x → x < p → 0 ≤ y → y < r → ((x, y) : Cell) ∈ P) {x y : ℤ}
    (h0 : 0 ≤ x) (h1 : x < r) (h2 : 0 ≤ y) (h3 : y < p) : c.back p q (x, y) ∈ P := by
  cases hx : c.negX
  · simpa [Orient.back, hs, hy, hx] using hR y x h2 h3 h0 h1
  · simpa [Orient.back, hs, hy, hx] using hR (p - 1 - y) x (by omega) (by omega) h0 h1

/-- A wide tile whose mark is on `F`: its local cell `(x, y)` is in `P` when `y`
is in a full layer. -/
private theorem oa_back_h {c : Orient} (hs : c.swap = false) (hy : c.negY = false) {r : ℤ}
    (hR : ∀ x y : ℤ, 0 ≤ x → x < p → 0 ≤ y → y < r → ((x, y) : Cell) ∈ P) {x y : ℤ}
    (h0 : 0 ≤ x) (h1 : x < p) (h2 : 0 ≤ y) (h3 : y < r) : c.back p q (x, y) ∈ P := by
  cases hx : c.negX
  · simpa [Orient.back, hs, hy, hx] using hR x y h0 h1 h2 h3
  · simpa [Orient.back, hs, hy, hx] using hR (p - 1 - x) y (by omega) (by omega) h2 h3

/-- The local position of a cell `d` of `P` in a wide tile with its mark on `F`. -/
private theorem oa_back_pos_h {c : Orient} (hs : c.swap = false) (hy : c.negY = false)
    (d : Cell) : c.back p q (if c.negX then p - 1 - d.1 else d.1, d.2) = d := by
  rcases d with ⟨x, y⟩
  cases hx : c.negX <;> simp [Orient.back, hs, hy, hx]

/-- The local position of a cell `d` of `P` in a tall tile with its mark on `F`. -/
private theorem oa_back_pos_v {c : Orient} (hs : c.swap = true) (hy : c.negY = false)
    (d : Cell) : c.back p q (d.2, if c.negX then p - 1 - d.1 else d.1) = d := by
  rcases d with ⟨x, y⟩
  cases hx : c.negX <;> simp [Orient.back, hs, hy, hx]

/-- `report-A2.md`, 6.3, type (v, v, h, h), (ii), first bullet: `F` of `T_5` at
the bottom, `M ≤ 2r`. Here `mu = L`, so `L = 2r`, `x5 = r`, `a = 4r`, `b = 3r`.
The layers `0, ..., r - 1` of `P` are full; the other cells of every tile lie in
`[r, 3r) x [r, 2r)`, at positions `≥ r` from its mark; two different marks are
impossible (the positions from `A` and from `C` add up to `2r - 1`), and equal
marks give a reflection by section 3.2. -/
theorem o63_vvhh_ii_small (F : FrameO P p q a b t o x5 y5) (S : AdjFull P p q)
    (h0 : (o 0).swap = true) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = false) (K : Setup12 P p q a b o) (h4 : (o 4).swap = false)
    (h4y : (o 4).negY = false) (hM : q ≤ 2 * colCount P 0) : False := by
  have F' := F.toFrame5
  have m0 := S.toAdjacent.mark F' (i := 0) (by decide)
  have m1 := S.toAdjacent.mark F' (i := 1) (by decide)
  have m2 := S.toAdjacent.mark F' (i := 2) (by decide)
  have m3 := S.toAdjacent.mark F' (i := 3) (by decide)
  have hy5 := F.y5_eq
  have hrlt := S.rA_lt
  have hr1 := S.rA_pos
  have ha := K.ha
  have hb := K.hb
  -- `mu = L`, so `L = 2r`; `x5 = u_1 = r`
  have hmu := K.hmu
  rw [oa_rowLine_h h4 h4y, S.fullF] at hmu
  have hx5 := oa_x5 F S.toAdjacent h4y
  rw [K.hu1] at hx5
  -- the rows at distance `c < r` from the top meet only `T_3`, `T_4`
  have hrow : ∀ c : ℤ, 0 ≤ c → c < colCount P 0 → rowCount P c = p := by
    intro c h0' h1'
    have e := F'.row_sum (y := b - 1 - c) (by omega) (by omega)
    rw [F'.rowLine_zero (o 0) (y := b - 1 - c) (Or.inr (by rw [oa_H_v h0]; omega)),
      F'.rowLine_zero (o 1) (y := b - 1 - c) (Or.inr (by rw [oa_H_v h1]; omega)),
      F'.rowLine_zero (o 4) (y := b - 1 - c - y5) (Or.inr (by rw [oa_H_h h4]; omega)),
      oa_rowLine_h h2 m2, oa_rowLine_h h3 m3, sub_sub_cancel] at e
    omega
  have hfull : ∀ x y : ℤ, 0 ≤ x → x < p → 0 ≤ y → y < colCount P 0 → ((x, y) : Cell) ∈ P :=
    fun x y h0' h1' h2' h3' => (F'.rowCount_eq_iff y).1 (hrow y h2' h3') x h0' h1'
  -- a cell `d` of `P` in a layer `≥ r` is at a position `≥ r` from every mark
  have k0 : ∀ d : Cell, d ∈ P → colCount P 0 ≤ d.2 →
      colCount P 0 ≤ (if (o 0).negX then p - 1 - d.1 else d.1) := by
    intro d hd hd2
    have hdb := F'.P_bounds hd
    have hX0 : 0 ≤ (if (o 0).negX then p - 1 - d.1 else d.1) := by split <;> omega
    by_contra hlt
    push Not at hlt
    have c0 : ((d.2, if (o 0).negX then p - 1 - d.1 else d.1) : Cell) ∈ t 0 := by
      rw [F'.mem0, oa_back_pos_v h0 m0 d]
      exact hd
    have c4 : ((d.2, if (o 0).negX then p - 1 - d.1 else d.1) : Cell) ∈ t 4 := by
      rw [F'.mem4]
      exact oa_back_h h4 h4y hfull (x := d.2 - x5)
        (y := (if (o 0).negX then p - 1 - d.1 else d.1) - y5) (by omega) (by omega) (by omega)
        (by omega)
    exact absurd (F'.tile_unique c0 c4) (by decide)
  have k1 : ∀ d : Cell, d ∈ P → colCount P 0 ≤ d.2 →
      colCount P 0 ≤ (if (o 1).negX then p - 1 - d.1 else d.1) := by
    intro d hd hd2
    have hdb := F'.P_bounds hd
    have hX0 : 0 ≤ (if (o 1).negX then p - 1 - d.1 else d.1) := by split <;> omega
    by_contra hlt
    push Not at hlt
    have c1 : ((a - 1 - d.2, if (o 1).negX then p - 1 - d.1 else d.1) : Cell) ∈ t 1 := by
      rw [F'.mem1]
      simp only [sub_sub_cancel]
      rw [oa_back_pos_v h1 m1 d]
      exact hd
    have c4 : ((a - 1 - d.2, if (o 1).negX then p - 1 - d.1 else d.1) : Cell) ∈ t 4 := by
      rw [F'.mem4]
      exact oa_back_h h4 h4y hfull (x := a - 1 - d.2 - x5)
        (y := (if (o 1).negX then p - 1 - d.1 else d.1) - y5) (by omega) (by omega) (by omega)
        (by omega)
    exact absurd (F'.tile_unique c1 c4) (by decide)
  have k2 : ∀ d : Cell, d ∈ P → colCount P 0 ≤ d.2 →
      colCount P 0 ≤ (if (o 2).negX then p - 1 - d.1 else d.1) := by
    intro d hd hd2
    have hdb := F'.P_bounds hd
    have hX0 : 0 ≤ (if (o 2).negX then p - 1 - d.1 else d.1) := by split <;> omega
    by_contra hlt
    push Not at hlt
    have c2 : ((a - 1 - (if (o 2).negX then p - 1 - d.1 else d.1), b - 1 - d.2) : Cell) ∈ t 2 := by
      rw [F'.mem2]
      simp only [sub_sub_cancel]
      rw [oa_back_pos_h h2 m2 d]
      exact hd
    have c1 : ((a - 1 - (if (o 2).negX then p - 1 - d.1 else d.1), b - 1 - d.2) : Cell) ∈ t 1 := by
      rw [F'.mem1]
      simp only [sub_sub_cancel]
      exact oa_back_v h1 m1 hfull (x := if (o 2).negX then p - 1 - d.1 else d.1)
        (y := b - 1 - d.2) hX0 hlt (by omega) (by omega)
    exact absurd (F'.tile_unique c1 c2) (by decide)
  have k3 : ∀ d : Cell, d ∈ P → colCount P 0 ≤ d.2 →
      colCount P 0 ≤ (if (o 3).negX then p - 1 - d.1 else d.1) := by
    intro d hd hd2
    have hdb := F'.P_bounds hd
    have hX0 : 0 ≤ (if (o 3).negX then p - 1 - d.1 else d.1) := by split <;> omega
    by_contra hlt
    push Not at hlt
    have c3 : ((if (o 3).negX then p - 1 - d.1 else d.1, b - 1 - d.2) : Cell) ∈ t 3 := by
      rw [F'.mem3]
      simp only [sub_sub_cancel]
      rw [oa_back_pos_h h3 m3 d]
      exact hd
    have c0 : ((if (o 3).negX then p - 1 - d.1 else d.1, b - 1 - d.2) : Cell) ∈ t 0 := by
      rw [F'.mem0]
      exact oa_back_v h0 m0 hfull hX0 hlt (by omega) (by omega)
    exact absurd (F'.tile_unique c0 c3) (by decide)
  have hpos : ∀ i : Fin 5, i ≠ 4 → ∀ d : Cell, d ∈ P → colCount P 0 ≤ d.2 →
      colCount P 0 ≤ (if (o i).negX then p - 1 - d.1 else d.1) := by
    intro i hi
    fin_cases i
    exacts [k0, k1, k2, k3, absurd rfl hi]
  -- layer `r` holds a cell, since `r < M`
  obtain ⟨x, hx⟩ := Prop61.rowCount_pos_iff.1
    (by have := F'.rowCount_pos (y := colCount P 0) (by omega) hrlt; omega :
      0 < rowCount P (colCount P 0))
  rcases oa_marks F' S.toAdjacent with ⟨i, j, hi, hj, hxi, hxj⟩ | hm
  · -- `A` and `C` used: the positions from `A` and from `C` add up to `2r - 1`
    have e1 := hpos i hi _ hx le_rfl
    have e2 := hpos j hj _ hx le_rfl
    simp only [hxi, hxj, Bool.false_eq_true, ite_false, ite_true] at e1 e2
    omega
  · -- all marks equal: the reflection of `P` exchanging `A` and `C`
    have hx' := (oa_reflect F S.toAdjacent hm (x, colCount P 0)).1 hx
    have e1 := hpos 0 (by decide) _ hx le_rfl
    have e2 := hpos 0 (by decide) _ hx' le_rfl
    cases h : (o 0).negX <;> simp [h] at e1 e2 <;> omega

/-- `report-A2.md`, 6.3, type (v, v, h, h), (ii), second bullet: `F` of `T_5` at
the bottom, `M > 2r`. With `t = 3r - M`: the row at distance `t` from the top
gives `2 lambda(t) + f = 4r`; the columns `t` from the left and from the right
give `lambda(t) + X_{m_4}(t) = 3r = lambda(t) + X_{m_3}(t)`; the row `t` from the
bottom gives `2 (r + f/2) + (2r - f/2) + 2f = 4r`, so `f = 0`. A line-count
argument: `Frame5.row_sum` twice, `Frame5.col_sum` twice, `Setup12.hsym`. -/
theorem o63_vvhh_ii_large (F : FrameO P p q a b t o x5 y5) (S : AdjFull P p q)
    (h0 : (o 0).swap = true) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = false) (K : Setup12 P p q a b o) (h4 : (o 4).swap = false)
    (h4y : (o 4).negY = false) (hM : 2 * colCount P 0 < q) : False := by
  have F' := F.toFrame5
  have m0 := S.toAdjacent.mark F' (i := 0) (by decide)
  have m1 := S.toAdjacent.mark F' (i := 1) (by decide)
  have m2 := S.toAdjacent.mark F' (i := 2) (by decide)
  have m3 := S.toAdjacent.mark F' (i := 3) (by decide)
  have hy5 := F.y5_eq
  have hf := S.f_pos
  have ha := K.ha
  have hb := K.hb
  have hmu := K.hmu
  rw [oa_rowLine_h h4 h4y, S.fullF] at hmu
  have hx5 := oa_x5 F S.toAdjacent h4y
  rw [K.hu1] at hx5
  have hq5 := F.h5_le
  rw [oa_H_h h4] at hq5
  -- `t = b - M`; the row at distance `t` from the top is row `M - 1`
  have e1 := F'.row_sum (y := q - 1) (by omega) (by omega)
  rw [F'.rowLine_zero (o 0) (y := q - 1) (Or.inr (by rw [oa_H_v h0]; omega)),
    F'.rowLine_zero (o 1) (y := q - 1) (Or.inr (by rw [oa_H_v h1]; omega)),
    oa_rowLine_h h2 m2, oa_rowLine_h h3 m3, oa_rowLine_h h4 h4y] at e1
  -- the column `t` from the left
  have e2 := F'.col_sum (x := b - q) (by omega) (by omega)
  rw [oa_colLine_v h0 m0,
    F'.colLine_zero (o 1) (x := a - 1 - (b - q)) (Or.inr (by rw [oa_W_v h1]; omega)),
    F'.colLine_zero (o 2) (x := a - 1 - (b - q)) (Or.inr (by rw [oa_W_h h2]; omega)),
    oa_colLine_h h3, F'.colLine_zero (o 4) (x := b - q - x5) (Or.inl (by omega))] at e2
  -- the column `t` from the right
  have e3 := F'.col_sum (x := a - 1 - (b - q)) (by omega) (by omega)
  rw [F'.colLine_zero (o 0) (x := a - 1 - (b - q)) (Or.inr (by rw [oa_W_v h0]; omega)),
    F'.colLine_zero (o 3) (x := a - 1 - (b - q)) (Or.inr (by rw [oa_W_h h3]; omega)),
    F'.colLine_zero (o 4) (x := a - 1 - (b - q) - x5) (Or.inr (by rw [oa_W_h h4]; omega)),
    sub_sub_cancel, oa_colLine_v h1 m1, oa_colLine_h h2] at e3
  -- the row `t` from the bottom
  have e4 := F'.row_sum (y := b - q) (by omega) (by omega)
  rw [oa_rowLine_v h0, oa_rowLine_v h1, oa_rowLine_h h2 m2, oa_rowLine_h h3 m3,
    oa_rowLine_h h4 h4y] at e4
  -- by (12), `X_A(t) = X_C(t)` in both cases
  have hX : colCount P (b - q) = colCount P (p - 1 - (b - q)) := by
    by_cases h23 : (o 2).negX = (o 3).negX
    · exact K.hsym h23 (b - q)
    · cases hx2 : (o 2).negX <;> cases hx3 : (o 3).negX <;> simp [hx2, hx3] at h23 e2 e3 <;>
        omega
  have hXi : ∀ n : Bool, colCount P (if n then p - 1 - (b - q) else b - q) = colCount P (b - q) := by
    intro n
    cases n
    · simp
    · simp [hX]
  simp only [hXi] at e2 e3 e4
  have r1 : rowCount P (b - 1 - (q - 1)) = rowCount P (b - q) := by congr 1; ring
  have r2 : rowCount P (q - 1 - y5) = rowCount P (q - 1) := by congr 1; omega
  have r3 : rowCount P (b - 1 - (b - q)) = rowCount P (q - 1) := by congr 1; ring
  have r4 : rowCount P (b - q - y5) = rowCount P (b - q) := by congr 1; omega
  omega

/-- `report-A2.md`, 6.3, type (v, v, h, h), (iii): `F` of `T_5` on top of its
box. `mu = f ≤ L - 2`, so `2r ≥ L + 2`; `T_4` contains `(L - 1, y)` for
`L ≤ y < b`, so `M ≤ L`; the layers `0, ..., r - 1` are full; row `M - 1` of
`T_5` gives `r ≤ x5` and `x5 + L ≤ 2L - r`, so `2r ≤ L`. -/
theorem o63_vvhh_iii (F : FrameO P p q a b t o x5 y5) (S : AdjFull P p q)
    (h0 : (o 0).swap = true) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = false) (K : Setup12 P p q a b o) (h4 : (o 4).swap = false)
    (h4y : (o 4).negY = true) : False := by
  have F' := F.toFrame5
  have m0 := S.toAdjacent.mark F' (i := 0) (by decide)
  have m1 := S.toAdjacent.mark F' (i := 1) (by decide)
  have m2 := S.toAdjacent.mark F' (i := 2) (by decide)
  have m3 := S.toAdjacent.mark F' (i := 3) (by decide)
  have hy5 := F.y5_eq
  have hfl := S.f_le
  have hrlt := S.rA_lt
  have hr1 := S.rA_pos
  have ha := K.ha
  have hb := K.hb
  -- `mu = f`
  have hmu := K.hmu
  have hmu' : (o 4).rowLine p q P 0 = rowCount P (q - 1) := by simp [Orient.rowLine, h4, h4y]
  rw [hmu'] at hmu
  have hH4 : (o 4).H p q = q := oa_H_h h4
  have hx5 := F.x5_pos
  have hx5' := F.x5_le
  have hq5 := F.h5_le
  rw [oa_W_h h4] at hx5'
  rw [hH4] at hq5
  have hrow0 : ∀ x : ℤ, 0 ≤ x → x < p → ((x, 0) : Cell) ∈ P := (F'.rowCount_eq_iff 0).1 S.fullF
  -- the row `M - 1` of `T_5` is its `F`
  have hT5 : ∀ x : ℤ, x5 ≤ x → x < x5 + p → ((x, q - 1) : Cell) ∈ t 4 := by
    intro x h0' h1'
    rw [F'.mem4]
    have := hrow0 (if (o 4).negX then p - 1 - (x - x5) else x - x5) (by split <;> omega)
      (by split <;> omega)
    convert this using 1
    simp [Orient.back, h4, h4y, hy5]
  -- `T_4` contains `(L - 1, y)` for `L ≤ y < b`
  have hT4 : ∀ y : ℤ, p ≤ y → y < b → ((p - 1, y) : Cell) ∈ t 3 := by
    intro y h0' h1'
    rw [F'.mem3]
    cases hx : (o 3).negX
    · have e : (o 3).back p q (p - 1, b - 1 - y) = (p - 1, b - 1 - y) := by
        simp [Orient.back, h3, m3, hx]
      rw [e]
      exact (K.colC _).2 ⟨by omega, by omega⟩
    · have e : (o 3).back p q (p - 1, b - 1 - y) = (0, b - 1 - y) := by
        simp [Orient.back, h3, m3, hx]
      rw [e]
      exact (K.colA _).2 ⟨by omega, by omega⟩
  -- `M ≤ L`
  have hqp : q ≤ p := by
    by_contra hlt
    have c4 := hT5 (p - 1) (by omega) (by omega)
    have c3 := hT4 (q - 1) (by omega) (by omega)
    exact absurd (F'.tile_unique c3 c4) (by decide)
  -- the layers `0, ..., r - 1` are full
  have hrow : ∀ c : ℤ, 0 ≤ c → c < colCount P 0 → rowCount P c = p := by
    intro c h0' h1'
    have e := F'.row_sum (y := b - 1 - c) (by omega) (by omega)
    rw [F'.rowLine_zero (o 0) (y := b - 1 - c) (Or.inr (by rw [oa_H_v h0]; omega)),
      F'.rowLine_zero (o 1) (y := b - 1 - c) (Or.inr (by rw [oa_H_v h1]; omega)),
      F'.rowLine_zero (o 4) (y := b - 1 - c - y5) (Or.inr (by rw [hH4]; omega)),
      oa_rowLine_h h2 m2, oa_rowLine_h h3 m3, sub_sub_cancel] at e
    omega
  have hfull : ∀ x y : ℤ, 0 ≤ x → x < p → 0 ≤ y → y < colCount P 0 → ((x, y) : Cell) ∈ P :=
    fun x y h0' h1' h2' h3' => (F'.rowCount_eq_iff y).1 (hrow y h2' h3') x h0' h1'
  -- row `M - 1` of `T_5`: `r ≤ x5`
  have hl : colCount P 0 ≤ x5 := by
    by_contra hlt
    have c4 := hT5 x5 le_rfl (by omega)
    have c0 : ((x5, q - 1) : Cell) ∈ t 0 := by
      rw [F'.mem0]
      exact oa_back_v h0 m0 hfull (by omega) (by omega) (by omega) (by omega)
    exact absurd (F'.tile_unique c0 c4) (by decide)
  -- and `x5 + L ≤ 2L - r`
  have hr : x5 + p ≤ 2 * p - colCount P 0 := by
    by_contra hlt
    have c4 := hT5 (x5 + p - 1) (by omega) (by omega)
    have c1 : ((x5 + p - 1, q - 1) : Cell) ∈ t 1 := by
      rw [F'.mem1]
      exact oa_back_v h1 m1 hfull (x := a - 1 - (x5 + p - 1)) (y := q - 1) (by omega)
        (by omega) (by omega) (by omega)
    exact absurd (F'.tile_unique c1 c4) (by decide)
  omega

/-- **`report-A2.md`, 6.3, type (v, v, h, h).** -/
theorem o63_vvhh (F : FrameO P p q a b t o x5 y5) (S : AdjFull P p q)
    (h0 : (o 0).swap = true) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = false) : False := by
  have K := o63_vvhh_12 F S h0 h1 h2 h3
  cases h4 : (o 4).swap
  · cases h4y : (o 4).negY
    · rcases le_or_gt q (2 * colCount P 0) with h | h
      · exact o63_vvhh_ii_small F S h0 h1 h2 h3 K h4 h4y h
      · exact o63_vvhh_ii_large F S h0 h1 h2 h3 K h4 h4y h
    · exact o63_vvhh_iii F S h0 h1 h2 h3 K h4 h4y
  · exact o63_vvhh_i F S h0 h1 h2 h3 K h4

/-! ## Type `(v, v, h, v)` -/

/-- The facts of `report-A2.md`, 6.3, type (v, v, h, v), with `m_3 = C`, before
the split on `F` of `T_5`: `b = 2L`, `r_C = L < M ≤ 2L - 1`, `a = L + r_{m_4}`,
and `A` is used; so by (R) the cells of `P` on the two sides of `box(P)`
perpendicular to `F` are the `r_A` and the `r_C = L` cells next to `F`. -/
structure SetupV (P : Finset Cell) (p q a b : ℤ) (o : Fin 5 → Orient) : Prop where
  /-- (1), left. -/
  hb : b = 2 * p
  /-- (1), right: `r_C = L`. -/
  hrC : colCount P (p - 1) = p
  /-- `r_C = L < M`. -/
  hpq : p < q
  /-- `M = H_3 ≤ b - 1`. -/
  hq : q ≤ 2 * p - 1
  /-- (1), top: `a = L + r_{m_4}`. -/
  ha : a = p + (o 3).rowLine p q P 0
  /-- `A` is used (by `T_1`, `T_2` or `T_4`; the mark of `T_3` is `C`). -/
  hA : (o 0).negX = false ∨ (o 1).negX = false ∨ (o 3).negX = false
  /-- (R) at `A`: the cells of `P` on the side of `box(P)` at `A` are the `r_A`
  cells next to `F`. -/
  colA : ∀ y : ℤ, ((0, y) : Cell) ∈ P ↔ 0 ≤ y ∧ y < colCount P 0
  /-- (R) at `C`: the side of `box(P)` at `C` holds the `L` cells next to `F`. -/
  colC : ∀ y : ℤ, ((p - 1, y) : Cell) ∈ P ↔ 0 ≤ y ∧ y < p

/-- A local row count is not negative. -/
private theorem vb_rowLine_nonneg (c : Orient) (y : ℤ) : 0 ≤ c.rowLine p q P y := by
  unfold Orient.rowLine
  split
  · exact colCount_nonneg _ _
  · exact rowCount_nonneg _ _

/-- The run `u_i` of a corner tile with `F` vertical is `r_{m_i}`: `L` for the
mark `C`, `r_A` for the mark `A`. -/
private theorem vb_u {c : Orient} (hrC : colCount P (p - 1) = p) (hs : c.swap = true) :
    c.rowLine p q P 0 = if c.negX then p else colCount P 0 := by
  cases hx : c.negX <;> simp [Orient.rowLine, hs, hx, hrC]

/-- The cells of a corner tile with `F` vertical in the row `L - 1` (the far end
of its `F`): `r_{m_i'}`. -/
private theorem vb_far {c : Orient} (hrC : colCount P (p - 1) = p) (hs : c.swap = true) :
    c.rowLine p q P (p - 1) = if c.negX then colCount P 0 else p := by
  cases hx : c.negX <;> simp [Orient.rowLine, hs, hx, hrC]

/-- (R) at `A`, read off a corner tile with `F` vertical and the mark `A`. -/
private theorem vb_colA (F : Frame5 P p q a b t o x5 y5) (S : AdjFull P p q) {i : Fin 5}
    (hi : i ≠ 4) (hs : (o i).swap = true) (hx : (o i).negX = false) (y : ℤ) :
    ((0, y) : Cell) ∈ P ↔ 0 ≤ y ∧ y < colCount P 0 := by
  have e : o i = ⟨true, false, false⟩ := Orient.ext hs hx (S.toAdjacent.mark F hi)
  have h := F.hside hi y
  rw [e] at h
  simpa [Orient.back, Orient.rowLine] using h

/-- `report-A2.md`, 6.3, type (v, v, h, v), first paragraph: "By (1) b = 2L
(left), r_{m_3} = L (right), a = L + r_{m_4} (top), r_{m_1} + mu + r_{m_2} = a.
... If all marks were C, a = 2L and 2L + mu = a. So A is used". -/
theorem o63_vvhv_setup (F : FrameO P p q a b t o x5 y5) (S : AdjFull P p q)
    (h0 : (o 0).swap = true) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) (h2x : (o 2).negX = true) : SetupV P p q a b o := by
  have y0 := S.toAdjacent.mark F.toFrame5 (i := 0) (by decide)
  have y1 := S.toAdjacent.mark F.toFrame5 (i := 1) (by decide)
  have y3 := S.toAdjacent.mark F.toFrame5 (i := 3) (by decide)
  have e2 : o 2 = ⟨false, true, false⟩ :=
    Orient.ext h2 h2x (S.toAdjacent.mark F.toFrame5 (i := 2) (by decide))
  have hl := F.side_left
  have hr := F.side_right
  have ht := F.side_top
  have hH := F.toFrame5.H_le (i := 2) (by decide)
  have v0 : (o 0).colLine p q P 0 = p := by simpa [Orient.colLine, h0, y0] using S.fullF
  have v1 : (o 1).colLine p q P 0 = p := by simpa [Orient.colLine, h1, y1] using S.fullF
  have v3 : (o 3).colLine p q P 0 = p := by simpa [Orient.colLine, h3, y3] using S.fullF
  have w2 : (o 2).rowLine p q P 0 = p := by rw [e2]; simpa [Orient.rowLine] using S.fullF
  have c2 : (o 2).colLine p q P 0 = colCount P (p - 1) := by rw [e2]; simp [Orient.colLine]
  rw [e2] at hH
  simp only [Orient.H] at hH
  have hb : b = 2 * p := by omega
  have hrC : colCount P (p - 1) = p := by omega
  have hC := S.rC_lt
  have hA : (o 0).negX = false ∨ (o 1).negX = false ∨ (o 3).negX = false := by
    by_contra hne
    simp only [not_or, Bool.not_eq_false] at hne
    obtain ⟨x0, x1, x3⟩ := hne
    have hbot := F.side_bottom
    have hmu := F.mu_pos
    rw [vb_u hrC h0, vb_u hrC h1, x0, x1] at hbot
    rw [vb_u hrC h3, x3] at ht
    simp at hbot ht
    omega
  refine ⟨hb, hrC, by omega, by simpa [hb] using hH, by omega, hA, ?_, ?_⟩
  · rcases hA with x | x | x
    · exact vb_colA F.toFrame5 S (i := 0) (by decide) h0 x
    · exact vb_colA F.toFrame5 S (i := 1) (by decide) h1 x
    · exact vb_colA F.toFrame5 S (i := 3) (by decide) h3 x
  · intro y
    have h := F.toFrame5.vside (i := 2) (by decide) y
    rw [e2] at h
    simpa [Orient.back, Orient.colLine, hrC] using h

/-- `report-A2.md`, 6.3, type (v, v, h, v), (i): `F` of `T_5` vertical; as (i) of
the type (v, v, h, h). `F` of `T_5` is the column `x*` of `box(T_5)`, rows
`[0, L)`; (T3) gives `M ≤ x*` and `M ≤ a - 1 - x*`; the bottom interval of `T_5`
starts at `x* = u_1` or ends at `x* = a - 1 - u_2`, and `u_1, u_2 < M`. -/
theorem o63_vvhv_i (F : FrameO P p q a b t o x5 y5) (S : AdjFull P p q)
    (h0 : (o 0).swap = true) (h1 : (o 1).swap = true) (_h2 : (o 2).swap = false)
    (_h3 : (o 3).swap = true) (_h2x : (o 2).negX = true) (V : SetupV P p q a b o)
    (h4 : (o 4).swap = true) : False := by
  have hy5 := F.y5_eq
  have hp := F.toFrame5.two_le_p
  have hbot := F.side_bottom
  have hu1 : (o 0).rowLine p q P 0 < q := by
    rw [vb_u V.hrC h0]; split <;> [exact V.hpq; exact S.rA_lt]
  have hu2 : (o 1).rowLine p q P 0 < q := by
    rw [vb_u V.hrC h1]; split <;> [exact V.hpq; exact S.rA_lt]
  have row0 := (F.toFrame5.rowCount_eq_iff 0).1 S.fullF
  have hH0 : (o 0).H p q ≤ p := by simp [Orient.H, h0]
  have hH1 : (o 1).H p q ≤ p := by simp [Orient.H, h1]
  have hW0 : (o 0).W p q = q := by simp [Orient.W, h0]
  have hW1 : (o 1).W p q = q := by simp [Orient.W, h1]
  have hW4 : (o 4).W p q = q := by simp [Orient.W, h4]
  cases hy4 : (o 4).negY
  · -- `x* = x5`
    have hcol : ∀ y : ℤ, 0 ≤ y → y < p → ((x5, y) : Cell) ∈ t 4 := by
      intro y hy0 hy1
      cases hx4 : (o 4).negX
      · exact (F.toFrame5.mem_of 4 (d := (y, 0))
          (by simp [loc, Orient.back, h4, hx4, hy4, hy5])).2 (row0 y hy0 hy1)
      · exact (F.toFrame5.mem_of 4 (d := (p - 1 - y, 0))
          (by simp [loc, Orient.back, h4, hx4, hy4, hy5])).2 (row0 _ (by omega) (by omega))
    have hT := F.T3_left hcol hH0
    have hin := (F.bottom4 x5).1 (hcol 0 le_rfl (by omega))
    have hout : ((x5 - 1, 0) : Cell) ∉ t 4 := fun h => by
      have := (F.toFrame5.box4 h).1.1
      simp at this
    rw [F.bottom4] at hout
    omega
  · -- `x* = x5 + M - 1`
    have hcol : ∀ y : ℤ, 0 ≤ y → y < p → ((x5 + q - 1, y) : Cell) ∈ t 4 := by
      intro y hy0 hy1
      cases hx4 : (o 4).negX
      · exact (F.toFrame5.mem_of 4 (d := (y, 0))
          (by simp [loc, Orient.back, h4, hx4, hy4, hy5]; omega)).2 (row0 y hy0 hy1)
      · exact (F.toFrame5.mem_of 4 (d := (p - 1 - y, 0))
          (by simp [loc, Orient.back, h4, hx4, hy4, hy5]; omega)).2
          (row0 _ (by omega) (by omega))
    have hT := F.T3_right hcol hH1
    have hin := (F.bottom4 (x5 + q - 1)).1 (hcol 0 le_rfl (by omega))
    have hout : ((x5 + q, 0) : Cell) ∉ t 4 := fun h => by
      have := (F.toFrame5.box4 h).1.2
      rw [hW4] at this
      simp at this
    rw [F.bottom4] at hout
    omega

/-- (13) of `report-A2.md`, 6.3, type (v, v, h, v), (iii), as a row count: `T_5`
meets the row `L - 1` (`M > L`), so the cells of `T_1` and `T_2` there are at
most `a - 1`. Also used in (ii). -/
private theorem vb_13 (F : FrameO P p q a b t o x5 y5) (V : SetupV P p q a b o)
    (h4 : (o 4).swap = false) :
    (o 0).rowLine p q P (p - 1) + (o 1).rowLine p q P (p - 1) + 1 ≤ a := by
  have hp := F.toFrame5.two_le_p
  have hy5 := F.y5_eq
  have hpq := V.hpq
  have hrow := F.toFrame5.row_sum (y := p - 1) (by omega) (by rw [V.hb]; omega)
  have n2 := vb_rowLine_nonneg (P := P) (p := p) (q := q) (o 2) (b - 1 - (p - 1))
  have n3 := vb_rowLine_nonneg (P := P) (p := p) (q := q) (o 3) (b - 1 - (p - 1))
  have h5 := F.toFrame5.rowLine_pos (o 4) (y := p - 1 - y5) (by omega)
    (by simp [Orient.H, h4]; omega)
  omega

/-- `report-A2.md`, 6.3, type (v, v, h, v), (ii): `F` of `T_5` at the bottom of
its box. `mu = L`, so `r_{m_4} = r_{m_1} + r_{m_2}`; `m_4 = A` is impossible;
`m_4 = C` gives `m_1 = m_2 = A`, `L = 2r`, `a = 2L`; then `T_1`, `T_2` fill row
`L - 1`, but `T_5` meets it (`M > L`): (13) (`vb_13`). -/
theorem o63_vvhv_ii (F : FrameO P p q a b t o x5 y5) (S : AdjFull P p q)
    (h0 : (o 0).swap = true) (h1 : (o 1).swap = true) (_h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) (_h2x : (o 2).negX = true) (V : SetupV P p q a b o)
    (h4 : (o 4).swap = false) (h4y : (o 4).negY = false) : False := by
  have hbot := F.side_bottom
  have h13 := vb_13 F V h4
  have hmu : (o 4).rowLine p q P 0 = p := by simpa [Orient.rowLine, h4, h4y] using S.fullF
  have ha := V.ha
  have hr1 := S.rA_pos
  have hrq := S.rA_lt
  have hq := V.hq
  rw [vb_u V.hrC h0, vb_u V.hrC h1, hmu] at hbot
  rw [vb_far V.hrC h0, vb_far V.hrC h1] at h13
  rw [vb_u V.hrC h3] at ha
  cases x0 : (o 0).negX <;> cases x1 : (o 1).negX <;> cases x3 : (o 3).negX <;>
    simp [x0, x1, x3] at hbot h13 ha <;> omega

/-- `report-A2.md`, 6.3, type (v, v, h, v), (iii), first bullet: `m_1 = m_2 = A`.
(13) gives `2L ≤ L + r_{m_4} - 1`, so `m_4 = A`, `r ≥ L + 1` and
`f = L + r - 2r < 0`. -/
theorem o63_vvhv_iii_AA (F : FrameO P p q a b t o x5 y5) (S : AdjFull P p q)
    (h0 : (o 0).swap = true) (h1 : (o 1).swap = true) (_h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) (_h2x : (o 2).negX = true) (V : SetupV P p q a b o)
    (h4 : (o 4).swap = false) (h4y : (o 4).negY = true) (m0 : (o 0).negX = false)
    (m1 : (o 1).negX = false) : False := by
  have hbot := F.side_bottom
  have h13 := vb_13 F V h4
  have hmu : (o 4).rowLine p q P 0 = rowCount P (q - 1) := by
    simp [Orient.rowLine, h4, h4y]
  have ha := V.ha
  have hf := S.f_pos
  rw [vb_u V.hrC h0, vb_u V.hrC h1, hmu, m0, m1] at hbot
  rw [vb_far V.hrC h0, vb_far V.hrC h1, m0, m1] at h13
  rw [vb_u V.hrC h3] at ha
  cases x3 : (o 3).negX <;> simp [x3] at hbot h13 ha <;> omega

/-- `report-A2.md`, 6.3, type (v, v, h, v), (iii), second bullet:
`m_1 = m_2 = C`. `f = r_{m_4} - L ≥ 1`, so `m_4 = A`, `r = L + f`, and (13) gives
`2r ≤ L + r - 1`. -/
theorem o63_vvhv_iii_CC (F : FrameO P p q a b t o x5 y5) (S : AdjFull P p q)
    (h0 : (o 0).swap = true) (h1 : (o 1).swap = true) (_h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) (_h2x : (o 2).negX = true) (V : SetupV P p q a b o)
    (h4 : (o 4).swap = false) (h4y : (o 4).negY = true) (m0 : (o 0).negX = true)
    (m1 : (o 1).negX = true) : False := by
  have hbot := F.side_bottom
  have h13 := vb_13 F V h4
  have hmu : (o 4).rowLine p q P 0 = rowCount P (q - 1) := by
    simp [Orient.rowLine, h4, h4y]
  have ha := V.ha
  have hf := S.f_pos
  rw [vb_u V.hrC h0, vb_u V.hrC h1, hmu, m0, m1] at hbot
  rw [vb_far V.hrC h0, vb_far V.hrC h1, m0, m1] at h13
  rw [vb_u V.hrC h3] at ha
  cases x3 : (o 3).negX <;> simp [x3] at hbot h13 ha <;> omega

/-- `report-A2.md`, 6.3, type (v, v, h, v), (iii), third bullet, the lines
shared by its two cases: "{m_1, m_2} = {A, C}: f = r_{m_4} - r >= 1, so m_4 = C,
a = 2L, f = L-r, r < L. 1 <= x_5 <= L-1. T_3 has at the far end A of its F, in
column L, the rows [2L-r, 2L). (L, M-1) is in T_5; so M <= 2L-r." -/
private theorem vb_mixed (F : FrameO P p q a b t o x5 y5) (S : AdjFull P p q)
    (h0 : (o 0).swap = true) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) (h2x : (o 2).negX = true) (V : SetupV P p q a b o)
    (h4 : (o 4).swap = false) (h4y : (o 4).negY = true) (hm : (o 0).negX ≠ (o 1).negX) :
    o 3 = ⟨true, true, false⟩ ∧ a = 2 * p ∧ rowCount P (q - 1) = p - colCount P 0 ∧
      colCount P 0 < p ∧ 1 ≤ x5 ∧ x5 ≤ p - 1 ∧ q ≤ 2 * p - colCount P 0 := by
  have hbot := F.side_bottom
  have hmu : (o 4).rowLine p q P 0 = rowCount P (q - 1) := by
    simp [Orient.rowLine, h4, h4y]
  have ha := V.ha
  have hf := S.f_pos
  rw [vb_u V.hrC h0, vb_u V.hrC h1, hmu] at hbot
  rw [vb_u V.hrC h3] at ha
  have key : (o 3).negX = true ∧ a = 2 * p ∧ rowCount P (q - 1) = p - colCount P 0 := by
    cases x0 : (o 0).negX <;> cases x1 : (o 1).negX <;> cases x3 : (o 3).negX <;>
      simp [x0, x1, x3] at hm hbot ha ⊢ <;> omega
  obtain ⟨x3, ha2, hf2⟩ := key
  have e3 : o 3 = ⟨true, true, false⟩ :=
    Orient.ext h3 x3 (S.toAdjacent.mark F.toFrame5 (i := 3) (by decide))
  have hx5 := F.x5_pos
  have hx5' := F.x5_le
  simp only [Orient.W, h4, Bool.false_eq_true, ite_false] at hx5'
  refine ⟨e3, ha2, hf2, by omega, hx5, by omega, ?_⟩
  -- the cell `(L, M - 1)` is in `T_5`, and otherwise in `T_3`
  by_contra hlt
  have hy5 := F.y5_eq
  have hq := V.hq
  have row0 := (F.toFrame5.rowCount_eq_iff 0).1 S.fullF
  have c4 : ((p, q - 1) : Cell) ∈ t 4 := by
    cases x4 : (o 4).negX
    · exact (F.toFrame5.mem_of 4 (d := (p - x5, 0))
        (by simp [loc, Orient.back, h4, h4y, x4, hy5])).2
        (row0 _ (by omega) (by omega))
    · exact (F.toFrame5.mem_of 4 (d := (x5 - 1, 0))
        (by simp [loc, Orient.back, h4, h4y, x4, hy5])).2
        (row0 _ (by omega) (by omega))
  have e2 : o 2 = ⟨false, true, false⟩ :=
    Orient.ext h2 h2x (S.toAdjacent.mark F.toFrame5 (i := 2) (by decide))
  have c2 : ((p, q - 1) : Cell) ∈ t 2 :=
    (F.toFrame5.mem_of 2 (d := (0, 2 * p - q))
      (by simp [loc, e2, Orient.back, ha2, V.hb]; omega)).2
      ((V.colA _).2 ⟨by omega, by omega⟩)
  exact Finset.disjoint_left.1 (F.tiling.disjoint 2 4 (by decide)) c2 c4

/-- `report-A2.md`, 6.3, type (v, v, h, v), (iii), third bullet, first case:
`(m_1, m_2) = (A, C)`. Then `m_4 = C`, `a = 2L`, `f = L - r`, `M ≤ 2L - r`,
`1 ≤ x5 ≤ r - 1` (`vb_mixed`, and the lower left corner of `box(T_5)` is not
occupied); `T_4` contains `(x5, L)`. `C` at the upper left corner of `box(T_5)`
puts `(x5, L)` in `T_5`; so `A` is there, `L + r + 1 ≤ M`, and the column and
the row at distance `c = 2L - M` from the right and from the top give `2f = L`,
against `2r + 1 ≤ L`. -/
theorem o63_vvhv_iii_AC (F : FrameO P p q a b t o x5 y5) (S : AdjFull P p q)
    (h0 : (o 0).swap = true) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) (h2x : (o 2).negX = true) (V : SetupV P p q a b o)
    (h4 : (o 4).swap = false) (h4y : (o 4).negY = true) (m0 : (o 0).negX = false)
    (m1 : (o 1).negX = true) : False := by
  obtain ⟨e3, ha2, hf, hr, hx5, hx5', hqr⟩ :=
    vb_mixed F S h0 h1 h2 h3 h2x V h4 h4y (by rw [m0, m1]; decide)
  have hy5 := F.y5_eq
  have hpq := V.hpq
  have hq := V.hq
  have hr1 := S.rA_pos
  have hmu : (o 4).rowLine p q P 0 = rowCount P (q - 1) := by
    simp [Orient.rowLine, h4, h4y]
  -- `x5 < r`: the lower left corner of `box(T_5)` is not occupied
  have hx5r : x5 < colCount P 0 := by
    have hout : ((x5, 0) : Cell) ∉ t 4 := by
      intro h
      cases x4 : (o 4).negX
      · exact S.h01 ((F.toFrame5.mem_of 4 (d := (0, q - 1))
          (by simp [loc, Orient.back, h4, h4y, x4, hy5])).1 h)
      · exact S.h11 ((F.toFrame5.mem_of 4 (d := (p - 1, q - 1))
          (by simp [loc, Orient.back, h4, h4y, x4, hy5])).1 h)
    rw [F.bottom4, vb_u V.hrC h0, m0, hmu] at hout
    simp at hout
    omega
  -- `(x5, L)` is in `T_4`
  have c3 : ((x5, p) : Cell) ∈ t 3 :=
    (F.toFrame5.mem_of 3 (d := (0, x5)) (by simp [loc, e3, Orient.back, V.hb]; omega)).2
      ((V.colA _).2 ⟨by omega, hx5r⟩)
  cases x4 : (o 4).negX
  · -- `A` at the upper left corner of `box(T_5)`: `L + r + 1 ≤ M`
    have hqr' : p + colCount P 0 + 1 ≤ q := by
      by_contra hlt
      have c4 : ((x5, p) : Cell) ∈ t 4 :=
        (F.toFrame5.mem_of 4 (d := (0, q - 1 - p))
          (by simp [loc, Orient.back, h4, h4y, x4, hy5])).2 ((V.colA _).2 ⟨by omega, by omega⟩)
      exact Finset.disjoint_left.1 (F.tiling.disjoint 3 4 (by decide)) c3 c4
    have e0 : o 0 = ⟨true, false, false⟩ :=
      Orient.ext h0 m0 (S.toAdjacent.mark F.toFrame5 (i := 0) (by decide))
    have e1 : o 1 = ⟨true, true, false⟩ :=
      Orient.ext h1 m1 (S.toAdjacent.mark F.toFrame5 (i := 1) (by decide))
    have e2 : o 2 = ⟨false, true, false⟩ :=
      Orient.ext h2 h2x (S.toAdjacent.mark F.toFrame5 (i := 2) (by decide))
    have e4 : o 4 = ⟨false, false, true⟩ := Orient.ext h4 x4 h4y
    have c1 := F.toFrame5.col_sum (x := q - 1) (by omega) (by omega)
    have r1 := F.toFrame5.row_sum (y := q - 1) (by omega) (by rw [V.hb]; omega)
    rw [e0, e1, e2, e3, e4] at c1 r1
    simp only [Orient.colLine_wide, Orient.colLine_wide_neg, Orient.colLine_tall,
      Orient.rowLine_wide, Orient.rowLine_wide_neg,
      Orient.rowLine_tall, Orient.rowLine_tall_neg] at c1 r1
    simp (disch := omega) only [F.toFrame5.colCount_zero, add_zero,
      zero_add] at c1 r1
    have l0 : rowCount P (q - 1 - (q - 1 - y5)) = p := by
      rw [show q - 1 - (q - 1 - y5) = (0 : ℤ) by omega]; exact S.fullF
    have k1 : rowCount P (a - 1 - (q - 1)) = rowCount P (b - 1 - (q - 1)) := by
      congr 1; rw [ha2, V.hb]
    have k2 : colCount P (p - 1 - (a - 1 - (q - 1))) =
        colCount P (p - 1 - (b - 1 - (q - 1))) := by
      congr 1; rw [ha2, V.hb]
    rw [V.hb] at c1
    omega
  · -- `C` at the upper left corner of `box(T_5)`: `(x5, L)` is in `T_5`
    have c4 : ((x5, p) : Cell) ∈ t 4 :=
      (F.toFrame5.mem_of 4 (d := (p - 1, q - 1 - p))
        (by simp [loc, Orient.back, h4, h4y, x4, hy5])).2 ((V.colC _).2 ⟨by omega, by omega⟩)
    exact Finset.disjoint_left.1 (F.tiling.disjoint 3 4 (by decide)) c3 c4

/-- `report-A2.md`, 6.3, type (v, v, h, v), (iii), third bullet, second case:
`(m_1, m_2) = (C, A)`. With `o = L - x5` (the right margin of `box(T_5)`),
`1 ≤ o ≤ r - 1` (`vb_mixed`, and the lower right corner of `box(T_5)` is not
occupied); the column and the row at distance `c = o` from the right and from
the top give `X_e(0) = 0` for the corner `e` of `P` at the upper right corner
of `box(T_5)`: for `e = A` this is the report's `X_A(0) = 0`; for `e = C` it
is `L = 0` (the report excludes `C` there by a cell of row `L - 1`). -/
theorem o63_vvhv_iii_CA (F : FrameO P p q a b t o x5 y5) (S : AdjFull P p q)
    (h0 : (o 0).swap = true) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) (h2x : (o 2).negX = true) (V : SetupV P p q a b o)
    (h4 : (o 4).swap = false) (h4y : (o 4).negY = true) (m0 : (o 0).negX = true)
    (m1 : (o 1).negX = false) : False := by
  obtain ⟨e3, ha2, hf, hr, hx5, hx5', hqr⟩ :=
    vb_mixed F S h0 h1 h2 h3 h2x V h4 h4y (by rw [m0, m1]; decide)
  have hy5 := F.y5_eq
  have hpq := V.hpq
  have hq := V.hq
  have hr1 := S.rA_pos
  have hp := F.toFrame5.two_le_p
  have hmu : (o 4).rowLine p q P 0 = rowCount P (q - 1) := by
    simp [Orient.rowLine, h4, h4y]
  -- `x5 ≥ L - r + 1`: the lower right corner of `box(T_5)` is not occupied
  have hx5r : p - colCount P 0 + 1 ≤ x5 := by
    have hout : ((x5 + p - 1, 0) : Cell) ∉ t 4 := by
      intro h
      cases x4 : (o 4).negX
      · exact S.h11 ((F.toFrame5.mem_of 4 (d := (p - 1, q - 1))
          (by simp [loc, Orient.back, h4, h4y, x4, hy5]; omega)).1 h)
      · exact S.h01 ((F.toFrame5.mem_of 4 (d := (0, q - 1))
          (by simp [loc, Orient.back, h4, h4y, x4, hy5]; omega)).1 h)
    rw [F.bottom4, vb_u V.hrC h0, m0, hmu] at hout
    simp at hout
    omega
  have e0 : o 0 = ⟨true, true, false⟩ :=
    Orient.ext h0 m0 (S.toAdjacent.mark F.toFrame5 (i := 0) (by decide))
  have e1 : o 1 = ⟨true, false, false⟩ :=
    Orient.ext h1 m1 (S.toAdjacent.mark F.toFrame5 (i := 1) (by decide))
  have e2 : o 2 = ⟨false, true, false⟩ :=
    Orient.ext h2 h2x (S.toAdjacent.mark F.toFrame5 (i := 2) (by decide))
  have c1 := F.toFrame5.col_sum (x := p - 1 + x5) (by omega) (by omega)
  have r1 := F.toFrame5.row_sum (y := p - 1 + x5) (by omega) (by rw [V.hb]; omega)
  have k1 : rowCount P (a - 1 - (p - 1 + x5)) = rowCount P (b - 1 - (p - 1 + x5)) := by
    congr 1; rw [ha2, V.hb]
  have k2 : colCount P (p - 1 - (a - 1 - (p - 1 + x5))) =
      colCount P (p - 1 - (b - 1 - (p - 1 + x5))) := by
    congr 1; rw [ha2, V.hb]
  have hrC := V.hrC
  rw [e0, e1, e2, e3] at c1 r1
  cases x4 : (o 4).negX
  · have e4 : o 4 = ⟨false, false, true⟩ := Orient.ext h4 x4 h4y
    rw [e4] at c1 r1
    simp only [Orient.colLine_wide, Orient.colLine_wide_neg, Orient.colLine_tall,
      Orient.rowLine_wide, Orient.rowLine_wide_neg,
      Orient.rowLine_tall, Orient.rowLine_tall_neg] at c1 r1
    simp (disch := omega) only [F.toFrame5.rowCount_zero, F.toFrame5.colCount_zero, add_zero,
      zero_add] at c1 r1
    have k3 : colCount P (p - 1 + x5 - x5) = p := by
      rw [show p - 1 + x5 - x5 = p - 1 by omega]; exact hrC
    rw [V.hb] at c1
    omega
  · have e4 : o 4 = ⟨false, true, true⟩ := Orient.ext h4 x4 h4y
    rw [e4] at c1 r1
    simp only [Orient.colLine_wide_neg, Orient.colLine_tall,
      Orient.rowLine_wide, Orient.rowLine_wide_neg,
      Orient.rowLine_tall, Orient.rowLine_tall_neg] at c1 r1
    simp (disch := omega) only [F.toFrame5.rowCount_zero, F.toFrame5.colCount_zero, add_zero,
      zero_add] at c1 r1
    have k3 : colCount P (p - 1 - (p - 1 + x5 - x5)) = colCount P 0 := by
      congr 1; omega
    rw [V.hb] at c1
    omega

/-- `report-A2.md`, 6.3, type (v, v, h, v), with `m_3 = C`. -/
theorem o63_vvhv_norm (F : FrameO P p q a b t o x5 y5) (S : AdjFull P p q)
    (h0 : (o 0).swap = true) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) (h2x : (o 2).negX = true) : False := by
  have V := o63_vvhv_setup F S h0 h1 h2 h3 h2x
  cases h4 : (o 4).swap
  · cases h4y : (o 4).negY
    · exact o63_vvhv_ii F S h0 h1 h2 h3 h2x V h4 h4y
    · cases m0 : (o 0).negX <;> cases m1 : (o 1).negX
      · exact o63_vvhv_iii_AA F S h0 h1 h2 h3 h2x V h4 h4y m0 m1
      · exact o63_vvhv_iii_AC F S h0 h1 h2 h3 h2x V h4 h4y m0 m1
      · exact o63_vvhv_iii_CA F S h0 h1 h2 h3 h2x V h4 h4y m0 m1
      · exact o63_vvhv_iii_CC F S h0 h1 h2 h3 h2x V h4 h4y m0 m1
  · exact o63_vvhv_i F S h0 h1 h2 h3 h2x V h4

/-- **`report-A2.md`, 6.3, type (v, v, h, v)** ("Name m_3 = C": the mirror image
of `P` in the vertical midline of its box exchanges `A` and `C`). -/
theorem o63_vvhv (F : FrameO P p q a b t o x5 y5) (S : Adjacent P p q)
    (h0 : (o 0).swap = true) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) : False := by
  cases hx : (o 2).negX
  · exact o63_vvhv_norm F.flipPX (S.flipPX.full F.flipPX.toFrame5) (by simpa using h0)
      (by simpa using h1) (by simpa using h2) (by simpa using h3) (by simp [hx])
  · exact o63_vvhv_norm F (S.full F.toFrame5) h0 h1 h2 h3 hx

/-- **`report-A2.md`, 6.3.** Pattern O with two adjacent occupied corners does
not occur. -/
theorem adj_O (F : FrameO P p q a b t o x5 y5) (S : Adjacent P p q) : False := by
  have S' := S.full F.toFrame5
  rcases o63_types F S' with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ |
    ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩
  · exact o63_hvhv F S' h0 h1 h2 h3
  · obtain ⟨t', F'⟩ := F.flipX
    exact o63_hvhv F' S' (by simpa using h1) (by simpa using h0) (by simpa using h3)
      (by simpa using h2)
  · exact o63_vvhh F S' h0 h1 h2 h3
  · exact o63_vvhv F S h0 h1 h2 h3
  · obtain ⟨t', F'⟩ := F.flipX
    exact o63_vvhv F' S (by simpa using h1) (by simpa using h0) (by simpa using h3)
      (by simpa using h2)

end PolyominoOddOrder
