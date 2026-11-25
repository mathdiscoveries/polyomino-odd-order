module

public import PolyominoOddOrder.ThreeCorners

/-!
# Case (I), three occupied corners, pattern O, `T_5` tall (`ThreeOTall.lean`)

Blueprint unit C3 (third increment). `report-A2.md`, section 5.3, up to the end
of "T_5 tall": the column `x*` of the full vertical side of `T_5` (`xStar`), the
barrier (4) (`o53_four`), `p = q` (`o53_sq`), and for a tall `T_5` the cases (a),
(b), (c) by the numbers of wide tiles at the bottom and on top.

| report | Lean |
|---|---|
| `x*` | `xStar (o 4) p q x5` |
| "reflect R so that x* = x_5" | `(o 4).revH = false`, by `FrameO.flipX` |
| (5), (6) of case (b) | `SetupB.h5`, `SetupB.h6` |
| (7), (8) of case (c) | `SetupC.h7`, `SetupC.h8` |

Entry statements (binding): `o53_four`, `o53_sq` (used by `ThreeOWide.lean`) and
`o53_tall`. A proof unit may reshape the nodes marked PROVISIONAL.

Source: `theoretician/report-A2.md` (goals lab, commit `076d663`), section 5.3.
-/

@[expose] public section

namespace PolyominoOddOrder

open Orient (cornerP)

variable {P : Finset Cell} {p q a b : ℤ} {t : Fin 5 → Finset Cell} {o : Fin 5 → Orient}
  {x5 y5 : ℤ}

/-! ## The full vertical side of `T_5`, (4), `p = q` -/

/-- The column `x*` of the full vertical side of `T_5` (`report-A2.md`, 5.3,
first line): the first or the last column of `box(T_5)`. -/
def xStar (c : Orient) (p q x5 : ℤ) : ℤ := if c.revH then x5 + c.W p q - 1 else x5

/-- `report-A2.md`, 5.3, first line: `T_5` has a full vertical side, in the
column `x*`. The full side is `EB` for a wide `T_5` and `EA` for a tall one
(`ThreeFull.fullEB`, `fullEA` with `Frame5.colCount_eq_iff`,
`rowCount_eq_iff`). -/
theorem o53_xstar_col (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) :
    ∀ y : ℤ, 0 ≤ y → y < (o 4).H p q → ((xStar (o 4) p q x5, y) : Cell) ∈ t 4 := by
  intro y hy0 hy1
  have hA : ∀ X Y : ℤ, Y = 0 → 0 ≤ X → X < p → ((X, Y) : Cell) ∈ P := by
    rintro X Y rfl
    exact (F.toFrame5.rowCount_eq_iff 0).1 S.fullEA X
  have hB : ∀ X Y : ℤ, X = 0 → 0 ≤ Y → Y < q → ((X, Y) : Cell) ∈ P := by
    rintro X Y rfl
    exact (F.toFrame5.colCount_eq_iff 0).1 S.fullEB Y
  rw [F.toFrame5.mem4, F.y5_eq, sub_zero]
  generalize o 4 = c at hy1 ⊢
  -- the local column of `x*` is column `0` of `box(P)` (wide) or row `0` (tall)
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;>
    simp only [xStar, Orient.revH, Orient.W, Orient.H, Orient.back, ite_true, ite_false,
      Bool.false_eq_true] at hy1 ⊢ <;>
    first
    | (refine hB _ _ ?_ ?_ ?_ <;> omega)
    | (refine hA _ _ ?_ ?_ ?_ <;> omega)

/-- **`report-A2.md`, 5.3, (4).** By (T3) with `h = H_5`: if `H_1 ≤ H_5` then
`W_1 ≤ x*`; if `H_2 ≤ H_5` then `W_2 ≤ a - 1 - x*`. -/
theorem o53_four (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) :
    ((o 0).H p q ≤ (o 4).H p q → (o 0).W p q ≤ xStar (o 4) p q x5) ∧
      ((o 1).H p q ≤ (o 4).H p q → (o 1).W p q ≤ a - 1 - xStar (o 4) p q x5) :=
  ⟨fun h => F.T3_left (o53_xstar_col F S) h, fun h => F.T3_right (o53_xstar_col F S) h⟩

/-- **`report-A2.md`, 5.3, "p = q".** (4) gives `2p ≤ a - 1`, and (1) gives
`a = u_3 + u_4 ≤ 2p`. -/
theorem o53_sq (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hpq : p = q) :
    False := by
  subst hpq
  obtain ⟨hl, hr⟩ := o53_four F S
  have hH : ∀ c : Orient, c.H p p = p := fun c => by simp [Orient.H]
  have hW : ∀ c : Orient, c.W p p = p := fun c => by simp [Orient.W]
  have hl' := hl (by rw [hH, hH])
  have hr' := hr (by rw [hH, hH])
  have ht := F.side_top
  have b2 := (F.toFrame5.hrun_bounds 2).2
  have b3 := (F.toFrame5.hrun_bounds 3).2
  rw [hW] at hl' hr' b2 b3
  omega

/-! ## `T_5` tall -/

/-- `report-A2.md`, 5.3, "T_5 tall", first sentence: (4) applies to both, so
`W_1 + W_2 ≤ a - 1 < W_3 + W_4`. -/
theorem o53_tall_count (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = true) :
    (o 0).W p q + (o 1).W p q < (o 2).W p q + (o 3).W p q := by
  obtain ⟨hl, hr⟩ := o53_four F S
  have h5 : (o 4).H p q = p := by simp [Orient.H, h4]
  have hH0 : (o 0).H p q ≤ p := by
    cases h : (o 0).swap <;> simp [Orient.H, h]
    omega
  have hH1 : (o 1).H p q ≤ p := by
    cases h : (o 1).swap <;> simp [Orient.H, h]
    omega
  have hl' := hl (by omega)
  have hr' := hr (by omega)
  have ht := F.side_top
  have b2 := (F.toFrame5.hrun_bounds 2).2
  have b3 := (F.toFrame5.hrun_bounds 3).2
  omega

/-- **`report-A2.md`, 5.3 (a).** One wide tile on top, none at the bottom. The
side with two tall tiles has `b = 2p` by Lemma 5.1; the other side has
`b ≤ p + q`. (The report reflects so that `T_4` is the wide one; here both
positions are done.) -/
theorem o53_a (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h0 : (o 0).swap = true) (h1 : (o 1).swap = true) (h23 : (o 2).swap ≠ (o 3).swap) :
    False := by
  have hl := F.side_left
  have hr := F.side_right
  have b0 := (F.toFrame5.vrun_bounds 0).2
  have b1 := (F.toFrame5.vrun_bounds 1).2
  have b2 := (F.toFrame5.vrun_bounds 2).2
  have b3 := (F.toFrame5.vrun_bounds 3).2
  cases h2 : (o 2).swap
  · have h3 : (o 3).swap = true := by
      revert h23; rw [h2]; cases (o 3).swap <;> simp
    obtain ⟨e0, e3⟩ := lemma51_left F.toFrame5 S hq F.x5_pos (h0.trans h3.symm)
    simp [Orient.H, h0, h1, h2, h3] at b0 b1 b2 b3 e0 e3
    omega
  · have h3 : (o 3).swap = false := by
      revert h23; rw [h2]; cases (o 3).swap <;> simp
    obtain ⟨e1, e2⟩ := lemma51_right F.toFrame5 S hq F.x5_le (h1.trans h2.symm)
    simp [Orient.H, h0, h1, h2, h3] at b0 b1 b2 b3 e1 e2
    omega

/-- The facts of `report-A2.md`, 5.3 (b), before the split on the mark of
`T_3` (`T_1` wide, `T_2` tall, `T_3`, `T_4` wide, `T_5` tall): `a = 2p`,
`b = 2q`, `p < 2q`, `x* = x5 + q - 1`, `x5 = 2p - 2q`, the mark of `T_4` is `E`,
the mark of `T_2` is `E` or `B`, the mark of `T_3` is `E` or `A`, (5), (6). -/
structure SetupB (P : Finset Cell) (p q a b : ℤ) (o : Fin 5 → Orient) (x5 : ℤ) : Prop where
  /-- Lemma 5.1 on top. -/
  ha : a = 2 * p
  /-- Lemma 5.1 on the left. -/
  hb : b = 2 * q
  /-- `p = H_5 ≤ b - 1`. -/
  hpq : p < 2 * q
  /-- `x* = x5 + q - 1`: the full side `EA` of `T_5` is its right column. -/
  h4y : (o 4).negY = true
  /-- `x5 = 2p - 2q`. -/
  hx5 : x5 = 2 * p - 2 * q
  /-- The mark of `T_4` is `E`. -/
  e3 : o 3 = Orient.wE
  /-- The mark of `T_2` is `E` or `B` (`u_2 = q`). -/
  m1 : (o 1).negX = false
  /-- The mark of `T_3` is `E` or `A` (`u_3 = p`). -/
  m2 : (o 2).negY = false
  /-- (5): `rho_j = p` for `j < 2q - p`. -/
  h5 : ∀ j : ℤ, 0 ≤ j → j < 2 * q - p → rowCount P j = p
  /-- (6): `kappa_c = q` for `c < 2p - 2q`. -/
  h6 : ∀ c : ℤ, 0 ≤ c → c < 2 * p - 2 * q → colCount P c = q

/-- `report-A2.md`, 5.3 (b), from "Lemma 5.1: on top a = 2p" to "(6) kappa_c = q
for c < 2p - 2q. T_3 has u_3 = p, so its mark is E or A." PROVISIONAL (the unit
may split it: dimensions; the cell `(p - 1, q)` and `x*`; (5); (6)). -/
theorem o53_b_setup (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = true) (h0 : (o 0).swap = false) (h1 : (o 1).swap = true)
    (h2 : (o 2).swap = false) (h3 : (o 3).swap = false) : SetupB P p q a b o x5 := by
  have F5 := F.toFrame5
  have hy5 := F.y5_eq
  have hq2 := F5.two_le_q
  have hW0 : (o 0).W p q = p := by simp [Orient.W, h0]
  have hH0 : (o 0).H p q = q := by simp [Orient.H, h0]
  have hW1 : (o 1).W p q = q := by simp [Orient.W, h1]
  have hH1 : (o 1).H p q = p := by simp [Orient.H, h1]
  have hW2 : (o 2).W p q = p := by simp [Orient.W, h2]
  have hH2 : (o 2).H p q = q := by simp [Orient.H, h2]
  have hW3 : (o 3).W p q = p := by simp [Orient.W, h3]
  have hH3 : (o 3).H p q = q := by simp [Orient.H, h3]
  have hW4 : (o 4).W p q = q := by simp [Orient.W, h4]
  have hH4 : (o 4).H p q = p := by simp [Orient.H, h4]
  -- dimensions: Lemma 5.1 on top and on the left, and `H_5 ≤ b - 1`
  obtain ⟨u2, u3⟩ := lemma51_top F5 S hq F.y5_le (h2.trans h3.symm)
  obtain ⟨v0, v3⟩ := lemma51_left F5 S hq F.x5_pos (h0.trans h3.symm)
  have ht := F.side_top
  have hl := F.side_left
  have ha : a = 2 * p := by omega
  have hb : b = 2 * q := by omega
  have hpq : p < 2 * q := by have := F.h5_le; omega
  -- marks: a run along a full side of `box(P)` is not `alpha` or `beta`
  have hal := S.alpha_lt
  have hbe := S.beta_lt
  have m0 : (o 0).negX = false := by
    cases hx : (o 0).negX
    · rfl
    · simp [Orient.colLine, h0, hx] at v0
      omega
  have m2 : (o 2).negY = false := by
    cases hy : (o 2).negY
    · rfl
    · simp [Orient.rowLine, h2, hy] at u2
      omega
  have e3 : o 3 = Orient.wE := by
    have hx : (o 3).negX = false := by
      cases hx : (o 3).negX
      · rfl
      · simp [Orient.colLine, h3, hx] at v3
        omega
    have hy : (o 3).negY = false := by
      cases hy : (o 3).negY
      · rfl
      · simp [Orient.rowLine, h3, hy] at u3
        omega
    exact Orient.ext h3 hx hy
  -- the corner `D = (p - 1, q)` of `T_4` lies in `T_5`, so `x5 ≤ p - 1 < x*`
  have h4y : (o 4).negY = true := by
    have hc : ((p - 1, q) : Cell) ∈ R a b := by
      rw [mem_R]; simp only; omega
    have hx4 : x5 ≤ p - 1 := by
      rcases F5.cover_cases hc with h | h | h | h | h
      · have := h.2.2; simp only at this; omega
      · have := h.2.1; simp only at this; omega
      · have := h.2.1; simp only at this; omega
      · exfalso
        refine S.hD ((F5.mem_of 3 (d := (p - 1, q - 1)) ?_).1 h.1)
        simp [loc, e3, Orient.wE, Orient.back]
        omega
      · exact h.2.1.1
    have hl4 := (o53_four F S).1 (by omega)
    cases hy : (o 4).negY
    · simp [xStar, Orient.revH, h4, hy] at hl4
      omega
    · rfl
  -- `x5 = 2p - 2q`: (4) on the right, and the bottom row of `T_5` ends at `x*`
  have hxs : xStar (o 4) p q x5 = x5 + q - 1 := by
    simp [xStar, Orient.revH, Orient.W, h4, h4y]
  have hr4 := (o53_four F S).2 (by omega)
  rw [hxs] at hr4
  have hsb := F.side_bottom
  have hmu := F.mu_pos
  have hu0 := (F5.hrun_bounds 0).1
  have hlast := (F.bottom4 ((o 0).rowLine p q P 0 + (o 4).rowLine p q P 0 - 1)).2
    ⟨by omega, by omega⟩
  have hbx := (F5.box4 hlast).1.2
  simp only at hbx
  have hu1 := (F5.hrun_bounds 1).2
  have hx5 : x5 = 2 * p - 2 * q := by omega
  -- `u_2 = q`: the mark of `T_2` is `E` or `B`
  have hu2 : (o 1).rowLine p q P 0 = q := by omega
  have m1 : (o 1).negX = false := by
    cases hx : (o 1).negX
    · rfl
    · simp [Orient.rowLine, h1, hx] at hu2
      omega
  -- (5): the rows `[p, 2q)` of `R` lie in `T_3` and `T_4` alone
  have h5 : ∀ j : ℤ, 0 ≤ j → j < 2 * q - p → rowCount P j = p := by
    intro j hj0 hj1
    have hs := F5.row_sum (y := b - 1 - j) (by omega) (by omega)
    rw [F5.rowLine_zero (o 0) (y := b - 1 - j) (Or.inr (by omega)),
      F5.rowLine_zero (o 1) (y := b - 1 - j) (Or.inr (by omega)),
      F5.rowLine_zero (o 4) (y := b - 1 - j - y5) (Or.inr (by omega)),
      show b - 1 - (b - 1 - j) = j by ring, e3] at hs
    have l2 := F5.rowLine_le (o 2) j
    have l3 := F5.rowCount_le j
    simp only [Orient.wE, Orient.rowLine_wide] at hs
    omega
  -- (6): the columns `[0, x5)` of `R` lie in `T_1` and `T_4` alone
  have h6 : ∀ c : ℤ, 0 ≤ c → c < 2 * p - 2 * q → colCount P c = q := by
    intro c hc0 hc1
    have hs := F5.col_sum (x := c) hc0 (by omega)
    rw [F5.colLine_zero (o 1) (x := a - 1 - c) (Or.inr (by omega)),
      F5.colLine_zero (o 2) (x := a - 1 - c) (Or.inr (by omega)),
      F5.colLine_zero (o 4) (x := c - x5) (Or.inl (by omega)), e3] at hs
    have e0 : (o 0).colLine p q P c = colCount P c := by simp [Orient.colLine, h0, m0]
    simp only [Orient.wE, Orient.colLine_wide] at hs
    omega
  exact ⟨ha, hb, hpq, h4y, hx5, e3, m1, m2, h5, h6⟩

/-- `report-A2.md`, 5.3 (b), "Mark A": `EB` of `T_3` is its column `p`, by (6)
`T_3` contains `[p, 3p - 2q) x [q, 2q)`, so it contains `(x*, q)`, which is in
`T_5`. -/
theorem o53_b_A (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = true) (_h0 : (o 0).swap = false) (_h1 : (o 1).swap = true)
    (B : SetupB P p q a b o x5) (e2 : o 2 = Orient.wA) : False := by
  have hq2 := F.toFrame5.two_le_q
  have hH4 : (o 4).H p q = p := by simp [Orient.H, h4]
  have hxs : xStar (o 4) p q x5 = 2 * p - 1 - q := by
    simp [xStar, Orient.revH, Orient.W, h4, B.h4y, B.hx5]
    omega
  -- `(x*, q)` is in `T_5`
  have h45 := o53_xstar_col F S q (by omega) (by omega)
  rw [hxs] at h45
  -- and in `T_3`: its local position is `(q, q - 1)`, the cell `(p - 1 - q, q - 1)` of `P`
  have hcol := (F.toFrame5.colCount_eq_iff (p - 1 - q)).1 (B.h6 _ (by omega) (by omega))
  have h25 : ((2 * p - 1 - q, q) : Cell) ∈ t 2 := by
    refine (F.toFrame5.mem_of 2 (d := (p - 1 - q, q - 1)) ?_).2 (hcol _ (by omega) (by omega))
    simp [loc, e2, Orient.wA, Orient.back, B.ha, B.hb]
    omega
  exact Finset.disjoint_left.1 (F.tiling.disjoint 2 4 (by decide)) h25 h45

/-- `report-A2.md`, 5.3 (b), "Mark E": `v_3 = q`, `v_2 = q < p`, so the mark of
`T_2` is `B` and `beta = q`; by (5) `T_2` contains `[2p - q, p + q) x [0, p)`;
by (6) `2p - 2q ≤ beta = q`; `T_5` and `T_2` contain `[p, p + q) x [q, p)`, so
`T_3` has no cell there; `T_3`, `T_4` are mirror images, so `T_4` has no cell in
`[p - q, p) x [q, p)`; `T_5` contains these cells, so `x5 ≤ p - q`, against
`x5 = 2p - 2q`.

The proof here needs one cell of that argument and not the bound `2p - 2q ≤ q`:
`(p - q, q)` is in no box but `box(T_4)` (it is left of `x5 = 2p - 2q`), so it
is in `T_4`; its mirror image `(p + q - 1, q)` is then in `T_3`, and by (5) it
is in `T_2`. -/
theorem o53_b_E (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (_h4 : (o 4).swap = true) (h0 : (o 0).swap = false) (h1 : (o 1).swap = true)
    (B : SetupB P p q a b o x5) (e2 : o 2 = Orient.wE) : False := by
  have F5 := F.toFrame5
  have hq2 := F5.two_le_q
  have ha := B.ha
  have hb := B.hb
  have hpq := B.hpq
  have hx5 := B.hx5
  -- `v_3 = q`, so `v_2 = b - q = q < p` and the mark of `T_2` is `B`
  have e1 : o 1 = Orient.tB := by
    have hr := F.side_right
    have hy : (o 1).negY = true := by
      cases hy : (o 1).negY
      · simp [Orient.colLine, h1, hy, e2, Orient.wE, S.fullEA, S.fullEB] at hr
        omega
      · rfl
    exact Orient.ext h1 B.m1 hy
  -- the cell `(p - q, q)` lies in `T_4`, by the boxes and `x5 = 2p - 2q`
  have hc : ((p - q, q) : Cell) ∈ R a b := by
    rw [mem_R]; simp only; omega
  have h3c : ((p - q, q) : Cell) ∈ t 3 := by
    rcases F5.cover_cases hc with h | h | h | h | h
    · have := h.2.2; simp [Orient.H, h0] at this
    · have := h.2.1; simp [Orient.W, h1] at this; omega
    · have := h.2.1; simp [e2, Orient.W, Orient.wE] at this; omega
    · exact h.1
    · have := h.2.1.1; simp only at this; omega
  have hP : ((p - q, q - 1) : Cell) ∈ P := by
    refine (F5.mem_of 3 (d := (p - q, q - 1)) ?_).1 h3c
    simp [loc, B.e3, Orient.wE, Orient.back]
    omega
  -- `T_3`, `T_4` are mirror images: `(p + q - 1, q)` is in `T_3`
  have h2c : ((p + q - 1, q) : Cell) ∈ t 2 := by
    refine (F5.mem_of 2 (d := (p - q, q - 1)) ?_).2 hP
    simp [loc, e2, Orient.wE, Orient.back]
    omega
  -- by (5) the same cell is in `T_2`: its cell of `P` is `(q, 2q - 1 - p)`
  have hrow := (F5.rowCount_eq_iff (2 * q - 1 - p)).1 (B.h5 _ (by omega) (by omega))
  have h1c : ((p + q - 1, q) : Cell) ∈ t 1 := by
    refine (F5.mem_of 1 (d := (q, 2 * q - 1 - p)) ?_).2 (hrow _ (by omega) hq)
    simp [loc, e1, Orient.tB, Orient.back]
    omega
  exact Finset.disjoint_left.1 (F.tiling.disjoint 1 2 (by decide)) h1c h2c

/-- **`report-A2.md`, 5.3 (b).** Two wide tiles on top, one at the bottom, `T_1`
the wide one. -/
theorem o53_b (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = true) (h0 : (o 0).swap = false) (h1 : (o 1).swap = true)
    (h2 : (o 2).swap = false) (h3 : (o 3).swap = false) : False := by
  have B := o53_b_setup F S hq h4 h0 h1 h2 h3
  cases hx : (o 2).negX
  · exact o53_b_E F S hq h4 h0 h1 B (Orient.ext h2 hx B.m2)
  · exact o53_b_A F S hq h4 h0 h1 B (Orient.ext h2 hx B.m2)

/-- 5.3 (b) with `T_2` the wide tile at the bottom ("Reflect so that T_1 is
wide, T_2 tall"). -/
theorem o53_b_mirror (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = true) (h0 : (o 0).swap = true) (h1 : (o 1).swap = false)
    (h2 : (o 2).swap = false) (h3 : (o 3).swap = false) : False := by
  obtain ⟨t', F'⟩ := F.flipX
  exact o53_b F' S hq (by simpa using h4) (by simpa using h1) (by simpa using h0)
    (by simpa using h3) (by simpa using h2)

/-- The facts of `report-A2.md`, 5.3 (c), before the split on the place of `E`
in `T_5` (`T_1`, `T_2`, `T_5` tall, `T_3`, `T_4` wide, `x* = x5`): `a = 2p`,
`x5 = q`, `b = p + g` with `1 ≤ g < q`, the marks of `T_3`, `T_4` are `E` or
`A`, the mark of `T_1` is `E` or `B`, (7), (8). -/
structure SetupC (P : Finset Cell) (p q a b : ℤ) (o : Fin 5 → Orient) (x5 : ℤ) : Prop where
  /-- Lemma 5.1 on top. -/
  ha : a = 2 * p
  /-- `x5 = q`. -/
  hx5 : x5 = q
  /-- `g = b - p ≥ 1`. -/
  hb1 : p < b
  /-- `g < q`. -/
  hb2 : b < p + q
  /-- The mark of `T_3` is `E` or `A` (`u_3 = p`). -/
  m2 : (o 2).negY = false
  /-- The mark of `T_4` is `E` or `A` (`u_4 = p`). -/
  m3 : (o 3).negY = false
  /-- The mark of `T_1` is `E` or `B`. -/
  m0 : (o 0).negX = false
  /-- (7): `rho_j = p` for `j < g`. -/
  h7 : ∀ j : ℤ, 0 ≤ j → j < b - p → rowCount P j = p
  /-- (8): `kappa_c = q` for `c < b - q`. -/
  h8 : ∀ c : ℤ, 0 ≤ c → c < b - q → colCount P c = q

/-- A local row of a wide tile with mark `E` or `A` is a row of `P`. -/
private theorem oc_rowLine_wide {c : Orient} (hs : c.swap = false) (hy : c.negY = false)
    (p q : ℤ) (P : Finset Cell) (y : ℤ) : c.rowLine p q P y = rowCount P y := by
  simp [Orient.rowLine, hs, hy]

/-- `report-A2.md`, 5.3 (c), first sentence: "Lemma 5.1: a = 2p, u_3 = u_4 = p.
So the marks of T_3, T_4 are E or A" (the mark `B` has the run `beta < p`). -/
private theorem oc_top (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h2 : (o 2).swap = false) (h3 : (o 3).swap = false) :
    a = 2 * p ∧ (o 2).negY = false ∧ (o 3).negY = false := by
  have ht := F.side_top
  obtain ⟨e2, e3⟩ := lemma51_top F.toFrame5 S hq F.y5_le (h2.trans h3.symm)
  have hb := S.beta_lt
  have hw2 : (o 2).W p q = p := by simp [Orient.W, h2]
  have hw3 : (o 3).W p q = p := by simp [Orient.W, h3]
  rw [hw2] at e2
  rw [hw3] at e3
  refine ⟨by omega, ?_, ?_⟩
  · cases hy : (o 2).negY
    · rfl
    · rw [Orient.hrun_eq] at e2
      simp [h2, hy] at e2
      omega
  · cases hy : (o 3).negY
    · rfl
    · rw [Orient.hrun_eq] at e3
      simp [h3, hy] at e3
      omega

/-- `report-A2.md`, 5.3 (c): "Rows [p, b) lie in T_3 and T_4 alone (H_1 = H_2 =
H_5 = p), so (7) rho_j = p" for `j < g`, read off the row sums (2) of these
rows; and "g < q", since `rho_{q-1} = beta < p`. -/
private theorem oc_rows (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q)
    (h4 : (o 4).swap = true) (h0 : (o 0).swap = true) (h1 : (o 1).swap = true)
    (h2 : (o 2).swap = false) (h3 : (o 3).swap = false) (m2 : (o 2).negY = false)
    (ha : a = 2 * p) :
    (∀ j : ℤ, 0 ≤ j → j < b - p → rowCount P j = p) ∧ b < p + q := by
  have F' := F.toFrame5
  have hp := F'.two_le_p
  have hq2 := F'.two_le_q
  have hy5 := F.y5_eq
  have hH0 : (o 0).H p q = p := by simp [Orient.H, h0]
  have hH1 : (o 1).H p q = p := by simp [Orient.H, h1]
  have hH4 : (o 4).H p q = p := by simp [Orient.H, h4]
  have hW2 : (o 2).W p q = p := by simp [Orient.W, h2]
  have hW3 : (o 3).W p q = p := by simp [Orient.W, h3]
  have h7 : ∀ j : ℤ, 0 ≤ j → j < b - p → rowCount P j = p := by
    intro j hj0 hj1
    have hs := F'.row_sum (y := b - 1 - j) (by omega) (by omega)
    rw [F'.rowLine_zero (o 0) (Or.inr (by omega)), F'.rowLine_zero (o 1) (Or.inr (by omega)),
      F'.rowLine_zero (o 4) (Or.inr (by omega)), show b - 1 - (b - 1 - j) = j by ring] at hs
    have l2 := F'.rowLine_le (o 2) j
    have l3 := F'.rowLine_le (o 3) j
    rw [oc_rowLine_wide h2 m2] at hs l2
    omega
  refine ⟨h7, ?_⟩
  by_contra hne
  have := h7 (q - 1) (by omega) (by omega)
  have := S.beta_lt
  omega

/-- `report-A2.md`, 5.3 (c): "The columns [0, x_5) there lie in T_1 alone (box(T_2)
starts at 2p-q > x_5), so x_5 <= q; with (4), x_5 = q." The cell `(q, 0)` would
lie in no tile if `x5 > q`. -/
private theorem oc_x5 (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = true) (h4y : (o 4).negY = false) (h0 : (o 0).swap = true)
    (h1 : (o 1).swap = true) (h2 : (o 2).swap = false) (h3 : (o 3).swap = false)
    (ha : a = 2 * p) (hb1 : p < b) : x5 = q := by
  have hx : xStar (o 4) p q x5 = x5 := by simp [xStar, Orient.revH, h4, h4y]
  have hl := (o53_four F S).1
  rw [hx] at hl
  have hW0 : (o 0).W p q = q := by simp [Orient.W, h0]
  have hW1 : (o 1).W p q = q := by simp [Orient.W, h1]
  have hH2 : (o 2).H p q = q := by simp [Orient.H, h2]
  have hH3 : (o 3).H p q = q := by simp [Orient.H, h3]
  have hl' : q ≤ x5 := hW0 ▸ hl (by simp [Orient.H, h0, h4])
  have hq2 := F.toFrame5.two_le_q
  by_contra hne
  have hc : ((q, 0) : Cell) ∈ R a b := by rw [mem_R]; simp only; omega
  rcases F.toFrame5.cover_cases hc with h | h | h | h | h
  · have := h.2.1; simp only at this; omega
  · have := h.2.1; simp only at this; omega
  · have := h.2.2; simp only at this; omega
  · have := h.2.2; simp only at this; omega
  · have := h.2.1.1; simp only at this; omega

/-- `report-A2.md`, 5.3 (c): "In the rows [0, b-q) there are only T_1, T_2, T_5.
... And T_1 contains [0, q) x [0, b-q)." -/
private theorem oc_T1 (F : FrameO P p q a b t o x5 y5) (hq : q < p)
    (h1 : (o 1).swap = true) (h2 : (o 2).swap = false) (h3 : (o 3).swap = false)
    (ha : a = 2 * p) (hx5 : x5 = q) :
    ∀ X Y : ℤ, 0 ≤ X → X < q → 0 ≤ Y → Y < b - q → ((X, Y) : Cell) ∈ t 0 := by
  intro X Y hX0 hX1 hY0 hY1
  have hW1 : (o 1).W p q = q := by simp [Orient.W, h1]
  have hH2 : (o 2).H p q = q := by simp [Orient.H, h2]
  have hH3 : (o 3).H p q = q := by simp [Orient.H, h3]
  have hc : ((X, Y) : Cell) ∈ R a b := by rw [mem_R]; simp only; omega
  rcases F.toFrame5.cover_cases hc with h | h | h | h | h
  · exact h.1
  · have := h.2.1; simp only at this; omega
  · have := h.2.2; simp only at this; omega
  · have := h.2.2; simp only at this; omega
  · have := h.2.1.1; simp only at this; omega

/-- `report-A2.md`, 5.3 (c): "So D of T_1 is not in its bottom row (its mark is
not A): the mark of T_1 is E or B, its EB is row 0, and (8) kappa_c = q for
c < b-q." With the mark `A` the row 0 of `T_1` would be the side `AD`, with
`alpha < q` cells. -/
private theorem oc_T1_mark (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q)
    (h0 : (o 0).swap = true) (hb : q < b)
    (hT1 : ∀ X Y : ℤ, 0 ≤ X → X < q → 0 ≤ Y → Y < b - q → ((X, Y) : Cell) ∈ t 0) :
    (o 0).negX = false ∧ ∀ c : ℤ, 0 ≤ c → c < b - q → colCount P c = q := by
  have F' := F.toFrame5
  have m0 : (o 0).negX = false := by
    cases hx : (o 0).negX
    · rfl
    · exfalso
      have hy : (o 0).negY = false := by
        have hm := S.mark F' (i := 0) (by decide)
        revert hm; rw [hx]; cases (o 0).negY <;> simp
      have e0 : o 0 = ⟨true, true, false⟩ := Orient.ext h0 hx hy
      have hfull : colCount P (p - 1) = q := by
        rw [F'.colCount_eq_iff]
        intro z hz0 hz1
        refine (F'.mem_of 0 (c := (z, 0)) (d := (p - 1, z)) ?_).1
          (hT1 z 0 hz0 hz1 le_rfl (by omega))
        simp [loc, e0, Orient.back]
      have := S.alpha_lt
      omega
  refine ⟨m0, fun c hc0 hc1 => ?_⟩
  rw [F'.colCount_eq_iff]
  intro z hz0 hz1
  cases hy : (o 0).negY
  · have e0 : o 0 = ⟨true, false, false⟩ := Orient.ext h0 m0 hy
    refine (F'.mem_of 0 (c := (z, c)) (d := (c, z)) ?_).1 (hT1 z c hz0 hz1 hc0 hc1)
    simp [loc, e0, Orient.back]
  · have e0 : o 0 = ⟨true, false, true⟩ := Orient.ext h0 m0 hy
    refine (F'.mem_of 0 (c := (q - 1 - z, c)) (d := (c, z)) ?_).1
      (hT1 _ c (by omega) (by omega) hc0 hc1)
    simp [loc, e0, Orient.back]

/-- `report-A2.md`, 5.3 (c), from "Lemma 5.1: a = 2p" to "(8) kappa_c = q for
c < b - q", with `x* = x5`. Assembled from `oc_top` (dimensions, marks of `T_3`,
`T_4`), `oc_rows` ((7) and `g < q`), `oc_x5`, `oc_T1` and `oc_T1_mark` (the mark
of `T_1` and (8)). -/
theorem o53_c_setup (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = true) (h4y : (o 4).negY = false) (h0 : (o 0).swap = true)
    (h1 : (o 1).swap = true) (h2 : (o 2).swap = false) (h3 : (o 3).swap = false) :
    SetupC P p q a b o x5 := by
  obtain ⟨ha, m2, m3⟩ := oc_top F S hq h2 h3
  have hb1 : p < b := by
    have := F.h5_le
    simp [Orient.H, h4] at this
    omega
  obtain ⟨h7, hb2⟩ := oc_rows F S h4 h0 h1 h2 h3 m2 ha
  have hx5 := oc_x5 F S hq h4 h4y h0 h1 h2 h3 ha hb1
  obtain ⟨m0, h8⟩ := oc_T1_mark F S h0 (by omega) (oc_T1 F hq h1 h2 h3 ha hx5)
  exact ⟨ha, hx5, hb1, hb2, m2, m3, m0, h7, h8⟩

/-- `report-A2.md`, 5.3 (c1), "Mark of T_2 is A": `v_2 = p`, `v_3 = g < q`, so
the mark of `T_3` is `A` and by (8) `T_3` contains `[p, p + b - q) x [b - q, b)`;
`T_2` contains `[2p - q, 2p) x {p - 1}`; the cell `(2p - q, p - 1)` is in
both. -/
theorem o53_c1_A (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h0 : (o 0).swap = true) (h2 : (o 2).swap = false) (h3 : (o 3).swap = false)
    (e4 : o 4 = Orient.tE) (C : SetupC P p q a b o x5) (e1 : o 1 = Orient.tA) : False := by
  have _ := h0 -- not needed: `T_2` and `T_3` alone meet at `(2p - q, p - 1)`
  have _ := h3
  have _ := e4
  have F' := F.toFrame5
  have hq2 := F'.two_le_q
  have ha := C.ha
  have hb1 := C.hb1
  have hb2 := C.hb2
  -- the mark of `T_3` is `A`: `v_2 = p`, so `v_3 = g < q`
  have e2 : o 2 = Orient.wA := by
    have hr := F.side_right
    rw [e1] at hr
    simp [Orient.vrun_eq, Orient.tA, h2, S.fullEA] at hr
    have hx : (o 2).negX = true := by
      by_contra hne
      simp [hne, S.fullEB] at hr
      omega
    exact Orient.ext h2 hx C.m2
  -- `(2p - q, p - 1)` is in `T_3`: the cell `(p - q, g)` of `P`, by (8)
  have hc2 : ((2 * p - q, p - 1) : Cell) ∈ t 2 := by
    refine (F'.mem_of 2 (d := (p - q, b - p)) ?_).2
      ((F'.colCount_eq_iff (p - q)).1 (C.h8 _ (by omega) (by omega)) _ (by omega) (by omega))
    simp [loc, e2, Orient.wA, Orient.back, ha]
  -- `(2p - q, p - 1)` is in `T_2`: the corner `B` of `P`
  have hc1 : ((2 * p - q, p - 1) : Cell) ∈ t 1 := by
    refine (F'.mem_of 1 (d := (0, q - 1)) ?_).2 S.hB
    simp [loc, e1, Orient.tA, Orient.back, ha]
  exact absurd (F'.tile_unique hc1 hc2) (by decide)

/-- `report-A2.md`, 5.3 (c1), "Mark of T_2 is E or B", first part: row 0 of
`T_2` has `q` cells, so `2p = 3q`; the mark of `T_4` is not `A` (else `T_4`
contains `(q, p - 1)`, a cell of `T_5`), so it is `E`; `v_1 = b - q < p`, so
the mark of `T_1` is `B`. -/
theorem o53_c1_EB (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h0 : (o 0).swap = true) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = false) (e4 : o 4 = Orient.tE) (C : SetupC P p q a b o x5)
    (h1x : (o 1).negX = false) : 2 * p = 3 * q ∧ o 3 = Orient.wE ∧ o 0 = Orient.tB := by
  have F' := F.toFrame5
  have hy5 := F.y5_eq
  have hq2 := F'.two_le_q
  have ha := C.ha
  have hx5 := C.hx5
  have hb1 := C.hb1
  have hb2 := C.hb2
  have hW0 : (o 0).W p q = q := by simp [Orient.W, h0]
  have hH2 : (o 2).H p q = q := by simp [Orient.H, h2]
  have hH3 : (o 3).H p q = q := by simp [Orient.H, h3]
  have hW4 : (o 4).W p q = q := by simp [Orient.W, e4, Orient.tE]
  -- `T_5` contains `[q, 2q) x [0, b - q)`, by (8)
  have hT5 : ∀ X Y : ℤ, q ≤ X → X < 2 * q → 0 ≤ Y → Y < b - q →
      ((X, Y) : Cell) ∈ t 4 := by
    intro X Y hX1 hX2 hY1 hY2
    have hcol := (F'.colCount_eq_iff Y).1 (C.h8 _ hY1 hY2)
    refine (F'.mem_of 4 (d := (Y, X - q)) ?_).2 (hcol _ (by omega) (by omega))
    simp [loc, e4, Orient.tE, Orient.back, hx5, hy5]
  -- row 0 of `T_2` is `[2p - q, 2p)`: its side `EB` is there (`u_2 = q`)
  have hu2 : ∀ X : ℤ, ((X, 0) : Cell) ∈ t 1 → 2 * p - q ≤ X ∧ X < 2 * p := by
    intro X hX
    have hm := (F'.mem1 (X, 0)).1 hX
    simp only at hm
    rw [F'.hside (by decide), Orient.hrun_eq] at hm
    simp [h1, h1x, S.fullEB] at hm
    omega
  have hu2' : ∀ X : ℤ, 2 * p - q ≤ X → X < 2 * p → ((X, 0) : Cell) ∈ t 1 := by
    intro X hX1 hX2
    rw [F'.mem1]
    simp only
    rw [F'.hside (by decide), Orient.hrun_eq]
    simp [h1, h1x, S.fullEB]
    omega
  -- `2p = 3q`
  have h3q : 2 * p = 3 * q := by
    rcases lt_trichotomy (2 * p) (3 * q) with hlt | heq | hgt
    · -- the cell `(2p - q, 0)` is in `T_2` and in `T_5`
      exact absurd (F'.tile_unique (hu2' (2 * p - q) le_rfl (by omega))
        (hT5 (2 * p - q) 0 (by omega) (by omega) le_rfl (by omega))) (by decide)
    · exact heq
    · -- the cell `(2q, 0)` is in no tile
      have hc : ((2 * q, 0) : Cell) ∈ R a b := by rw [mem_R]; simp only; omega
      rcases F'.cover_cases hc with h | h | h | h | h
      · have := h.2.1; simp only at this; omega
      · have := hu2 _ h.1; omega
      · have := h.2.2; simp only at this; omega
      · have := h.2.2; simp only at this; omega
      · have := h.2.1.2; simp only at this; omega
  -- the mark of `T_4` is `E`: with `A`, the cell `(q, p - 1)` is in `T_4` and in `T_5`
  have e3 : o 3 = Orient.wE := by
    have hx : (o 3).negX = false := by
      cases hx' : (o 3).negX
      · rfl
      · exfalso
        have e3' : o 3 = ⟨false, true, false⟩ := Orient.ext h3 hx' C.m3
        have hc3 : ((q, p - 1) : Cell) ∈ t 3 := by
          refine (F'.mem_of 3 (d := (p - 1 - q, b - p)) ?_).2
            ((F'.colCount_eq_iff _).1 (C.h8 _ (by omega) (by omega)) _ (by omega) (by omega))
          simp [loc, e3', Orient.back]
        have hc4 : ((q, p - 1) : Cell) ∈ t 4 := by
          refine (F'.mem_of 4 (d := (p - 1, 0)) ?_).2 S.hA
          simp [loc, e4, Orient.tE, Orient.back, hx5, hy5]
        exact absurd (F'.tile_unique hc3 hc4) (by decide)
    exact Orient.ext h3 hx C.m3
  -- the mark of `T_1` is `B`: `v_1 = b - q < p`
  have hl := F.side_left
  rw [e3] at hl
  simp [Orient.vrun_eq, Orient.wE, S.fullEB] at hl
  have hy : (o 0).negY = true := by
    by_contra hne
    simp [h0, hne, S.fullEA] at hl
    omega
  exact ⟨h3q, e3, Orient.ext h0 C.m0 hy⟩

/-- `report-A2.md`, 5.3 (c1): "If the mark of T_2 is B, then v_2 = beta = b - q
and v_3 = q, so the mark of T_3 is E; then the reflection of R in its vertical
midline exchanges T_1, T_2 (tall, B) and T_3, T_4 (wide, E), and |S| is even by
(T4)." -/
theorem o53_c1_B (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q)
    (h2 : (o 2).swap = false) (m2 : (o 2).negY = false) (e0 : o 0 = Orient.tB)
    (e1 : o 1 = Orient.tB) (e3 : o 3 = Orient.wE) : False := by
  have hl := F.side_left
  have hr := F.side_right
  rw [e0, e3] at hl
  rw [e1] at hr
  simp [Orient.vrun_eq, Orient.tB, Orient.wE, h2, S.fullEB] at hl hr
  have hx : (o 2).negX = false := by
    cases hx' : (o 2).negX
    · rfl
    · exfalso
      have := S.alpha_lt
      rw [hx'] at hr
      simp at hr
      omega
  have e2 : o 2 = Orient.wE := Orient.ext h2 hx m2
  obtain ⟨-, hsym⟩ := F.toFrame5.T4_flipX (e0.trans e1.symm) (e2.trans e3.symm)
  refine S.no_reflection ?_
  cases h : (o 4).swap
  · exact Or.inl fun c => by simpa [h] using hsym c
  · exact Or.inr fun c => by simpa [h] using hsym c

/-- **`report-A2.md`, 5.3 (c1), the last count** ("Now count columns by (2)").
`T_1` tall with mark `B`, `T_2` tall with mark `E`, `T_4` wide with mark `E`,
`T_5` tall with `E` at its lower left corner, `2p = 3q`. Then `v_2 = p`,
`v_3 = g < q`, so the mark of `T_3` is `A`. The column sums at `x = q - 1`,
`x = p + q - 1` and `x = p` read `p + kappa_{q-1} = b`,
`rho_{p-q} + kappa_{q-1} = b` and `kappa_0 + rho_{p-q} = b`, so `b = p + q`. -/
theorem o53_c1_E (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (e0 : o 0 = Orient.tB) (e1 : o 1 = Orient.tE) (h2 : (o 2).swap = false)
    (e3 : o 3 = Orient.wE) (e4 : o 4 = Orient.tE) (ha : a = 2 * p) (hx5 : x5 = q)
    (h3q : 2 * p = 3 * q) (hb2 : b < p + q) : False := by
  have hq2 := F.toFrame5.two_le_q
  -- the mark of `T_3` is `A`
  have e2 : o 2 = Orient.wA := by
    have hm := S.mark F.toFrame5 (i := 2) (by decide)
    have hr := F.side_right
    rw [e1] at hr
    simp [Orient.vrun_eq, Orient.tE, h2, S.fullEA] at hr
    have hx : (o 2).negX = true := by
      by_contra hne
      simp [hne, S.fullEB] at hr
      omega
    have hy : (o 2).negY = false := by
      revert hm; rw [hx]; cases (o 2).negY <;> simp
    exact Orient.ext h2 hx hy
  -- three column sums (2)
  have c1 := F.toFrame5.col_sum (x := q - 1) (by omega) (by omega)
  have c2 := F.toFrame5.col_sum (x := p + q - 1) (by omega) (by omega)
  have c3 := F.toFrame5.col_sum (x := p) (by omega) (by omega)
  rw [e0, e1, e2, e3, e4] at c1 c2 c3
  simp only [Orient.tB, Orient.tE, Orient.wA, Orient.wE, Orient.colLine_wide,
    Orient.colLine_wide_neg, Orient.colLine_tall, Orient.colLine_tall_neg] at c1 c2 c3
  simp (disch := omega) only [F.toFrame5.rowCount_zero, F.toFrame5.colCount_zero, add_zero,
    zero_add] at c1 c2 c3
  have r0 : rowCount P (q - 1 - (q - 1)) = p := by
    rw [show q - 1 - (q - 1) = (0 : ℤ) by omega]; exact S.fullEA
  have r1 : rowCount P (a - 1 - (p + q - 1)) = rowCount P (p - x5) := by congr 1; omega
  have k1 : colCount P (p - 1 - (a - 1 - (p + q - 1))) = colCount P (q - 1) := by
    congr 1; omega
  have k0 : colCount P (p - 1 - (a - 1 - p)) = q := by
    rw [show p - 1 - (a - 1 - p) = (0 : ℤ) by omega]; exact S.fullEB
  omega

/-- `report-A2.md`, 5.3 (c1): `E` of `T_5` at its lower left corner. -/
theorem o53_c1 (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h0 : (o 0).swap = true) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = false) (e4 : o 4 = Orient.tE) (C : SetupC P p q a b o x5) : False := by
  cases h1x : (o 1).negX
  · obtain ⟨h3q, e3, e0⟩ := o53_c1_EB F S hq h0 h1 h2 h3 e4 C h1x
    cases h1y : (o 1).negY
    · exact o53_c1_E F S hq e0 (Orient.ext h1 h1x h1y) h2 e3 e4 C.ha C.hx5 h3q C.hb2
    · exact o53_c1_B F S h2 C.m2 e0 (Orient.ext h1 h1x h1y) e3
  · have h1y : (o 1).negY = false := by
      have hm := S.mark F.toFrame5 (i := 1) (by decide)
      revert hm; rw [h1x]; cases (o 1).negY <;> simp
    exact o53_c1_A F S hq h0 h2 h3 e4 C (Orient.ext h1 h1x h1y)

/-- **`report-A2.md`, 5.3 (c2).** `E` of `T_5` at its upper left corner
`(q, p - 1)`. By (8) `T_5` contains `[q, 2q) x [q - g, p)`. If `2p ≥ 3q`, the
cell `(2q - 1, 0)` (the corner `D` of `T_5`) is in no tile. So `2p < 3q`, and
the cell `(2p - q, p - 1)` is in `T_5`; it is the corner of `box(T_2)` opposite
to the mark, so for the marks `A`, `B` of `T_2` it is in `T_2`. For the mark
`E`: `v_2 = p`, `v_3 = g < q`, the mark of `T_3` is `A`, and `(p, p - 1)` is in
`T_3` and in `T_5`. -/
theorem o53_c2 (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h0 : (o 0).swap = true) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = false) (e4 : o 4 = ⟨true, true, false⟩) (ha : a = 2 * p)
    (hx5 : x5 = q) (hb1 : p < b) (hb2 : b < p + q)
    (h8 : ∀ c : ℤ, 0 ≤ c → c < b - q → colCount P c = q) : False := by
  have hy5 := F.y5_eq
  have hq2 := F.toFrame5.two_le_q
  -- `T_5` contains `[q, 2q) x [q - g, p)`
  have hT5 : ∀ X Y : ℤ, q ≤ X → X < 2 * q → q - (b - p) ≤ Y → Y < p →
      ((X, Y) : Cell) ∈ t 4 := by
    intro X Y hX1 hX2 hY1 hY2
    have hcol := (F.toFrame5.colCount_eq_iff (p - 1 - Y)).1 (h8 _ (by omega) (by omega))
    refine (F.toFrame5.mem_of 4 (d := (p - 1 - Y, X - q)) ?_).2 (hcol _ (by omega) (by omega))
    simp [loc, e4, Orient.back, hx5, hy5]
  -- `2p < 3q`: otherwise the cell `(2q - 1, 0)` is in no tile
  have h3q : 2 * p < 3 * q := by
    by_contra hge
    have hc : ((2 * q - 1, 0) : Cell) ∈ R a b := by
      rw [mem_R]; simp only; omega
    rcases F.toFrame5.cover_cases hc with h | h | h | h | h
    · have := h.2.1; simp [Orient.W, h0] at this; omega
    · have := h.2.1; simp [Orient.W, h1] at this; omega
    · have := h.2.2; simp [Orient.H, h2] at this; omega
    · have := h.2.2; simp [Orient.H, h3] at this; omega
    · refine S.hD ((F.toFrame5.mem_of 4 (d := (p - 1, q - 1)) ?_).1 h.1)
      simp [loc, e4, Orient.back, hx5, hy5]
      omega
  have hc45 : ((2 * p - q, p - 1) : Cell) ∈ t 4 :=
    hT5 _ _ (by omega) (by omega) (by omega) (by omega)
  by_cases hE : (o 1).negX = false ∧ (o 1).negY = false
  · -- mark `E` of `T_2`: the mark of `T_3` is `A`, and `(p, p - 1)` is in `T_3` and `T_5`
    obtain ⟨hx, hy⟩ := hE
    have hr := F.side_right
    have hm2 := S.mark F.toFrame5 (i := 2) (by decide)
    simp [Orient.vrun_eq, h1, hy, h2, S.fullEA] at hr
    have hx2 : (o 2).negX = true := by
      by_contra hne
      simp [hne, S.fullEB] at hr
      omega
    have hy2 : (o 2).negY = false := by
      revert hm2; rw [hx2]; cases (o 2).negY <;> simp
    have e2 : o 2 = ⟨false, true, false⟩ := Orient.ext h2 hx2 hy2
    have h0g : ((0, b - p) : Cell) ∈ P :=
      (F.toFrame5.colCount_eq_iff 0).1 S.fullEB _ (by omega) (by omega)
    have hc2 : ((p, p - 1) : Cell) ∈ t 2 := by
      refine (F.toFrame5.mem_of 2 (d := (0, b - p)) ?_).2 h0g
      simp [loc, e2, Orient.back, ha]
      omega
    have hc4 : ((p, p - 1) : Cell) ∈ t 4 := hT5 _ _ (by omega) (by omega) (by omega) (by omega)
    exact Finset.disjoint_left.1 (F.tiling.disjoint 2 4 (by decide)) hc2 hc4
  · -- mark `A` or `B` of `T_2`: `(2p - q, p - 1)` is in `T_2` and in `T_5`
    have hm := S.mark F.toFrame5 (i := 1) (by decide)
    have h21 : ((2 * p - q, p - 1) : Cell) ∈ t 1 := by
      rcases e : o 1 with ⟨s, x, y⟩
      rw [e] at h1 hE hm
      simp only at h1 hE hm
      subst h1
      cases x <;> cases y <;> simp at hE hm
      · refine (F.toFrame5.mem_of 1 (d := (p - 1, 0)) ?_).2 S.hA
        simp [loc, e, Orient.back, ha]
      · refine (F.toFrame5.mem_of 1 (d := (0, q - 1)) ?_).2 S.hB
        simp [loc, e, Orient.back, ha]
    exact Finset.disjoint_left.1 (F.tiling.disjoint 1 4 (by decide)) h21 hc45

/-- `report-A2.md`, 5.3 (c), with `x* = x5`. -/
theorem o53_c_norm (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = true) (h4y : (o 4).negY = false) (h0 : (o 0).swap = true)
    (h1 : (o 1).swap = true) (h2 : (o 2).swap = false) (h3 : (o 3).swap = false) : False := by
  have C := o53_c_setup F S hq h4 h4y h0 h1 h2 h3
  cases hx : (o 4).negX
  · exact o53_c1 F S hq h0 h1 h2 h3 (Orient.ext h4 hx h4y) C
  · exact o53_c2 F S hq h0 h1 h2 h3 (Orient.ext h4 hx h4y) C.ha C.hx5 C.hb1 C.hb2 C.h8

/-- **`report-A2.md`, 5.3 (c).** Two wide tiles on top, none at the bottom
("Reflect R so that x* = x_5"). -/
theorem o53_c (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = true) (h0 : (o 0).swap = true) (h1 : (o 1).swap = true)
    (h2 : (o 2).swap = false) (h3 : (o 3).swap = false) : False := by
  cases hy : (o 4).negY
  · exact o53_c_norm F S hq h4 hy h0 h1 h2 h3
  · obtain ⟨t', F'⟩ := F.flipX
    exact o53_c_norm F' S hq (by simpa using h4) (by simp [Orient.reflX, h4, hy])
      (by simpa using h1) (by simpa using h0) (by simpa using h3) (by simpa using h2)

/-- **`report-A2.md`, 5.3, "T_5 tall".** There are more wide tiles on top than at
the bottom (`o53_tall_count`), which leaves (a), (b), (c). -/
theorem o53_tall (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = true) : False := by
  have hc := o53_tall_count F S hq h4
  cases h0 : (o 0).swap <;> cases h1 : (o 1).swap <;> cases h2 : (o 2).swap <;>
    cases h3 : (o 3).swap <;> simp [Orient.W, h0, h1, h2, h3] at hc <;>
    first
    | omega
    | exact o53_a F S hq h0 h1 fun h => Bool.noConfusion (h2.symm.trans (h.trans h3))
    | exact o53_b F S hq h4 h0 h1 h2 h3
    | exact o53_b_mirror F S hq h4 h0 h1 h2 h3
    | exact o53_c F S hq h4 h0 h1 h2 h3

end PolyominoOddOrder
