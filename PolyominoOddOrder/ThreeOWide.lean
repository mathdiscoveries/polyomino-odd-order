module

public import PolyominoOddOrder.ThreeOTall

/-!
# Case (I), three occupied corners, pattern O, `T_5` wide (`ThreeOWide.lean`)

Blueprint unit C4 (third increment). `report-A2.md`, section 5.3, "T_5 wide":
`H_5 = q`, `W_5 = p`, the full vertical side of `T_5` is `EB`. Both bottom tiles
wide is against (4) (`o53_wide_both`); one wide at the bottom is case (d), none
is case (e). The file ends with the entry statement of section 5.3, `three_O`.

| report | Lean |
|---|---|
| "x* = x_5 + p - 1" | `(o 4).negX = true` (for a wide `T_5`) |
| `Sigma = [0, x_5 + p) x [0, q)` and the Claim of (d) | `SigmaD` |
| (9) of (d), (10) of (e) | inside `o53_d_large`; `o53_e_q_setup` |

Entry statement (binding): `three_O`. A proof unit may reshape the nodes marked
PROVISIONAL.

Source: `theoretician/report-A2.md` (goals lab, commit `076d663`), section 5.3.
-/

@[expose] public section

namespace PolyominoOddOrder

open Orient (cornerP)

variable {P : Finset Cell} {p q a b : ℤ} {t : Fin 5 → Finset Cell} {o : Fin 5 → Orient}
  {x5 y5 : ℤ}

/-- `report-A2.md`, 5.3, "T_5 wide": "If T_1 and T_2 are both wide, (4) gives
2p ≤ a - 1 ≤ 2p - 1." -/
theorem o53_wide_both (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = false) (h0 : (o 0).swap = false) (h1 : (o 1).swap = false) : False := by
  obtain ⟨hl, hr⟩ := o53_four F S
  have hl' := hl (by simp [Orient.H, h0, h4])
  have hr' := hr (by simp [Orient.H, h1, h4])
  simp only [Orient.W, h0, h1] at hl' hr'
  have ht := F.side_top
  have b2 := (F.toFrame5.hrun_bounds 2).2
  have b3 := (F.toFrame5.hrun_bounds 3).2
  have w2 : (o 2).W p q ≤ p := by
    cases h : (o 2).swap <;> simp [Orient.W, h]
    omega
  have w3 : (o 3).W p q ≤ p := by
    cases h : (o 3).swap <;> simp [Orient.W, h]
    omega
  simp at hl' hr'
  omega

/-! ## (d) One wide tile at the bottom -/

/-- The width of a wide box. -/
private theorem wd_W_f {c : Orient} (h : c.swap = false) : c.W p q = p := by
  simp [Orient.W, h]

/-- The height of a wide box. -/
private theorem wd_H_f {c : Orient} (h : c.swap = false) : c.H p q = q := by
  simp [Orient.H, h]

/-- The width of a tall box. -/
private theorem wd_W_t {c : Orient} (h : c.swap = true) : c.W p q = q := by
  simp [Orient.W, h]

/-- The height of a tall box. -/
private theorem wd_H_t {c : Orient} (h : c.swap = true) : c.H p q = p := by
  simp [Orient.H, h]

/-- `report-A2.md`, 5.3 (d), "T_4 wide, T_3 wide": Lemma 5.1 gives `b = 2q`,
`a = 2p`; `box(T_4) = [0, p) x [q, 2q)` meets no other tile (`T_1`, `T_5` in the
rows `< q`, `T_2` in the columns `≥ 2p - q > p`, `T_3` in the columns `≥ p`), so
`T_4` fills its box, against `Frame5.exists_hole`. -/
theorem o53_d_ww (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = false) (h0 : (o 0).swap = false) (h1 : (o 1).swap = true)
    (h2 : (o 2).swap = false) (h3 : (o 3).swap = false) : False := by
  obtain ⟨e0, e3⟩ := lemma51_left F.toFrame5 S hq F.x5_pos (h0.trans h3.symm)
  obtain ⟨e2, e3'⟩ := lemma51_top F.toFrame5 S hq F.y5_le (h2.trans h3.symm)
  have hl := F.side_left
  have ht := F.side_top
  rw [wd_H_f h0] at e0
  rw [wd_H_f h3] at e3
  rw [wd_W_f h2] at e2
  rw [wd_W_f h3] at e3'
  have hb : b = 2 * q := by omega
  have ha : a = 2 * p := by omega
  have hy5 := F.y5_eq
  -- a cell of `box(T_4)` that is not in `T_4` is in no tile
  obtain ⟨l, hlb, hlP⟩ := F.toFrame5.exists_hole (o 3)
  rw [wd_W_f h3, wd_H_f h3] at hlb
  have hc : ((l.1, b - 1 - l.2) : Cell) ∈ R a b := by
    rw [mem_R]; simp only; omega
  rcases F.toFrame5.cover_cases hc with h | h | h | h | h
  · rw [wd_H_f h0] at h; simp only at h; omega
  · rw [wd_W_t h1] at h; simp only at h; omega
  · rw [wd_W_f h2] at h; simp only at h; omega
  · apply hlP
    have := (F.toFrame5.mem3 _).1 h.1
    simpa using this
  · rw [wd_H_f h4] at h; simp only at h; omega

/-- `report-A2.md`, 5.3 (d), "T_4 wide, T_3 tall" and "T_4 tall, T_3 tall":
`T_2`, `T_3` tall give `b = 2p` on the right by Lemma 5.1, and on the left
`b = v_1 + v_4 ≤ q + p`. -/
theorem o53_d_T3tall (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h0 : (o 0).swap = false) (h1 : (o 1).swap = true) (h2 : (o 2).swap = true) : False := by
  have hl := F.side_left
  have b0 := (F.toFrame5.vrun_bounds 0).2
  have b3 := (F.toFrame5.vrun_bounds 3).2
  obtain ⟨e1, e2⟩ := lemma51_right F.toFrame5 S hq F.x5_le (h1.trans h2.symm)
  have hr := F.side_right
  have h3 : (o 3).H p q ≤ p := by
    cases h : (o 3).swap <;> simp [Orient.H, h]
    omega
  simp [Orient.H, h0, h1, h2] at b0 e1 e2
  omega

/-- The facts of `report-A2.md`, 5.3 (d), "T_4 tall, T_3 wide", before the
Claim: `x* = x5 + p - 1`, the mark of `T_2` is `A`, `a = x5 + p + alpha`,
`x5 < q`. -/
structure SetupD (P : Finset Cell) (p q a : ℤ) (o : Fin 5 → Orient) (x5 : ℤ) : Prop where
  /-- `x* = x5 + p - 1`: the full side `EB` of `T_5` is its right column. -/
  h4x : (o 4).negX = true
  /-- The mark of `T_2` is `A`. -/
  e1 : o 1 = Orient.tA
  /-- `a = x5 + p + u_2` with `u_2 = alpha`. -/
  ha : a = x5 + p + colCount P (p - 1)
  /-- `x5 ≤ a - 1 - p < q`. -/
  hx5 : x5 < q

/-- `report-A2.md`, 5.3 (d), "T_4 tall, T_3 wide", up to "D of T_2 is (a - q, 0),
E is (a - 1, p - 1)". `a = u_3 + u_4 ≤ p + q`; `x* = x5` would give
`p ≤ x5 ≤ a - 1 - p < q` by (4); so `x* = x5 + p - 1`, and as `(x*, 0)` is in
`T_5` and `(x* + 1, 0)` is not, the bottom row reads `u_1 + mu = x5 + p`
(`FrameO.bottom4`); then `u_2 = a - x5 - p < q`, which for a tall `T_2` leaves
only the mark `A`. -/
theorem o53_d_setup (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = false) (h0 : (o 0).swap = false) (h1 : (o 1).swap = true)
    (h2 : (o 2).swap = false) (h3 : (o 3).swap = true) : SetupD P p q a o x5 := by
  have hW4 : (o 4).W p q = p := wd_W_f h4
  have hH4 : (o 4).H p q = q := wd_H_f h4
  have hq2 := F.toFrame5.two_le_q
  have hx5le := F.x5_le
  have hx5pos := F.x5_pos
  have ht := F.side_top
  have b2 := (F.toFrame5.hrun_bounds 2).2
  have b3 := (F.toFrame5.hrun_bounds 3).2
  rw [wd_W_f h2] at b2
  rw [wd_W_t h3] at b3
  rw [hW4] at hx5le
  have hx5 : x5 < q := by omega
  -- `x* = x5` would give `p ≤ x5`
  have h4x : (o 4).negX = true := by
    have hl := (o53_four F S).1 (by rw [wd_H_f h0, hH4])
    rw [wd_W_f h0] at hl
    cases hx : (o 4).negX
    · simp [xStar, Orient.revH, h4, hx] at hl
      omega
    · rfl
  have hxs : xStar (o 4) p q x5 = x5 + p - 1 := by
    simp [xStar, Orient.revH, h4, h4x, hW4]
  -- the bottom interval of `T_5` ends at `x*`
  have hc := o53_xstar_col F S 0 le_rfl (by omega)
  rw [hxs, F.bottom4] at hc
  have hn : ¬ (((x5 + p, 0) : Cell) ∈ t 4) := fun h => by
    have := (F.toFrame5.box4 h).1.2
    rw [hW4] at this
    simp at this
  rw [F.bottom4] at hn
  have hs := F.side_bottom
  have hu2 : (o 1).rowLine p q P 0 = a - x5 - p := by omega
  -- `u_2 < q`: the mark of `T_2` is `A`
  have hx1 : (o 1).negX = true := by
    cases hx : (o 1).negX
    · have := hu2
      rw [Orient.hrun_eq] at this
      simp [h1, hx, S.fullEB] at this
      omega
    · rfl
  have hy1 : (o 1).negY = false := by
    have hm := S.mark F.toFrame5 (i := 1) (by decide)
    revert hm; rw [hx1]; cases (o 1).negY <;> simp
  have e1 : o 1 = Orient.tA := Orient.ext h1 hx1 hy1
  refine ⟨h4x, e1, ?_, hx5⟩
  rw [e1] at hu2
  simp only [Orient.tA, Orient.rowLine_tall_neg, sub_zero] at hu2
  omega

/-- The Claim of `report-A2.md`, 5.3 (d): `T_1` and `T_5` together are
`Sigma = [0, x5 + p) x [0, q)`, `beta = x5`, `v_1 = q`. Here `beta` is the
number of cells of `P` on the side `BD`, whether or not `B` is a mark. -/
structure SigmaD (P : Finset Cell) (p q : ℤ) (t : Fin 5 → Finset Cell)
    (o : Fin 5 → Orient) (x5 : ℤ) : Prop where
  /-- Every cell of `Sigma` is in `T_1` or in `T_5`. -/
  cover : ∀ X Y : ℤ, 0 ≤ X → X < x5 + p → 0 ≤ Y → Y < q →
    ((X, Y) : Cell) ∈ t 0 ∨ ((X, Y) : Cell) ∈ t 4
  /-- `beta = x5`. -/
  hbeta : rowCount P (q - 1) = x5
  /-- `v_1 = q`. -/
  hv1 : (o 0).colLine p q P 0 = q

/-- The Claim of 5.3 (d), first case, `E` of `T_5` at `(x*, 0)`: "the bottom row
of box(T_5) is EA, so u_1 = x_5 < p ..., so the mark of T_1 is B, beta = x_5,
v_1 = q"; the row `q - 1` of `Sigma` is `[0, p)` of `T_1` and `[p, p + x5)` of
`T_5`. -/
private theorem wd_sigma_low (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q)
    (hq : q < p) (h4 : (o 4).swap = false) (h0 : (o 0).swap = false)
    (h4x : (o 4).negX = true) (h4y : (o 4).negY = false) (hx5 : x5 < q)
    (hum : (o 0).rowLine p q P 0 + (o 4).rowLine p q P 0 = x5 + p) :
    (∀ X : ℤ, 0 ≤ X → X < x5 + p → ((X, q - 1) : Cell) ∈ t 0 ∨ ((X, q - 1) : Cell) ∈ t 4) ∧
      rowCount P (q - 1) = x5 ∧ (o 0).colLine p q P 0 = q := by
  have hy5 := F.y5_eq
  have e4 : o 4 = ⟨false, true, false⟩ := Orient.ext h4 h4x h4y
  have hmu : (o 4).rowLine p q P 0 = p := by
    rw [e4]; simpa [Orient.rowLine] using S.fullEA
  have hu1 : (o 0).rowLine p q P 0 = x5 := by omega
  have hy0 : (o 0).negY = true := by
    cases hy : (o 0).negY
    · have := hu1
      simp [Orient.rowLine, h0, hy, S.fullEA] at this
      omega
    · rfl
  have hx0 : (o 0).negX = false := by
    have hm := S.mark F.toFrame5 (i := 0) (by decide)
    revert hm; rw [hy0]; cases (o 0).negX <;> simp
  have e0 : o 0 = Orient.wB := Orient.ext h0 hx0 hy0
  have hbeta : rowCount P (q - 1) = x5 := by
    rw [e0] at hu1; simpa [Orient.wB, Orient.rowLine] using hu1
  have hv1 : (o 0).colLine p q P 0 = q := by
    rw [e0]; simpa [Orient.wB, Orient.colLine] using S.fullEB
  refine ⟨?_, hbeta, hv1⟩
  -- the run of `B`: `(x, q - 1) ∈ P ↔ 0 ≤ x < x5`
  have hB : ∀ x : ℤ, ((x, q - 1) : Cell) ∈ P ↔ 0 ≤ x ∧ x < x5 := by
    intro x
    have := F.toFrame5.hside (i := 0) (by decide) x
    rw [hu1, e0] at this
    simpa [Orient.wB, Orient.back] using this
  intro X h0' h1'
  by_cases hX : X < p
  · left
    refine (F.toFrame5.mem_of 0 (d := (X, 0)) ?_).2
      ((F.toFrame5.rowCount_eq_iff 0).1 S.fullEA X h0' hX)
    simp [loc, e0, Orient.wB, Orient.back]
  · right
    refine (F.toFrame5.mem_of 4 (d := (p - 1 - (X - x5), q - 1)) ?_).2
      ((hB _).2 ⟨by omega, by omega⟩)
    simp [loc, e4, Orient.back, hy5]

/-- The Claim of 5.3 (d), second case, `E` of `T_5` at `(x*, q - 1)`: the marks
`A`, `B` of `T_1` put `(p - 1, q - 1)` in `T_1`, a cell of the top row of
`box(T_5)`; so the mark of `T_1` is `E`, `mu = beta = x5`, and the bottom row of
`T_5` gives the cells `[0, x5) x {q - 1}` of `P`; the row `q - 1` of `Sigma` is
`[0, x5)` of `T_1` and `[x5, x5 + p)` of `T_5`. -/
private theorem wd_sigma_high (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q)
    (hq : q < p) (h4 : (o 4).swap = false) (h0 : (o 0).swap = false)
    (h4x : (o 4).negX = true) (h4y : (o 4).negY = true) (hx5 : x5 < q)
    (hum : (o 0).rowLine p q P 0 + (o 4).rowLine p q P 0 = x5 + p) :
    (∀ X : ℤ, 0 ≤ X → X < x5 + p → ((X, q - 1) : Cell) ∈ t 0 ∨ ((X, q - 1) : Cell) ∈ t 4) ∧
      rowCount P (q - 1) = x5 ∧ (o 0).colLine p q P 0 = q := by
  have hy5 := F.y5_eq
  have hx5pos := F.x5_pos
  have e4 : o 4 = ⟨false, true, true⟩ := Orient.ext h4 h4x h4y
  -- the top row of `box(T_5)` is in `T_5`
  have hT5 : ∀ X : ℤ, x5 ≤ X → X < x5 + p → ((X, q - 1) : Cell) ∈ t 4 := by
    intro X h0' h1'
    refine (F.toFrame5.mem_of 4 (d := (p - 1 - (X - x5), 0)) ?_).2
      ((F.toFrame5.rowCount_eq_iff 0).1 S.fullEA _ (by omega) (by omega))
    simp [loc, e4, Orient.back, hy5]
  -- the mark of `T_1` is `E`
  have hD : ((p - 1, q - 1) : Cell) ∉ t 0 := fun h =>
    Finset.disjoint_left.1 (F.tiling.disjoint 0 4 (by decide)) h (hT5 _ (by omega) (by omega))
  have hx0 : (o 0).negX = false := by
    cases hx : (o 0).negX
    · rfl
    · exfalso
      have hy0 : (o 0).negY = false := by
        have hm := S.mark F.toFrame5 (i := 0) (by decide)
        revert hm; rw [hx]; cases (o 0).negY <;> simp
      apply hD
      refine (F.toFrame5.mem_of 0 (d := (0, q - 1)) ?_).2 S.hB
      simp [loc, Orient.back, h0, hx, hy0]
  have hy0 : (o 0).negY = false := by
    cases hy : (o 0).negY
    · rfl
    · exfalso
      apply hD
      refine (F.toFrame5.mem_of 0 (d := (p - 1, 0)) ?_).2 S.hA
      simp [loc, Orient.back, h0, hx0, hy]
  have e0 : o 0 = Orient.wE := Orient.ext h0 hx0 hy0
  have hu1 : (o 0).rowLine p q P 0 = p := by
    rw [e0]; simpa [Orient.wE, Orient.rowLine] using S.fullEA
  have hmu : (o 4).rowLine p q P 0 = rowCount P (q - 1) := by
    rw [e4]; simp [Orient.rowLine]
  have hbeta : rowCount P (q - 1) = x5 := by omega
  have hv1 : (o 0).colLine p q P 0 = q := by
    rw [e0]; simpa [Orient.wE, Orient.colLine] using S.fullEB
  refine ⟨?_, hbeta, hv1⟩
  -- `(j, q - 1) ∈ P` for `j < x5`, read off the bottom row of `T_5`
  have hB : ∀ j : ℤ, 0 ≤ j → j < x5 → ((j, q - 1) : Cell) ∈ P := by
    intro j hj0 hj1
    have h := (F.bottom4 (p - 1 - j + x5)).2 (by omega)
    refine (F.toFrame5.mem_of 4 (d := (j, q - 1)) ?_).1 h
    simp [loc, e4, Orient.back, hy5]
  intro X h0' h1'
  by_cases hX : X < x5
  · left
    refine (F.toFrame5.mem_of 0 (d := (X, q - 1)) ?_).2 (hB X h0' hX)
    simp [loc, e0, Orient.wE, Orient.back]
  · right
    exact hT5 X (by omega) h1'

/-- The closing step of the Claim of 5.3 (d): a tile other than `T_1`, `T_5`
with a cell outside `Sigma` has no cell in `Sigma`, since "to enter Sigma they
would have to enter row q-1 or column x* of Sigma"
(`EdgeConnected.exists_adj_leaving`). -/
private theorem wd_sigma_out (F : Frame5 P p q a b t o x5 y5) {i : Fin 5} (hi0 : i ≠ 0)
    (hi4 : i ≠ 4)
    (hrow : ∀ X : ℤ, 0 ≤ X → X < x5 + p → ((X, q - 1) : Cell) ∈ t 0 ∨ ((X, q - 1) : Cell) ∈ t 4)
    (hcol : ∀ Y : ℤ, 0 ≤ Y → Y < q → ((x5 + p - 1, Y) : Cell) ∈ t 4)
    {d : Cell} (hd : d ∈ t i) (hdo : ¬ (0 ≤ d.1 ∧ d.1 < x5 + p ∧ 0 ≤ d.2 ∧ d.2 < q))
    {c : Cell} (hc : c ∈ t i) : ¬ (0 ≤ c.1 ∧ c.1 < x5 + p ∧ 0 ≤ c.2 ∧ c.2 < q) := by
  intro hcS
  obtain ⟨⟨ux, uy⟩, ⟨vx, vy⟩, hu, hv, hadj, hA, hB⟩ :=
    (F.conn i).exists_adj_leaving
      (fun c : Cell => 0 ≤ c.1 ∧ c.1 < x5 + p ∧ 0 ≤ c.2 ∧ c.2 < q) hc hd hcS hdo
  simp only [adj_iff] at hadj
  simp only at hA hB
  have hvR := mem_R.1 (F.sub_R i hv)
  simp only at hvR
  have hne : ∀ j : Fin 5, j ≠ i → ((ux, uy) : Cell) ∉ t j := fun j hj hj' =>
    hj (F.tile_unique hj' hu)
  by_cases hx : ux = x5 + p - 1
  · exact hne 4 (Ne.symm hi4) (by rw [hx]; exact hcol uy hA.2.2.1 hA.2.2.2)
  · have hy : uy = q - 1 := by omega
    rcases hrow ux hA.1 hA.2.1 with h | h
    · exact hne 0 (Ne.symm hi0) (by rw [hy]; exact h)
    · exact hne 4 (Ne.symm hi4) (by rw [hy]; exact h)

/-- **`report-A2.md`, 5.3 (d), the Claim.** Two cases by the place of `E` in
`T_5` (`(x*, 0)`: `(o 4).negY = false`; `(x*, q - 1)`: `(o 4).negY = true`). In
both, row `q - 1` of `Sigma` is in `T_1` and `T_5` (`wd_sigma_low`,
`wd_sigma_high`), the right column `x*` of `Sigma` is in `T_5`, and `T_2`,
`T_3`, `T_4` cannot enter `Sigma` (`wd_sigma_out`). Reshaped from the skeleton:
the hypotheses on `T_2` and `T_3`, not used, are dropped. -/
theorem o53_d_sigma (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = false) (h0 : (o 0).swap = false) (h3 : (o 3).swap = true)
    (D : SetupD P p q a o x5) : SigmaD P p q t o x5 := by
  have hW4 : (o 4).W p q = p := wd_W_f h4
  have hH4 : (o 4).H p q = q := wd_H_f h4
  have hx5le := F.x5_le
  rw [hW4] at hx5le
  have hx5 := D.hx5
  have hb3 := F.toFrame5.H_le (i := 3) (by decide)
  rw [wd_H_t h3] at hb3
  -- the column `x*` of `Sigma` is in `T_5`
  have hcol : ∀ Y : ℤ, 0 ≤ Y → Y < q → ((x5 + p - 1, Y) : Cell) ∈ t 4 := by
    intro Y h0' h1'
    have := o53_xstar_col F S Y h0' (by rw [hH4]; exact h1')
    simpa [xStar, Orient.revH, h4, D.h4x, hW4] using this
  -- `u_1 + mu = x5 + p`
  have hs := F.side_bottom
  have hu2 : (o 1).rowLine p q P 0 = colCount P (p - 1) := by
    rw [D.e1]; simp [Orient.tA, Orient.rowLine]
  have hum : (o 0).rowLine p q P 0 + (o 4).rowLine p q P 0 = x5 + p := by
    have := D.ha; omega
  obtain ⟨hrow, hbeta, hv1⟩ :
      (∀ X : ℤ, 0 ≤ X → X < x5 + p →
        ((X, q - 1) : Cell) ∈ t 0 ∨ ((X, q - 1) : Cell) ∈ t 4) ∧
      rowCount P (q - 1) = x5 ∧ (o 0).colLine p q P 0 = q := by
    cases hy4 : (o 4).negY
    · exact wd_sigma_low F S hq h4 h0 D.h4x hy4 hx5 hum
    · exact wd_sigma_high F S hq h4 h0 D.h4x hy4 hx5 hum
  refine ⟨?_, hbeta, hv1⟩
  intro X Y hX0 hX1 hY0 hY1
  have hc : ((X, Y) : Cell) ∈ R a b := by
    rw [mem_R]; simp only; omega
  have hS : 0 ≤ ((X, Y) : Cell).1 ∧ ((X, Y) : Cell).1 < x5 + p ∧ 0 ≤ ((X, Y) : Cell).2 ∧
      ((X, Y) : Cell).2 < q := ⟨hX0, hX1, hY0, hY1⟩
  -- the corners of `T_2`, `T_3`, `T_4` lie outside `Sigma` (`b ≥ p + 1 > q`)
  rcases F.toFrame5.cover_cases hc with h | h | h | h | h
  · exact Or.inl h.1
  · exact absurd hS (wd_sigma_out F.toFrame5 (i := 1) (by decide) (by decide) hrow hcol
      F.toFrame5.corner1 (by simp only; omega) h.1)
  · exact absurd hS (wd_sigma_out F.toFrame5 (i := 2) (by decide) (by decide) hrow hcol
      F.toFrame5.corner2 (by simp only; omega) h.1)
  · exact absurd hS (wd_sigma_out F.toFrame5 (i := 3) (by decide) (by decide) hrow hcol
      F.toFrame5.corner3 (by simp only; omega) h.1)
  · exact Or.inr h.1

/-- `report-A2.md`, 5.3 (d), "v_4 < p": the mark of `T_4` is `B`, `b = q + beta`,
the mark of `T_3` is `A`, `alpha + beta = q`, `p = 2 beta`; `(q - 1, q - 1)` is
in `T_4` and in `Sigma`. The proof needs only the first and the last of these
steps: with the mark `B` the column `q - 1` of `box(T_4)` is its side `EA`, all
in `T_4`, and it holds `(q - 1, q - 1)` because `b - q = v_4 < p`. -/
theorem o53_d_small (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = false) (h0 : (o 0).swap = false) (h1 : (o 1).swap = true)
    (h2 : (o 2).swap = false) (h3 : (o 3).swap = true) (D : SetupD P p q a o x5)
    (G : SigmaD P p q t o x5) (hv : (o 3).colLine p q P 0 < p) : False := by
  -- not needed: the codes of `T_1`, `T_2`, `T_3`, `T_5` enter through `D` and `G`
  have _ := h4
  have _ := h0
  have _ := h1
  have _ := h2
  have hl := F.side_left
  rw [G.hv1] at hl
  have b3 := (F.toFrame5.vrun_bounds 3).1
  have hx5 := D.hx5
  have hx5pos := F.x5_pos
  -- `v_4 < p`: the mark of `T_4` is `B`
  have hy3 : (o 3).negY = true := by
    cases hy : (o 3).negY
    · exfalso
      have := hv
      simp [Orient.colLine, h3, hy, S.fullEA] at this
    · rfl
  have hx3 : (o 3).negX = false := by
    have hm := S.mark F.toFrame5 (i := 3) (by decide)
    revert hm; rw [hy3]; cases (o 3).negX <;> simp
  have e3 : o 3 = Orient.tB := Orient.ext h3 hx3 hy3
  -- `(q - 1, q - 1)` is in `T_4` (its side `EA` is the column `q - 1`) and in `Sigma`
  have hc3 : ((q - 1, q - 1) : Cell) ∈ t 3 := by
    refine (F.toFrame5.mem_of 3 (d := (b - q, 0)) ?_).2
      ((F.toFrame5.rowCount_eq_iff 0).1 S.fullEA _ (by omega) (by omega))
    simp [loc, e3, Orient.tB, Orient.back]
  rcases G.cover (q - 1) (q - 1) (by omega) (by omega) (by omega) (by omega) with h | h
  · exact absurd (F.toFrame5.tile_unique hc3 h) (by decide)
  · exact absurd (F.toFrame5.tile_unique hc3 h) (by decide)

/-- `report-A2.md`, 5.3 (d), "v_4 = p": `b = p + q`, `v_3 = q`, `T_4` fills
`[0, q) x [q, b)` up to its shape, (9) `kappa_{p-1-c} = alpha` for `c < q`; the
mark of `T_4` is `E` or `A`, and row `q` (mark `E`) or row `b - 1` (mark `A`) of
`R a b` has too many cells left for `T_2` or `T_3`. The proof needs only `b = p + q`
and the two final counts: for the mark `E` the row sum (2) at the row `q`, for
the mark `A` the side equation `u_3 + u_4 = a` with `u_4 = alpha`; (9) is not
used. -/
theorem o53_d_large (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = false) (h0 : (o 0).swap = false) (h1 : (o 1).swap = true)
    (h2 : (o 2).swap = false) (h3 : (o 3).swap = true) (D : SetupD P p q a o x5)
    (G : SigmaD P p q t o x5) (hv : (o 3).colLine p q P 0 = p) : False := by
  have _ := h1 -- not needed: the code of `T_2` is `D.e1`
  have hl := F.side_left
  rw [G.hv1, hv] at hl
  have hx5pos := F.x5_pos
  have ha := D.ha
  -- `v_4 = p`: the mark of `T_4` is `E` or `A`
  have hy3 : (o 3).negY = false := by
    cases hy : (o 3).negY
    · rfl
    · exfalso
      have := hv
      simp [Orient.colLine, h3, hy] at this
      have := S.beta_lt
      omega
  cases hx3 : (o 3).negX
  · -- mark `E`: the row `q` of `R a b` has `alpha` cells of `T_4` and
    -- `kappa_{p-1-q}` cells of `T_2`, no others
    have e3 : o 3 = Orient.tE := Orient.ext h3 hx3 hy3
    have hq2 := F.toFrame5.two_le_q
    have hr := F.toFrame5.row_sum (y := q) (by omega) (by omega)
    rw [F.toFrame5.rowLine_zero (o 0) (y := q) (Or.inr (by rw [wd_H_f h0])),
      F.toFrame5.rowLine_zero (o 2) (y := b - 1 - q) (Or.inr (by rw [wd_H_f h2]; omega)),
      F.toFrame5.rowLine_zero (o 4) (y := q - y5) (Or.inr (by rw [wd_H_f h4, F.y5_eq]; omega)),
      D.e1, e3] at hr
    simp only [Orient.tA, Orient.tE, Orient.rowLine_tall, Orient.rowLine_tall_neg] at hr
    have k : colCount P (b - 1 - q) = colCount P (p - 1) := by congr 1; omega
    have := F.toFrame5.colCount_le (p - 1 - q)
    omega
  · -- mark `A`: `u_4 = alpha`, so `u_3 = x5 + p > p`
    have e3 : o 3 = Orient.tA := Orient.ext h3 hx3 hy3
    have ht := F.side_top
    have b2 := (F.toFrame5.hrun_bounds 2).2
    rw [wd_W_f h2] at b2
    rw [e3] at ht
    simp only [Orient.tA, Orient.rowLine_tall_neg, sub_zero] at ht
    omega

/-- `report-A2.md`, 5.3 (d), "T_4 tall, T_3 wide". -/
theorem o53_d_main (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = false) (h0 : (o 0).swap = false) (h1 : (o 1).swap = true)
    (h2 : (o 2).swap = false) (h3 : (o 3).swap = true) : False := by
  have D := o53_d_setup F S hq h4 h0 h1 h2 h3
  have G := o53_d_sigma F S hq h4 h0 h3 D
  have hv := (F.toFrame5.vrun_bounds 3).2
  simp only [Orient.H, h3, ite_true] at hv
  rcases lt_or_eq_of_le hv with h | h
  · exact o53_d_small F S hq h4 h0 h1 h2 h3 D G h
  · exact o53_d_large F S hq h4 h0 h1 h2 h3 D G h

/-- **`report-A2.md`, 5.3 (d).** One wide tile at the bottom, `T_1` the wide
one. -/
theorem o53_d (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = false) (h0 : (o 0).swap = false) (h1 : (o 1).swap = true) : False := by
  cases h2 : (o 2).swap
  · cases h3 : (o 3).swap
    · exact o53_d_ww F S hq h4 h0 h1 h2 h3
    · exact o53_d_main F S hq h4 h0 h1 h2 h3
  · exact o53_d_T3tall F S hq h0 h1 h2

/-! ## (e) No wide tile at the bottom -/

/-- `report-A2.md`, 5.3 (e), "T_3, T_4 tall": Lemma 5.1 gives `a = 2q`, `b = 2p`;
the rows `[p, 2p)` lie in `T_3` and `T_4` alone (`H_5 = q < p`), whose boxes are
disjoint; so `T_3` fills its box. -/
theorem o53_e_tt (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = false) (h0 : (o 0).swap = true) (h1 : (o 1).swap = true)
    (h2 : (o 2).swap = true) (h3 : (o 3).swap = true) : False := by
  have F' := F.toFrame5
  have hy5 := F.y5_eq
  obtain ⟨u2, u3⟩ := lemma51_top F' S hq F.y5_le (h2.trans h3.symm)
  obtain ⟨v0, v3⟩ := lemma51_left F' S hq F.x5_pos (h0.trans h3.symm)
  have ht := F.side_top
  have hl := F.side_left
  simp only [Orient.W, Orient.H, h0, h2, h3, ite_true] at u2 u3 v0 v3
  -- a hole of `T_3` in its box `[q, 2q) x [p, 2p)` lies in no tile
  obtain ⟨⟨lx, ly⟩, hlb, hlP⟩ := F'.exists_hole (o 2)
  simp only [Orient.W, Orient.H, h2, ite_true] at hlb
  have hc : ((a - 1 - lx, b - 1 - ly) : Cell) ∈ R a b := by
    rw [mem_R]; simp only; omega
  rcases F'.cover_cases hc with h | h | h | h | h
  · have := h.2.2; simp [Orient.H, h0] at this; omega
  · have := h.2.2; simp [Orient.H, h1] at this; omega
  · exact hlP (by simpa using (F'.mem2 _).1 h.1)
  · have := h.2.1; simp [Orient.W, h3] at this; omega
  · have := h.2.2.2; simp [Orient.H, h4, hy5] at this; omega

/-- The facts of `report-A2.md`, 5.3 (e), "T_3, T_4 wide", with `x* = x5`:
`a = 2p`, `p < b ≤ 2q`, the marks of `T_3`, `T_4` are `E` or `A`, `x5 ≤ q`,
`x5 + p ≥ 2p - q`, `u_1 = x5`. -/
structure SetupE (P : Finset Cell) (p q a b : ℤ) (o : Fin 5 → Orient) (x5 : ℤ) : Prop where
  /-- Lemma 5.1 on top. -/
  ha : a = 2 * p
  /-- `H_1 = p ≤ b - 1`. -/
  hb1 : p < b
  /-- `b ≤ 2q`. -/
  hb2 : b ≤ 2 * q
  /-- The mark of `T_3` is `E` or `A`. -/
  m2 : (o 2).negY = false
  /-- The mark of `T_4` is `E` or `A`. -/
  m3 : (o 3).negY = false
  /-- `x5 ≤ q`. -/
  hx5a : x5 ≤ q
  /-- `x5 + p ≥ 2p - q`. -/
  hx5b : p - q ≤ x5
  /-- `u_1 = x5`. -/
  hu1 : (o 0).rowLine p q P 0 = x5

/-- `report-A2.md`, 5.3 (e), "T_3, T_4 wide", up to "so u_1 = x_5; u_1 is q or
alpha", after the reflection that makes `x* = x5`. -/
theorem o53_e_setup (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = false) (h4x : (o 4).negX = false) (h0 : (o 0).swap = true)
    (h1 : (o 1).swap = true) (h2 : (o 2).swap = false) (h3 : (o 3).swap = false) :
    SetupE P p q a b o x5 := by
  have F' := F.toFrame5
  have hy5 := F.y5_eq
  have hq2 := F'.two_le_q
  -- Lemma 5.1 on top: `a = 2p`, and the marks of `T_3`, `T_4` are `E` or `A`
  obtain ⟨u2, u3⟩ := lemma51_top F' S hq F.y5_le (h2.trans h3.symm)
  have ht := F.side_top
  have hW2 : (o 2).W p q = p := by simp [Orient.W, h2]
  have hW3 : (o 3).W p q = p := by simp [Orient.W, h3]
  have ha : a = 2 * p := by omega
  have hbeta := S.beta_lt
  have m2 : (o 2).negY = false := by
    cases hy : (o 2).negY
    · rfl
    · rw [Orient.hrun_eq, hW2] at u2
      simp [h2, hy] at u2
      omega
  have m3 : (o 3).negY = false := by
    cases hy : (o 3).negY
    · rfl
    · rw [Orient.hrun_eq, hW3] at u3
      simp [h3, hy] at u3
      omega
  -- `H_1 = p ≤ b - 1`
  have hH0 := F'.H_le (i := 0) (by decide)
  simp only [Orient.H, h0, ite_true] at hH0
  -- `b ≤ 2q`: otherwise row `q` lies in `T_1` and `T_2` alone
  have hb2 : b ≤ 2 * q := by
    by_contra hgt
    have hs := F'.row_sum (y := q) (by omega) (by omega)
    have z2 : (o 2).rowLine p q P (b - 1 - q) = 0 :=
      F'.rowLine_zero _ (Or.inr (by simp [Orient.H, h2]; omega))
    have z3 : (o 3).rowLine p q P (b - 1 - q) = 0 :=
      F'.rowLine_zero _ (Or.inr (by simp [Orient.H, h3]; omega))
    have z4 : (o 4).rowLine p q P (q - y5) = 0 :=
      F'.rowLine_zero _ (Or.inr (by simp [Orient.H, h4, hy5]))
    have l0 := F'.rowLine_le (o 0) q
    have l1 := F'.rowLine_le (o 1) q
    simp only [Orient.W, h0, h1, ite_true] at l0 l1
    omega
  -- `x5 ≤ q`: column `q` meets `T_5`
  have hx5a : x5 ≤ q := by
    by_contra hgt
    have hs := F'.col_sum (x := q) (by omega) (by omega)
    have z0 : (o 0).colLine p q P q = 0 :=
      F'.colLine_zero _ (Or.inr (by simp [Orient.W, h0]))
    have z1 : (o 1).colLine p q P (a - 1 - q) = 0 :=
      F'.colLine_zero _ (Or.inr (by simp [Orient.W, h1]; omega))
    have z2 : (o 2).colLine p q P (a - 1 - q) = 0 :=
      F'.colLine_zero _ (Or.inr (by simp [Orient.W, h2]; omega))
    have z4 : (o 4).colLine p q P (q - x5) = 0 := F'.colLine_zero _ (Or.inl (by omega))
    have l3 := F'.colLine_le (o 3) q
    rw [show (o 3).H p q = q by simp [Orient.H, h3]] at l3
    omega
  -- `x5 + p ≥ 2p - q`: column `2p - q - 1` meets `T_5`
  have hx5b : p - q ≤ x5 := by
    by_contra hlt
    have hs := F'.col_sum (x := 2 * p - q - 1) (by omega) (by omega)
    have z0 : (o 0).colLine p q P (2 * p - q - 1) = 0 :=
      F'.colLine_zero _ (Or.inr (by simp [Orient.W, h0]; omega))
    have z1 : (o 1).colLine p q P (a - 1 - (2 * p - q - 1)) = 0 :=
      F'.colLine_zero _ (Or.inr (by simp [Orient.W, h1]; omega))
    have z3 : (o 3).colLine p q P (2 * p - q - 1) = 0 :=
      F'.colLine_zero _ (Or.inr (by simp [Orient.W, h3]; omega))
    have z4 : (o 4).colLine p q P (2 * p - q - 1 - x5) = 0 :=
      F'.colLine_zero _ (Or.inr (by simp [Orient.W, h4]; omega))
    have l2 := F'.colLine_le (o 2) (a - 1 - (2 * p - q - 1))
    rw [show (o 2).H p q = q by simp [Orient.H, h2]] at l2
    omega
  -- `u_1 = x5`: `(x5, 0)` is in `T_5` (the side `EB`), `(x5 - 1, 0)` is not
  have hu1 : (o 0).rowLine p q P 0 = x5 := by
    have hcol := (F'.colCount_eq_iff 0).1 S.fullEB
    have hin : ((x5, 0) : Cell) ∈ t 4 := by
      cases hy : (o 4).negY
      · refine (F'.mem_of 4 (d := (0, 0)) ?_).2 (hcol 0 le_rfl (by omega))
        simp [loc, Orient.back, h4, h4x, hy, hy5]
      · refine (F'.mem_of 4 (d := (0, q - 1)) ?_).2 (hcol (q - 1) (by omega) (by omega))
        simp [loc, Orient.back, h4, h4x, hy, hy5]
    have hout : ((x5 - 1, 0) : Cell) ∉ t 4 := fun h => by
      have := (F'.box4 h).1.1
      dsimp only at this
      omega
    obtain ⟨e1, e2⟩ := (F.bottom4 x5).1 hin
    by_contra hne
    exact hout ((F.bottom4 (x5 - 1)).2 ⟨by omega, by omega⟩)
  exact ⟨ha, by omega, hb2, m2, m3, hx5a, hx5b, hu1⟩

/-- `report-A2.md`, 5.3 (e), "u_1 = alpha": the mark of `T_1` is `A`, the mark of
`T_4` is `A`, `alpha = b - p = x5`; the columns `p - 1` and `x5` of `R a b`
give `rho_{b-p} = 0` by (2), against `rho_j ≥ 1` (`Frame5.rowCount_pos`). A
line-count argument (`Frame5.col_sum` twice). -/
theorem o53_e_alpha (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = false) (h4x : (o 4).negX = false) (h1 : (o 1).swap = true)
    (h2 : (o 2).swap = false) (h3 : (o 3).swap = false) (E : SetupE P p q a b o x5)
    (e0 : o 0 = Orient.tA) : False := by
  have F' := F.toFrame5
  have hq2 := F'.two_le_q
  have hx1 := F.x5_pos
  have ha := E.ha
  have hb2 := E.hb2
  have hx5a := E.hx5a
  have halpha := S.alpha_lt
  -- `u_1 = alpha = x5`, `v_1 = p`
  have hu1 := E.hu1
  rw [e0] at hu1
  simp [Orient.hrun_eq, Orient.tA] at hu1
  have hl := F.side_left
  have v0 : (o 0).colLine p q P 0 = p := by
    rw [e0]; simp [Orient.vrun_eq, Orient.tA, S.fullEA]
  -- the mark of `T_4` is `A`: `v_4 = b - p < q`
  have e3 : o 3 = Orient.wA := by
    cases hx : (o 3).negX
    · exfalso
      have v3 : (o 3).colLine p q P 0 = q := by simp [Orient.vrun_eq, h3, hx, S.fullEB]
      omega
    · exact Orient.ext h3 hx E.m3
  have e4 : o 4 = ⟨false, false, (o 4).negY⟩ := Orient.ext h4 h4x rfl
  -- the columns `p - 1` and `x5`
  have c1 := F'.col_sum (x := p - 1) (by omega) (by omega)
  have c2 := F'.col_sum (x := x5) (by omega) (by omega)
  have z1 : (o 1).colLine p q P (a - 1 - (p - 1)) = 0 :=
    F'.colLine_zero _ (Or.inr (by simp [Orient.W, h1]; omega))
  have z2 : (o 2).colLine p q P (a - 1 - (p - 1)) = 0 :=
    F'.colLine_zero _ (Or.inr (by simp [Orient.W, h2]; omega))
  have z1' : (o 1).colLine p q P (a - 1 - x5) = 0 :=
    F'.colLine_zero _ (Or.inr (by simp [Orient.W, h1]; omega))
  have z2' : (o 2).colLine p q P (a - 1 - x5) = 0 :=
    F'.colLine_zero _ (Or.inr (by simp [Orient.W, h2]; omega))
  rw [z1, z2] at c1
  rw [z1', z2'] at c2
  rw [e0, e3, e4] at c1 c2
  simp only [Orient.tA, Orient.wA, Orient.colLine_wide, Orient.colLine_wide_neg,
    Orient.colLine_tall] at c1 c2
  simp (disch := omega) only [F'.rowCount_zero, add_zero, zero_add] at c1 c2
  have k1 : colCount P (p - 1 - (p - 1)) = q := by
    rw [show p - 1 - (p - 1) = (0 : ℤ) by omega]; exact S.fullEB
  have k2 : colCount P (x5 - x5) = q := by
    rw [show x5 - x5 = (0 : ℤ) by omega]; exact S.fullEB
  have r := F'.rowCount_pos (y := x5) (by omega) (by omega)
  omega

/-- `report-A2.md`, 5.3 (e), "u_1 = q = x_5", first lines: `x5 = q`, and
`[0, q) x [0, b - q)` lies in `T_1` alone, so (10) `kappa_c = q` for
`c < b - q`. -/
theorem o53_e_q_setup (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h0 : (o 0).swap = true) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = false) (E : SetupE P p q a b o x5) (h0x : (o 0).negX = false) :
    x5 = q ∧ ∀ c : ℤ, 0 ≤ c → c < b - q → colCount P c = q := by
  have F' := F.toFrame5
  have hq2 := F'.two_le_q
  have ha := E.ha
  have hb1 := E.hb1
  -- `u_1 = q`: the mark of `T_1` is `E` or `B`
  have hx5 : x5 = q := by
    have hu1 := E.hu1
    rw [Orient.hrun_eq] at hu1
    simp [h0, h0x, S.fullEB] at hu1
    omega
  refine ⟨hx5, fun c hc0 hc1 => (F'.colCount_eq_iff c).2 fun y hy0 hy1 => ?_⟩
  -- `[0, q) x [0, b - q)` lies in `T_1` alone
  have key : ∀ X : ℤ, 0 ≤ X → X < q → ((X, c) : Cell) ∈ t 0 := by
    intro X hX0 hX1
    have hcR : ((X, c) : Cell) ∈ R a b := by
      rw [mem_R]; simp only; omega
    rcases F'.cover_cases hcR with h | h | h | h | h
    · exact h.1
    · have := h.2.1; simp [Orient.W, h1] at this; omega
    · have := h.2.2; simp [Orient.H, h2] at this; omega
    · have := h.2.2; simp [Orient.H, h3] at this; omega
    · have := h.2.1.1; dsimp only at this; omega
  cases hy : (o 0).negY
  · have := (F'.mem0 _).1 (key y hy0 hy1)
    simpa [Orient.back, h0, h0x, hy] using this
  · have := (F'.mem0 _).1 (key (q - 1 - y) (by omega) (by omega))
    simpa [Orient.back, h0, h0x, hy] using this

/-- (T4) for case (e): if the reflection of `R a b` in its vertical midline
exchanges `T_1`, `T_2` and `T_3`, `T_4` (equal codes), then `P` has a reflection
as a symmetry, which three occupied corners exclude (`Frame5.T4_flipX`,
`Three.no_reflection`). -/
private theorem we_flipX (F : Frame5 P p q a b t o x5 y5) (S : ThreeFull P p q)
    (h4 : (o 4).swap = false) (h01 : o 0 = o 1) (h23 : o 2 = o 3) : False := by
  obtain ⟨-, hsym⟩ := F.T4_flipX h01 h23
  exact S.no_reflection (Or.inl fun c => by simpa [h4] using hsym c)

/-- The vertical run of a tall corner tile: `p` for the marks `E`, `A`
(`negY = false`), `beta` for `B` (`negY = true`). -/
private theorem we_tall_vrun {c : Orient} (S : ThreeFull P p q) (hs : c.swap = true) :
    (c.negY = false ∧ c.colLine p q P 0 = p) ∨
      (c.negY = true ∧ c.colLine p q P 0 = rowCount P (q - 1)) := by
  cases hy : c.negY
  · left; simp [Orient.vrun_eq, hs, hy, S.fullEA]
  · right; simp [Orient.vrun_eq, hs, hy]

/-- `report-A2.md`, 5.3 (e), "b < 2q": the marks of `T_4`, `T_3` are not `A`
(cells `(p - 1, b - q)`, `(p, b - q)` of `T_5`), so they are `E`; then the marks
of `T_1`, `T_2` are `B`, and the reflection of `R a b` in its vertical midline
permutes the corner tiles, against (T4). -/
theorem o53_e_q_lt (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = false) (h4x : (o 4).negX = false) (h0 : (o 0).swap = true)
    (h1 : (o 1).swap = true) (h2 : (o 2).swap = false) (h3 : (o 3).swap = false)
    (E : SetupE P p q a b o x5) (h0x : (o 0).negX = false) (hx5 : x5 = q)
    (h10 : ∀ c : ℤ, 0 ≤ c → c < b - q → colCount P c = q) (hb : b < 2 * q) : False := by
  have F' := F.toFrame5
  have hy5 := F.y5_eq
  have ha := E.ha
  have hb1 := E.hb1
  have hq2 := F'.two_le_q
  have hbeta := S.beta_lt
  -- `T_5` contains `[q, b) x [0, q)`, by (10)
  have hT5 : ∀ X Y : ℤ, q ≤ X → X < b → 0 ≤ Y → Y < q → ((X, Y) : Cell) ∈ t 4 := by
    intro X Y hX0 hX1 hY0 hY1
    have hcol := (F'.colCount_eq_iff (X - q)).1 (h10 _ (by omega) (by omega))
    cases hy : (o 4).negY
    · refine (F'.mem_of 4 (d := (X - q, Y)) ?_).2 (hcol _ hY0 hY1)
      simp [loc, Orient.back, h4, h4x, hy, hx5, hy5]
    · refine (F'.mem_of 4 (d := (X - q, q - 1 - Y)) ?_).2 (hcol _ (by omega) (by omega))
      simp [loc, Orient.back, h4, h4x, hy, hx5, hy5]
  -- the mark of `T_4` is not `A`: else `(p - 1, b - q)` is in `T_4` and `T_5`
  have e3 : o 3 = Orient.wE := by
    cases hx : (o 3).negX
    · exact Orient.ext h3 hx E.m3
    · exfalso
      have h34 : ((p - 1, b - q) : Cell) ∈ t 3 := by
        refine (F'.mem_of 3 (d := (0, q - 1)) ?_).2 S.hB
        simp [loc, Orient.back, h3, hx, E.m3]
      have h44 := hT5 (p - 1) (b - q) (by omega) (by omega) (by omega) (by omega)
      exact Finset.disjoint_left.1 (F.tiling.disjoint 3 4 (by decide)) h34 h44
  -- the mark of `T_3` is not `A`: else `(p, b - q)` is in `T_3` and `T_5`
  have e2 : o 2 = Orient.wE := by
    cases hx : (o 2).negX
    · exact Orient.ext h2 hx E.m2
    · exfalso
      have h24 : ((p, b - q) : Cell) ∈ t 2 := by
        refine (F'.mem_of 2 (d := (0, q - 1)) ?_).2 S.hB
        simp [loc, Orient.back, h2, hx, E.m2, ha]
        omega
      have h44 := hT5 p (b - q) (by omega) hb1 (by omega) (by omega)
      exact Finset.disjoint_left.1 (F.tiling.disjoint 2 4 (by decide)) h24 h44
  -- `v_1 = v_2 = b - q < p`: the marks of `T_1`, `T_2` are `B`
  have hl := F.side_left
  have hr := F.side_right
  have v3 : (o 3).colLine p q P 0 = q := by
    rw [e3]; simp [Orient.vrun_eq, Orient.wE, S.fullEB]
  have v2 : (o 2).colLine p q P 0 = q := by
    rw [e2]; simp [Orient.vrun_eq, Orient.wE, S.fullEB]
  have e0 : o 0 = Orient.tB := by
    rcases we_tall_vrun S h0 with ⟨-, hv⟩ | ⟨hy, -⟩
    · omega
    · exact Orient.ext h0 h0x hy
  have e1 : o 1 = Orient.tB := by
    rcases we_tall_vrun S h1 with ⟨-, hv⟩ | ⟨hy, -⟩
    · omega
    · have hm := S.mark F' (i := 1) (by decide)
      have hx : (o 1).negX = false := by
        revert hm; rw [hy]; cases (o 1).negX <;> simp
      exact Orient.ext h1 hx hy
  exact we_flipX F' S h4 (e0.trans e1.symm) (e2.trans e3.symm)

/-- `report-A2.md`, 5.3 (e), "b = 2q": a column `x` with `q ≤ x < 2p - q` is full
in `T_5` and in `T_3` or `T_4`; the marks of `T_4`, `T_3` are `A`; `m_1 = m_2`
is against (T4); so `m_1 = E`, `m_2 = A`, `p = 2q - alpha`, and the columns
`c = p - q` and `2p - 1 - c` have sums that differ by at least 1 (`T_5` meets
only the second). A line-count argument (`Frame5.col_sum` twice,
`Frame5.colLine_pos`). -/
theorem o53_e_q_eq (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = false) (h4x : (o 4).negX = false) (h0 : (o 0).swap = true)
    (h1 : (o 1).swap = true) (h2 : (o 2).swap = false) (h3 : (o 3).swap = false)
    (E : SetupE P p q a b o x5) (h0x : (o 0).negX = false) (hx5 : x5 = q)
    (h10 : ∀ c : ℤ, 0 ≤ c → c < b - q → colCount P c = q) (hb : b = 2 * q) : False := by
  -- (10) is not needed for `b = 2q`; the statement keeps it for the caller
  have _ := h10
  have F' := F.toFrame5
  have ha := E.ha
  have hq2 := F'.two_le_q
  have halpha := S.alpha_pos
  have hbeta := S.beta_lt
  have W0 : (o 0).W p q = q := by simp [Orient.W, h0]
  have W1 : (o 1).W p q = q := by simp [Orient.W, h1]
  have W2 : (o 2).W p q = p := by simp [Orient.W, h2]
  have W3 : (o 3).W p q = p := by simp [Orient.W, h3]
  have H2 : (o 2).H p q = q := by simp [Orient.H, h2]
  have H3 : (o 3).H p q = q := by simp [Orient.H, h3]
  have H4 : (o 4).H p q = q := by simp [Orient.H, h4]
  -- column `p - 1` is full in `T_4`: its mark is not `E` (the corner `D`), so `A`
  have e3 : o 3 = Orient.wA := by
    cases hx : (o 3).negX
    · exfalso
      have hs := F'.col_sum (x := p - 1) (by omega) (by omega)
      have z0 : (o 0).colLine p q P (p - 1) = 0 := F'.colLine_zero _ (Or.inr (by omega))
      have z1 : (o 1).colLine p q P (a - 1 - (p - 1)) = 0 :=
        F'.colLine_zero _ (Or.inr (by omega))
      have z2 : (o 2).colLine p q P (a - 1 - (p - 1)) = 0 :=
        F'.colLine_zero _ (Or.inr (by omega))
      have l3 := F'.colLine_le (o 3) (p - 1)
      have l4 := F'.colLine_le (o 4) (p - 1 - x5)
      have hfull : (o 3).colLine p q P (p - 1) = (o 3).H p q := by omega
      have hD := (F'.colLine_eq_iff (o 3) (p - 1)).1 hfull (q - 1) (by omega) (by omega)
      simp [Orient.back, h3, hx, E.m3] at hD
      exact S.hD hD
    · exact Orient.ext h3 hx E.m3
  -- column `p` is full in `T_3`: its mark is `A`
  have e2 : o 2 = Orient.wA := by
    cases hx : (o 2).negX
    · exfalso
      have hs := F'.col_sum (x := p) (by omega) (by omega)
      rw [show a - 1 - p = p - 1 by omega] at hs
      have z0 : (o 0).colLine p q P p = 0 := F'.colLine_zero _ (Or.inr (by omega))
      have z1 : (o 1).colLine p q P (p - 1) = 0 := F'.colLine_zero _ (Or.inr (by omega))
      have z3 : (o 3).colLine p q P p = 0 := F'.colLine_zero _ (Or.inr (by omega))
      have l2 := F'.colLine_le (o 2) (p - 1)
      have l4 := F'.colLine_le (o 4) (p - x5)
      have hfull : (o 2).colLine p q P (p - 1) = (o 2).H p q := by omega
      have hD := (F'.colLine_eq_iff (o 2) (p - 1)).1 hfull (q - 1) (by omega) (by omega)
      simp [Orient.back, h2, hx, E.m2] at hD
      exact S.hD hD
    · exact Orient.ext h2 hx E.m2
  -- `v_3 = v_4 = alpha`, so `v_1 = v_2 = 2q - alpha`
  have hl := F.side_left
  have hr := F.side_right
  have v3 : (o 3).colLine p q P 0 = colCount P (p - 1) := by
    rw [e3]; simp [Orient.vrun_eq, Orient.wA]
  have v2 : (o 2).colLine p q P 0 = colCount P (p - 1) := by
    rw [e2]; simp [Orient.vrun_eq, Orient.wA]
  rcases we_tall_vrun S h0 with ⟨hy0, hv0⟩ | ⟨hy0, hv0⟩
  · -- `m_1 = E`: `v_2 = p`, so `m_2` is `E` (against (T4)) or `A`
    have e0 : o 0 = Orient.tE := Orient.ext h0 h0x hy0
    rcases we_tall_vrun S h1 with ⟨hy1, hv1⟩ | ⟨hy1, hv1⟩
    · cases hx1 : (o 1).negX
      · have e1 : o 1 = Orient.tE := Orient.ext h1 hx1 hy1
        exact we_flipX F' S h4 (e0.trans e1.symm) (e2.trans e3.symm)
      · have e1 : o 1 = Orient.tA := Orient.ext h1 hx1 hy1
        -- `p = 2q - alpha`; the columns `p - q` and `p + q - 1`
        have hp2 : p + colCount P (p - 1) = b := by omega
        have e4 : o 4 = ⟨false, false, (o 4).negY⟩ := Orient.ext h4 h4x rfl
        have c1 := F'.col_sum (x := p - q) (by omega) (by omega)
        have c2 := F'.col_sum (x := p + q - 1) (by omega) (by omega)
        rw [e0, e1, e2, e3, e4] at c1 c2
        simp only [Orient.tE, Orient.tA, Orient.wA, Orient.colLine_wide,
          Orient.colLine_wide_neg, Orient.colLine_tall] at c1 c2
        simp (disch := omega) only [F'.rowCount_zero, F'.colCount_zero, add_zero,
          zero_add] at c1 c2
        have r1 : rowCount P (a - 1 - (p + q - 1)) = rowCount P (p - q) := by
          congr 1; omega
        have k1 : colCount P (p - 1 - (a - 1 - (p + q - 1))) = colCount P (q - 1) := by
          congr 1; omega
        have k2 : colCount P (p - 1 - (p - q)) = colCount P (q - 1) := by
          congr 1; omega
        have k3 : colCount P (p + q - 1 - x5) = colCount P (p - 1) := by
          congr 1; omega
        omega
    · omega
  · -- `m_1 = B`: `v_2 = beta < p`, so `m_2 = B`, against (T4)
    rcases we_tall_vrun S h1 with ⟨hy1, hv1⟩ | ⟨hy1, hv1⟩
    · omega
    · have hm := S.mark F' (i := 1) (by decide)
      have hx1 : (o 1).negX = false := by
        revert hm; rw [hy1]; cases (o 1).negX <;> simp
      have e0 : o 0 = Orient.tB := Orient.ext h0 h0x hy0
      have e1 : o 1 = Orient.tB := Orient.ext h1 hx1 hy1
      exact we_flipX F' S h4 (e0.trans e1.symm) (e2.trans e3.symm)

/-- `report-A2.md`, 5.3 (e), "T_3, T_4 wide", with `x* = x5`. -/
theorem o53_e_ww_norm (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = false) (h4x : (o 4).negX = false) (h0 : (o 0).swap = true)
    (h1 : (o 1).swap = true) (h2 : (o 2).swap = false) (h3 : (o 3).swap = false) : False := by
  have E := o53_e_setup F S hq h4 h4x h0 h1 h2 h3
  cases h0x : (o 0).negX
  · obtain ⟨hx5, h10⟩ := o53_e_q_setup F S hq h0 h1 h2 h3 E h0x
    rcases lt_or_eq_of_le E.hb2 with hb | hb
    · exact o53_e_q_lt F S hq h4 h4x h0 h1 h2 h3 E h0x hx5 h10 hb
    · exact o53_e_q_eq F S hq h4 h4x h0 h1 h2 h3 E h0x hx5 h10 hb
  · have h0y : (o 0).negY = false := by
      have hm := S.mark F.toFrame5 (i := 0) (by decide)
      revert hm; rw [h0x]; cases (o 0).negY <;> simp
    exact o53_e_alpha F S hq h4 h4x h1 h2 h3 E (Orient.ext h0 h0x h0y)

/-- `report-A2.md`, 5.3 (e), "T_3, T_4 wide" ("Reflect R so that x* = x_5"). -/
theorem o53_e_ww (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = false) (h0 : (o 0).swap = true) (h1 : (o 1).swap = true)
    (h2 : (o 2).swap = false) (h3 : (o 3).swap = false) : False := by
  cases hx : (o 4).negX
  · exact o53_e_ww_norm F S hq h4 hx h0 h1 h2 h3
  · obtain ⟨t', F'⟩ := F.flipX
    exact o53_e_ww_norm F' S hq (by simpa using h4) (by simp [Orient.reflX, h4, hx])
      (by simpa using h1) (by simpa using h0) (by simpa using h3) (by simpa using h2)

/-! ## `T_5` wide; the entry statement of 5.3 -/

/-- **`report-A2.md`, 5.3, "T_5 wide".** -/
theorem o53_wide (F : FrameO P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h4 : (o 4).swap = false) : False := by
  cases h0 : (o 0).swap
  · cases h1 : (o 1).swap
    · exact o53_wide_both F S hq h4 h0 h1
    · exact o53_d F S hq h4 h0 h1
  · cases h1 : (o 1).swap
    · obtain ⟨t', F'⟩ := F.flipX
      exact o53_d F' S hq (by simpa using h4) (by simpa using h1) (by simpa using h0)
    · cases h2 : (o 2).swap
      · cases h3 : (o 3).swap
        · exact o53_e_ww F S hq h4 h0 h1 h2 h3
        · exact o53_a F S hq h0 h1 fun h => Bool.noConfusion (h2.symm.trans (h.trans h3))
      · cases h3 : (o 3).swap
        · exact o53_a F S hq h0 h1 fun h => Bool.noConfusion (h2.symm.trans (h.trans h3))
        · exact o53_e_tt F S hq h4 h0 h1 h2 h3

/-- **`report-A2.md`, 5.3.** Pattern O with three occupied corners does not
occur. -/
theorem three_O (F : FrameO P p q a b t o x5 y5) (S : Three P p q) (hpq : q ≤ p) : False := by
  have S' := S.full_O F
  rcases eq_or_lt_of_le hpq with h | hq
  · exact o53_sq F S' h.symm
  · cases h4 : (o 4).swap
    · exact o53_wide F S' hq h4
    · exact o53_tall F S' hq h4

end PolyominoOddOrder
