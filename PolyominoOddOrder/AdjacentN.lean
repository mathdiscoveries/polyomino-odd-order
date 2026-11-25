module

public import PolyominoOddOrder.AllEqual

/-!
# Case (I), two adjacent occupied corners: common part and pattern N (`AdjacentN.lean`)

Blueprint unit C5 (third increment). `report-A2.md`, section 6 up to the end of
6.2. Normal form (`Adjacent`): `A = (0, 0)` and `C = (p - 1, 0)` are in `P`, the
two upper corners of `box(P)` are not; `F` is the bottom row of `box(P)`,
`L = p`, `M = q`, and no order between `p` and `q` is assumed.

| report | Lean |
|---|---|
| mark `A` / `C` of `T_i` | `(o i).negY = false` and `(o i).negX = false` / `true` |
| `F` of `T_i` horizontal (h) / vertical (v) | `(o i).swap = false` / `true` |
| `F` is full | `AdjFull.fullF` |
| `r_A`, `r_C` | `colCount P 0`, `colCount P (p - 1)` |
| `lambda(j)`, `f` | `rowCount P j`, `rowCount P (q - 1)` |
| `X_A(c)`, `X_C(c)` | `colCount P c`, `colCount P (p - 1 - c)` |
| "name m_3 = C" | the mirror image of `P`: `Adjacent.flipPX`, `FrameO.flipPX` |

Entry statements (binding): `Adjacent.full`, `lemma61_bottom`, `lemma61_top`,
`lemma61_left`, `lemma61_right` (used by `AdjacentO.lean`) and `adj_N`. A proof
unit may reshape the nodes marked PROVISIONAL.

Source: `theoretician/report-A2.md` (goals lab, commit `076d663`), section 6.
-/

@[expose] public section

namespace PolyominoOddOrder

open Orient (cornerP)

variable {P : Finset Cell} {p q a b : ℤ} {t : Fin 5 → Finset Cell} {o : Fin 5 → Orient}
  {x5 y5 : ℤ}

/-! ## Marks, the side `F`, runs -/

/-- The mark of a corner tile is `A` or `C`. -/
theorem Adjacent.mark (S : Adjacent P p q) (F : Frame5 P p q a b t o x5 y5) {i : Fin 5}
    (hi : i ≠ 4) : (o i).negY = false := by
  have h := F.mark_mem hi
  cases hy : (o i).negY
  · rfl
  · rw [hy] at h
    cases hx : (o i).negX
    · rw [hx, cornerP_ft] at h
      exact absurd h S.h01
    · rw [hx, cornerP_tt] at h
      exact absurd h S.h11

/-- The mirror image of `P` in the vertical midline of its box exchanges `A` and
`C` ("name m_3 = C"). -/
theorem Adjacent.flipPX (S : Adjacent P p q) :
    Adjacent (P.image (GridIso.flipX p).apply) p q := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← cornerP_ff (p := p) (q := q), cornerP_mem_flipPX]
    simpa [cornerP] using S.hC
  · rw [← cornerP_tf (p := p) (q := q), cornerP_mem_flipPX]
    simpa [cornerP] using S.hA
  · rw [← cornerP_ft (p := p) (q := q), cornerP_mem_flipPX]
    simpa [cornerP] using S.h11
  · rw [← cornerP_tt (p := p) (q := q), cornerP_mem_flipPX]
    simpa [cornerP] using S.h01

/-- (3) of `report-A2.md`, section 3, for two adjacent corners in pattern N:
both `A` and `C` are used. -/
theorem Adjacent.not_sameMarks_N (S : Adjacent P p q) (F : FrameN P p q a b t o x5 y5) :
    ¬ SameMarks o := fun hm => S.h11 (allEqual_N F hm).c11

/-- Two adjacent occupied corners together with what `report-A2.md`, section 6,
first paragraph, derives at once: `F` is full, `1 ≤ r_A, r_C < M`,
`1 ≤ f ≤ L - 2`. Here `r_A`, `r_C` are the numbers of cells of `P` on the two
sides of `box(P)` perpendicular to `F`, whether or not `A`, `C` are marks. -/
structure AdjFull (P : Finset Cell) (p q : ℤ) : Prop extends Adjacent P p q where
  /-- `F` is full: `lambda(0) = L`. -/
  fullF : rowCount P 0 = p
  /-- `r_A ≥ 1`. -/
  rA_pos : 1 ≤ colCount P 0
  /-- `r_A < M`. -/
  rA_lt : colCount P 0 < q
  /-- `r_C ≥ 1`. -/
  rC_pos : 1 ≤ colCount P (p - 1)
  /-- `r_C < M`. -/
  rC_lt : colCount P (p - 1) < q
  /-- `f ≥ 1`. -/
  f_pos : 1 ≤ rowCount P (q - 1)
  /-- `f ≤ L - 2`: the two ends of the layer `M - 1` are not in `P`. -/
  f_le : rowCount P (q - 1) ≤ p - 2

/-- `report-A2.md`, section 6, first paragraph, for the side `F`: if the mark of a
corner tile is `A` or `C`, its run along `F` is the whole side by (Full), as the
other end of `F` is occupied. The same argument as `Three.fullEA_of`
(`ThreeCorners.lean`). -/
private theorem ac_fullF_of (S : Adjacent P p q) (F : Frame5 P p q a b t o x5 y5)
    {i : Fin 5} (hi : i ≠ 4) (hy : (o i).negY = false) : rowCount P 0 = p := by
  have hfar : cornerP p q (!(o i).negX) false ∈ P := by
    cases (o i).negX
    · simpa [cornerP] using S.hC
    · simpa [cornerP] using S.hA
  cases hs : (o i).swap
  · have h := F.hrun_of_far hi (by simpa [hs, hy] using hfar)
    simpa [Orient.hrun_eq, hs, hy, Orient.W] using h
  · have h := F.vrun_of_far hi (by simpa [hs, hy] using hfar)
    simpa [Orient.vrun_eq, hs, hy, Orient.H] using h

/-- `report-A2.md`, section 6, first paragraph: "the two ends of layer M - 1 are
the corners not in P, so f ≤ L - 2". The cells of `P` in the row `q - 1` lie in
the columns `1, ..., p - 2`. -/
private theorem ac_f_le (S : Adjacent P p q) (F : Frame5 P p q a b t o x5 y5) :
    rowCount P (q - 1) ≤ p - 2 := by
  have hsub : (P.filter fun c => c.2 = q - 1) ⊆
      Finset.Ico 1 (p - 1) ×ˢ ({q - 1} : Finset ℤ) := by
    rintro ⟨x, y⟩ hc
    obtain ⟨hcP, hcy⟩ := Finset.mem_filter.1 hc
    simp only at hcy
    subst hcy
    have hb := F.P_bounds hcP
    simp only at hb
    have h0 : x ≠ 0 := by
      rintro rfl
      exact S.h01 hcP
    have h1 : x ≠ p - 1 := by
      rintro rfl
      exact S.h11 hcP
    rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico]
    exact ⟨⟨by omega, by omega⟩, rfl⟩
  have h := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_singleton, mul_one, Int.card_Ico] at h
  have hp := F.two_le_p
  unfold rowCount
  omega

/-- `report-A2.md`, section 6, first paragraph: "One of A, C is used, so F is
full. ... r < M, as the other corners are not occupied. ... f = lambda(M - 1) ≥ 1;
the two ends of layer M - 1 are the corners not in P, so f ≤ L - 2." The mark of
`T_1` is `A` or `C` (`Adjacent.mark`), so (Full) gives `F`; the bounds are
`Frame5.colCount_pos`, `colCount_le`, `colCount_eq_iff` at the columns `0` and
`p - 1`, and `Frame5.rowCount_pos` at the row `q - 1`. -/
theorem Adjacent.full (S : Adjacent P p q) (F : Frame5 P p q a b t o x5 y5) :
    AdjFull P p q := by
  have hp := F.two_le_p
  have hq := F.two_le_q
  have hA := F.colCount_le 0
  have hC := F.colCount_le (p - 1)
  refine ⟨S, ac_fullF_of S F (i := 0) (by decide) (S.mark F (by decide)),
    F.colCount_pos (by omega) (by omega), ?_, F.colCount_pos (by omega) (by omega), ?_,
    F.rowCount_pos (by omega) (by omega), ac_f_le S F⟩
  · refine lt_of_le_of_ne hA fun h => S.h01 ?_
    exact (F.colCount_eq_iff 0).1 h (q - 1) (by omega) (by omega)
  · refine lt_of_le_of_ne hC fun h => S.h11 ?_
    exact (F.colCount_eq_iff (p - 1)).1 h (q - 1) (by omega) (by omega)

/-! ## Lemma 6.1 -/

/-- **`report-A2.md`, Lemma 6.1, bottom side.** At a free side at least one of
the two corner tiles has its `F` along this side. Otherwise both boxes have
extent `L` perpendicular to the side; equal marks: (T1) gives `r = M`
(`Frame5.T1_bottom`); different marks: (T5) (`Frame5.T5_bottom`: the second code
is the first with the local vertical direction reversed). In codes: both tiles
are tall with `negY = false`; equal `negX` makes the codes equal, and the run
`colCount P 0` or `colCount P (p - 1)` would be `q`; different `negX` makes
`o 1 = (o 0).reflY`. -/
theorem lemma61_bottom (F : Frame5 P p q a b t o x5 y5) (S : AdjFull P p q) (hfree : 1 ≤ y5) :
    (o 0).swap = false ∨ (o 1).swap = false := by
  have hm0 := S.toAdjacent.mark F (i := 0) (by decide)
  have hm1 := S.toAdjacent.mark F (i := 1) (by decide)
  have hA := S.rA_lt
  have hC := S.rC_lt
  rcases e0 : o 0 with ⟨s0, x0, y0⟩
  rcases e1 : o 1 with ⟨s1, x1, y1⟩
  rw [e0] at hm0
  rw [e1] at hm1
  simp only at hm0 hm1
  subst hm0 hm1
  cases s0
  · exact Or.inl rfl
  cases s1
  · exact Or.inr rfl
  exfalso
  cases x0 <;> cases x1
  · -- both marks `A`: (T1) gives `r_A = M`
    have h1 := (F.T1_bottom hfree (e0.trans e1.symm)).1
    rw [e0] at h1
    simp [Orient.rowLine, Orient.W] at h1
    omega
  · -- marks `A`, `C`: (T5)
    exact F.T5_bottom hfree (by simp [e0, e1, Orient.reflY])
  · -- marks `C`, `A`: (T5)
    exact F.T5_bottom hfree (by simp [e0, e1, Orient.reflY])
  · -- both marks `C`: (T1) gives `r_C = M`
    have h1 := (F.T1_bottom hfree (e0.trans e1.symm)).1
    rw [e0] at h1
    simp [Orient.rowLine, Orient.W] at h1
    omega

/-- Lemma 6.1 at a free top side. -/
theorem lemma61_top (F : Frame5 P p q a b t o x5 y5) (S : AdjFull P p q)
    (hfree : y5 + (o 4).H p q ≤ b - 1) : (o 2).swap = false ∨ (o 3).swap = false := by
  obtain ⟨t', F'⟩ := F.flipY
  have h := lemma61_bottom F' S (by omega)
  simpa [or_comm] using h

/-- Lemma 6.1 at a free left side: `F` along a vertical side is `v`. -/
theorem lemma61_left (F : Frame5 P p q a b t o x5 y5) (S : AdjFull P p q) (hfree : 1 ≤ x5) :
    (o 0).swap = true ∨ (o 3).swap = true := by
  obtain ⟨t', F'⟩ := F.transpose
  have h := lemma61_bottom F' S hfree
  simpa using h

/-- Lemma 6.1 at a free right side. -/
theorem lemma61_right (F : Frame5 P p q a b t o x5 y5) (S : AdjFull P p q)
    (hfree : x5 + (o 4).W p q ≤ a - 1) : (o 1).swap = true ∨ (o 2).swap = true := by
  obtain ⟨t', F'⟩ := F.transpose
  have h := lemma61_top F' S (by simpa using hfree)
  simpa [or_comm] using h

/-! ## 6.2 Pattern N -/

/-- `report-A2.md`, 6.2: "every side of R contains exactly one F. So going around
they all lie on the side that follows the corner or all on the side that
precedes it." From Lemma 6.1 at the four sides. -/
theorem n62_types (F : FrameN P p q a b t o x5 y5) (S : AdjFull P p q) :
    ((o 0).swap = false ∧ (o 1).swap = true ∧ (o 2).swap = false ∧ (o 3).swap = true) ∨
      ((o 0).swap = true ∧ (o 1).swap = false ∧ (o 2).swap = true ∧ (o 3).swap = false) := by
  have hb := lemma61_bottom F.toFrame5 S F.y5_pos
  have ht := lemma61_top F.toFrame5 S F.y5_le
  have hl := lemma61_left F.toFrame5 S F.x5_pos
  have hr := lemma61_right F.toFrame5 S F.x5_le
  revert hb ht hl hr
  cases (o 0).swap <;> cases (o 1).swap <;> cases (o 2).swap <;> cases (o 3).swap <;> simp

/-- `report-A2.md`, 6.2, from "By (1)" to "So r_A = r_C =: r, a = b = L + r":
with `F` on the bottom for `T_1`, on the right for `T_2`, on top for `T_3`, on
the left for `T_4`. If `r_A ≠ r_C`, then `m_1 = m_3` and `m_2 = m_4`, the half
turn of `R a b` permutes the corner tiles and `P` has a half turn by (T4)
(`Frame5.T4_halfTurn`), which maps `A` to a corner that is not in `P`. -/
theorem n62_r (F : FrameN P p q a b t o x5 y5) (S : AdjFull P p q)
    (h0 : (o 0).swap = false) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) :
    colCount P (p - 1) = colCount P 0 ∧ a = p + colCount P 0 ∧ b = p + colCount P 0 := by
  have F5 := F.toFrame5
  have m0 := S.mark F5 (i := 0) (by decide)
  have m1 := S.mark F5 (i := 1) (by decide)
  have m2 := S.mark F5 (i := 2) (by decide)
  have m3 := S.mark F5 (i := 3) (by decide)
  -- (1): `a = L + r_{m_2} = L + r_{m_4}`, `b = L + r_{m_1} = L + r_{m_3}`
  have hb := F.side_bottom
  have ht := F.side_top
  have hl := F.side_left
  have hr := F.side_right
  rw [Orient.hrun_eq, Orient.hrun_eq] at hb ht
  rw [Orient.vrun_eq, Orient.vrun_eq] at hl hr
  simp only [h0, h1, h2, h3, m0, m1, m2, m3, Bool.false_eq_true, ↓reduceIte, S.fullF] at hb ht hl hr
  by_cases hrr : colCount P (p - 1) = colCount P 0
  · refine ⟨hrr, ?_, ?_⟩
    · cases hx : (o 1).negX <;> simp only [hx, Bool.false_eq_true, ↓reduceIte] at hb <;> omega
    · cases hx : (o 0).negX <;> simp only [hx, Bool.false_eq_true, ↓reduceIte] at hl <;> omega
  · -- `r_A ≠ r_C`: `m_1 = m_3`, `m_2 = m_4`, and (T4) gives a half turn of `P`
    exfalso
    have e02 : o 0 = o 2 := by
      refine Orient.ext (h0.trans h2.symm) ?_ (m0.trans m2.symm)
      cases hx0 : (o 0).negX <;> cases hx2 : (o 2).negX <;>
        simp only [hx0, hx2, Bool.false_eq_true, ↓reduceIte] at hl hr <;> first | rfl | omega
    have e13 : o 1 = o 3 := by
      refine Orient.ext (h1.trans h3.symm) ?_ (m1.trans m3.symm)
      cases hx1 : (o 1).negX <;> cases hx3 : (o 3).negX <;>
        simp only [hx1, hx3, Bool.false_eq_true, ↓reduceIte] at hb ht <;> first | rfl | omega
    obtain ⟨-, -, hsym⟩ := F5.T4_halfTurn e02 e13
    exact S.h11 (by simpa using (hsym (0, 0)).1 S.hA)

/-- The side of `box(P)` at the mark of a corner tile, perpendicular to `F`, holds
the cells of `P` in an interval from `F` (`report-A2.md`, section 1.2, (R)). -/
private theorem an_col (F : Frame5 P p q a b t o x5 y5) (S : Adjacent P p q) {i : Fin 5}
    (hi : i ≠ 4) (y : ℤ) :
    ((if (o i).negX then p - 1 else 0, y) : Cell) ∈ P ↔
      0 ≤ y ∧ y < colCount P (if (o i).negX then p - 1 else 0) := by
  have hm := S.mark F hi
  cases hs : (o i).swap
  · have h := F.vside hi y
    cases hx : (o i).negX <;> simpa [Orient.back, Orient.colLine, hs, hx, hm] using h
  · have h := F.hside hi y
    cases hx : (o i).negX <;> simpa [Orient.back, Orient.rowLine, hs, hx, hm] using h

/-- Both `A` and `C` are used (`report-A2.md`, 6.2, "By (3)"), so both sides of
`box(P)` perpendicular to `F` hold the cells of `P` in an interval from `F`. -/
private theorem an_cols (F : FrameN P p q a b t o x5 y5) (S : Adjacent P p q) (y : ℤ) :
    (((0, y) : Cell) ∈ P ↔ 0 ≤ y ∧ y < colCount P 0) ∧
      (((p - 1, y) : Cell) ∈ P ↔ 0 ≤ y ∧ y < colCount P (p - 1)) := by
  have hex : ∀ n : Bool, ∃ i : Fin 5, i ≠ 4 ∧ (o i).negX = n := by
    intro n
    by_contra h
    simp only [not_exists, not_and] at h
    exact S.not_sameMarks_N F fun i hi =>
      ⟨bool_eq_of_ne (h i hi) (h 0 (by decide)),
        (S.mark F.toFrame5 hi).trans (S.mark F.toFrame5 (i := 0) (by decide)).symm⟩
  obtain ⟨i, hi, hiA⟩ := hex false
  obtain ⟨j, hj, hjC⟩ := hex true
  have hA := an_col F.toFrame5 S hi y
  have hC := an_col F.toFrame5 S hj y
  rw [hiA] at hA
  rw [hjC] at hC
  exact ⟨by simpa using hA, by simpa using hC⟩

/-- `report-A2.md`, 6.2, the geometry before the count, with `F` of `T_5`
horizontal and the lowest row of `box(T_5)`: `2 ≤ r < L`, `r + 1 ≤ y5 ≤ L - 2`
and `M ≤ L - 2`. The cells `(L - 1, y')` with `y' < r` (in `T_1`), `(r, y')` with
`y' ≥ L` (in `T_3`), `(r - 1, r)` (in `T_4`) and `(L, L - 1)` (in `T_2`) lie in
the columns of `F` of `T_5`. PROVISIONAL (a leaf of `n62_low`). -/
theorem n62_low_dims (F : FrameN P p q a b t o x5 y5) (S : AdjFull P p q)
    (h0 : (o 0).swap = false) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) (h4 : (o 4).swap = false) (h4y : (o 4).negY = false) :
    2 ≤ colCount P 0 ∧ colCount P 0 < p ∧ colCount P 0 + 1 ≤ y5 ∧ y5 ≤ p - 2 ∧ q ≤ p - 2 := by
  have F5 := F.toFrame5
  obtain ⟨hrC, ha, hb⟩ := n62_r F S h0 h1 h2 h3
  have m0 := S.mark F5 (i := 0) (by decide)
  have m1 := S.mark F5 (i := 1) (by decide)
  have m2 := S.mark F5 (i := 2) (by decide)
  have m3 := S.mark F5 (i := 3) (by decide)
  have hrA := S.rA_pos
  have hrq := S.rA_lt
  have hp2 := F5.two_le_p
  have hx5 := F.x5_pos
  have hx5' := F.x5_le
  have hy5 := F.y5_pos
  have hy5' := F.y5_le
  have hW4 : (o 4).W p q = p := by simp [Orient.W, h4]
  have hH4 : (o 4).H p q = q := by simp [Orient.H, h4]
  rw [hW4] at hx5'
  rw [hH4] at hy5'
  -- the sides of `box(P)` at `A` and at `C` hold the cells `[0, r)`
  have hcol : ∀ (n : Bool) (y : ℤ), 0 ≤ y → y < colCount P 0 →
      ((if n then 0 else p - 1, y) : Cell) ∈ P := by
    intro n y hy0 hy1
    obtain ⟨hc0, hc1⟩ := an_cols F S.toAdjacent y
    cases n
    · exact hc1.2 ⟨hy0, by omega⟩
    · exact hc0.2 ⟨hy0, hy1⟩
  have hrow : ∀ x : ℤ, 0 ≤ x → x < p → ((x, 0) : Cell) ∈ P :=
    fun x h h' => (F5.rowCount_eq_iff 0).1 S.fullF x h h'
  -- `(L - 1, y')` with `y' < r` in `T_1`
  have c0 : ∀ y : ℤ, 0 ≤ y → y < colCount P 0 → ((p - 1, y) : Cell) ∈ t 0 := by
    intro y hy0 hy1
    refine (F5.mem_of 0 (d := (if (o 0).negX then 0 else p - 1, y)) ?_).2 (hcol _ y hy0 hy1)
    cases hx : (o 0).negX <;> simp [loc, Orient.back, h0, hx, m0]
  -- `(L, L - 1)` in `T_2`
  have c1 : ((p, p - 1) : Cell) ∈ t 1 := by
    refine (F5.mem_of 1 (d := (if (o 1).negX then 0 else p - 1, colCount P 0 - 1)) ?_).2
      (hcol _ _ (by omega) (by omega))
    cases hx : (o 1).negX <;> simp [loc, Orient.back, h1, hx, m1] <;> omega
  -- `(r, y')` with `y' ≥ L` in `T_3`
  have c2 : ∀ y : ℤ, p ≤ y → y < b → ((colCount P 0, y) : Cell) ∈ t 2 := by
    intro y hy0 hy1
    refine (F5.mem_of 2 (d := (if (o 2).negX then 0 else p - 1, b - 1 - y)) ?_).2
      (hcol _ _ (by omega) (by omega))
    cases hx : (o 2).negX <;> simp [loc, Orient.back, h2, hx, m2] <;> omega
  -- `(x, r)` with `x < r` in `T_4`
  have c3 : ∀ x : ℤ, 0 ≤ x → x < colCount P 0 → ((x, colCount P 0) : Cell) ∈ t 3 := by
    intro x hx0 hx1
    refine (F5.mem_of 3 (d := (if (o 3).negX then 0 else p - 1, x)) ?_).2 (hcol _ x hx0 hx1)
    cases hx : (o 3).negX <;> simp [loc, Orient.back, h3, hx, m3] <;> omega
  -- the row `y5` of `box(T_5)` (its `F`) lies in `T_5`
  have c4 : ∀ x : ℤ, x5 ≤ x → x < x5 + p → ((x, y5) : Cell) ∈ t 4 := by
    intro x hx0 hx1
    cases hx : (o 4).negX
    · refine (F5.mem_of 4 (d := (x - x5, 0)) ?_).2 (hrow _ (by omega) (by omega))
      simp [loc, Orient.back, h4, hx, h4y]
    · refine (F5.mem_of 4 (d := (p - 1 - (x - x5), 0)) ?_).2 (hrow _ (by omega) (by omega))
      simp [loc, Orient.back, h4, hx, h4y]
  have hr2 : 2 ≤ colCount P 0 := by omega
  -- `r < L`: otherwise the row `r` of `T_1` lies in `T_4`
  have hrp : colCount P 0 < p := by
    by_contra hge
    obtain ⟨xt, hxt⟩ := F5.top
    obtain ⟨x', hx'⟩ := F5.conn_P.exists_in_row S.hA hxt (y := colCount P 0)
      (by dsimp only; omega) (by dsimp only; omega)
    have hb' := F5.P_bounds hx'
    simp only at hb'
    have hc : ((if (o 0).negX then p - 1 - x' else x', colCount P 0) : Cell) ∈ t 0 := by
      refine (F5.mem_of 0 (d := (x', colCount P 0)) ?_).2 hx'
      cases hx : (o 0).negX <;> simp [loc, Orient.back, h0, hx, m0]
    have hc' := c3 (if (o 0).negX then p - 1 - x' else x') (by split <;> omega)
      (by split <;> omega)
    exact absurd (F5.tile_unique hc hc') (by decide)
  -- `r + 1 ≤ y5`: the cells `(L - 1, y5)` (if `y5 < r`) and `(r - 1, r)` (if `y5 = r`)
  have hy5r : colCount P 0 + 1 ≤ y5 := by
    by_contra hlt
    rcases (by omega : y5 < colCount P 0 ∨ y5 = colCount P 0) with hlt' | heq
    · exact absurd (F5.tile_unique (c0 y5 (by omega) hlt') (c4 (p - 1) (by omega) (by omega)))
        (by decide)
    · have h4' := c4 (colCount P 0 - 1) (by omega) (by omega)
      rw [heq] at h4'
      exact absurd (F5.tile_unique (c3 (colCount P 0 - 1) (by omega) (by omega)) h4')
        (by decide)
  -- `y5 ≤ L - 2`: the cells `(r, y5)` (if `y5 ≥ L`) and `(L, L - 1)` (if `y5 = L - 1`)
  have hy5p : y5 ≤ p - 2 := by
    by_contra hlt
    rcases (by omega : p ≤ y5 ∨ y5 = p - 1) with hge | heq
    · exact absurd (F5.tile_unique (c2 y5 hge (by omega)) (c4 _ (by omega) (by omega)))
        (by decide)
    · have h4' := c4 p (by omega) (by omega)
      rw [heq] at h4'
      exact absurd (F5.tile_unique c1 h4') (by decide)
  exact ⟨hr2, hrp, hy5r, hy5p, by omega⟩

/-- `report-A2.md`, 6.2, the count ("Consider lines at distance c < r from a side
of R ... Contradiction."), with `F` of `T_5` horizontal and the lowest row of
`box(T_5)`. By (2), for `c < r`: `lambda(c) + X_{m_2}(c) = s` (row `c`),
`lambda(c) + X_{m_1}(c) + X_e(c - x5) = s` (column `c`),
`lambda(c) + X_{m_3}(c) + X_{e'}(c - x') = s` (column `s - 1 - c`), with
`s = L + r`, `x' = r - x5`. So `m_1 ≠ m_2`, `m_3 ≠ m_2`, `m_1 = m_3`; then the
columns `c` and `s - 1 - c` hold the same number of cells of the corner tiles,
so `x5 = x'` and `X_A = X_C`, against the first two equations at `c = x5`.
Line-count arguments (`Frame5.col_sum`, `Frame5.row_sum`). -/
theorem n62_low (F : FrameN P p q a b t o x5 y5) (S : AdjFull P p q)
    (h0 : (o 0).swap = false) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) (h4 : (o 4).swap = false) (h4y : (o 4).negY = false) :
    False := by
  have F5 := F.toFrame5
  obtain ⟨hrC, ha, hb⟩ := n62_r F S h0 h1 h2 h3
  obtain ⟨hr2, hrp, hy5r, hy5p, hqp⟩ := n62_low_dims F S h0 h1 h2 h3 h4 h4y
  have m0 := S.mark F5 (i := 0) (by decide)
  have m1 := S.mark F5 (i := 1) (by decide)
  have m2 := S.mark F5 (i := 2) (by decide)
  have m3 := S.mark F5 (i := 3) (by decide)
  have hx5 := F.x5_pos
  have hx5' := F.x5_le
  have hW4 : (o 4).W p q = p := by simp [Orient.W, h4]
  rw [hW4] at hx5'
  have hW0 : (o 0).W p q = p := by simp [Orient.W, h0]
  have hW1 : (o 1).W p q = q := by simp [Orient.W, h1]
  have hW2 : (o 2).W p q = p := by simp [Orient.W, h2]
  have hW3 : (o 3).W p q = q := by simp [Orient.W, h3]
  have hH2 : (o 2).H p q = q := by simp [Orient.H, h2]
  have hH3 : (o 3).H p q = p := by simp [Orient.H, h3]
  have hH4 : (o 4).H p q = q := by simp [Orient.H, h4]
  -- `X_{m_i}`, `X_e` and `lambda`, read off the codes
  have hX0 : ∀ c, (o 0).colLine p q P c = colCount P (if (o 0).negX then p - 1 - c else c) := by
    intro c; simp [Orient.colLine, h0]
  have hX1 : ∀ c, (o 1).rowLine p q P c = colCount P (if (o 1).negX then p - 1 - c else c) := by
    intro c; simp [Orient.rowLine, h1]
  have hX2 : ∀ c, (o 2).colLine p q P c = colCount P (if (o 2).negX then p - 1 - c else c) := by
    intro c; simp [Orient.colLine, h2]
  have hX4 : ∀ c, (o 4).colLine p q P c = colCount P (if (o 4).negX then p - 1 - c else c) := by
    intro c; simp [Orient.colLine, h4]
  have hl0 : ∀ c, (o 0).rowLine p q P c = rowCount P c := by
    intro c; simp [Orient.rowLine, h0, m0]
  have hl1 : ∀ c, (o 1).colLine p q P c = rowCount P c := by
    intro c; simp [Orient.colLine, h1, m1]
  have hl3 : ∀ c, (o 3).colLine p q P c = rowCount P c := by
    intro c; simp [Orient.colLine, h3, m3]
  -- (2) at the lines at distance `c < r` from a side of `R`: row `c` from the bottom
  have hrow : ∀ c, 0 ≤ c → c < colCount P 0 → rowCount P c + (o 1).rowLine p q P c = a := by
    intro c hc0 hc1
    have h := F5.row_sum (y := c) hc0 (by omega)
    have z2 := F5.rowLine_zero (o 2) (y := b - 1 - c) (by omega)
    have z3 := F5.rowLine_zero (o 3) (y := b - 1 - c) (by omega)
    have z4 := F5.rowLine_zero (o 4) (y := c - y5) (by omega)
    have e := hl0 c
    omega
  -- column `c` from the left
  have hcolL : ∀ c, 0 ≤ c → c < colCount P 0 →
      (o 0).colLine p q P c + rowCount P c + (o 4).colLine p q P (c - x5) = b := by
    intro c hc0 hc1
    have h := F5.col_sum (x := c) hc0 (by omega)
    have z1 := F5.colLine_zero (o 1) (x := a - 1 - c) (by omega)
    have z2 := F5.colLine_zero (o 2) (x := a - 1 - c) (by omega)
    have e := hl3 c
    omega
  -- column `c` from the right
  have hcolR : ∀ c, 0 ≤ c → c < colCount P 0 →
      rowCount P c + (o 2).colLine p q P c + (o 4).colLine p q P (a - 1 - c - x5) = b := by
    intro c hc0 hc1
    have h := F5.col_sum (x := a - 1 - c) (by omega) (by omega)
    rw [show a - 1 - (a - 1 - c) = c by omega] at h
    have z0 := F5.colLine_zero (o 0) (x := a - 1 - c) (by omega)
    have z3 := F5.colLine_zero (o 3) (x := a - 1 - c) (by omega)
    have e := hl1 c
    omega
  -- `T_5` meets exactly the columns `[x5, x5 + L)`
  have hpos : ∀ u, 0 ≤ u → u < p → 1 ≤ (o 4).colLine p q P u :=
    fun u h h' => F5.colLine_pos (o 4) h (by omega)
  have hzero : ∀ u, u < 0 ∨ p ≤ u → (o 4).colLine p q P u = 0 :=
    fun u h => F5.colLine_zero (o 4) (by omega)
  -- `m_1 ≠ m_2` (at `c = x5`) and `m_3 ≠ m_2` (at `c = x'`), so `m_1 = m_3`
  have n01 : (o 0).negX ≠ (o 1).negX := by
    intro e
    have k1 := hrow x5 (by omega) (by omega)
    have k2 := hcolL x5 (by omega) (by omega)
    have kp := hpos (x5 - x5) (by omega) (by omega)
    rw [hX0, e] at k2
    rw [hX1] at k1
    omega
  have n21 : (o 2).negX ≠ (o 1).negX := by
    intro e
    have k1 := hrow (colCount P 0 - x5) (by omega) (by omega)
    have k2 := hcolR (colCount P 0 - x5) (by omega) (by omega)
    have kp := hpos (a - 1 - (colCount P 0 - x5) - x5) (by omega) (by omega)
    rw [hX2, e] at k2
    rw [hX1] at k1
    omega
  have e02 : o 0 = o 2 :=
    Orient.ext (h0.trans h2.symm) (bool_eq_of_ne n01 n21) (m0.trans m2.symm)
  have e13 : ∀ y, (o 1).colLine p q P y = (o 3).colLine p q P y := fun y => by rw [hl1, hl3]
  -- the columns `x` and `s - 1 - x` hold the same number of cells of `T_1, ..., T_4`,
  -- so by (2) of `T_5`
  have hsym : ∀ x, 0 ≤ x → x < a →
      (o 4).colLine p q P (x - x5) = (o 4).colLine p q P (a - 1 - x - x5) := by
    intro x hx0 hx1
    have h := F5.col_sum hx0 hx1
    have h' := F5.col_sum (x := a - 1 - x) (by omega) (by omega)
    rw [show a - 1 - (a - 1 - x) = x by omega] at h'
    rw [← e02] at h h'
    simp only [e13] at h h'
    omega
  -- the columns of `T_5` are `[x5, x5 + L)`: `x5 = x'`, that is `r = 2 x5`
  have hr5 : colCount P 0 = 2 * x5 := by
    have k1 := hsym (x5 - 1) (by omega) (by omega)
    rw [hzero (x5 - 1 - x5) (by omega)] at k1
    have k2 := hsym x5 (by omega) (by omega)
    have kp := hpos (x5 - x5) (by omega) (by omega)
    rcases (by omega : colCount P 0 < 2 * x5 ∨ colCount P 0 = 2 * x5 ∨
        2 * x5 < colCount P 0) with hlt | heq | hlt
    · have := hpos (a - 1 - (x5 - 1) - x5) (by omega) (by omega)
      omega
    · exact heq
    · rw [hzero (a - 1 - x5 - x5) (by omega)] at k2
      omega
  -- `X_A = X_C` at `x5`
  have hAC : colCount P x5 = colCount P (p - 1 - x5) := by
    have k := hsym (colCount P 0) (by omega) (by omega)
    rw [hX4, hX4] at k
    have e1 : colCount P 0 - x5 = x5 := by omega
    have e2 : a - 1 - colCount P 0 - x5 = p - 1 - x5 := by omega
    rw [e1, e2] at k
    cases hn : (o 4).negX <;> simp only [hn, Bool.false_eq_true, ↓reduceIte] at k
    · exact k
    · rw [show p - 1 - (p - 1 - x5) = x5 by omega] at k
      exact k.symm
  -- the first two equations at `c = x5`: `X_{m_2}(x5) - X_{m_1}(x5) = X_e(0) ≥ 1`
  have k1 := hrow x5 (by omega) (by omega)
  have k2 := hcolL x5 (by omega) (by omega)
  have kp := hpos (x5 - x5) (by omega) (by omega)
  rw [hX1] at k1
  rw [hX0] at k2
  cases hn0 : (o 0).negX <;> cases hn1 : (o 1).negX <;>
    simp only [hn0, hn1, Bool.false_eq_true, ↓reduceIte] at k1 k2 <;> omega

/-- `report-A2.md`, 6.2: "By a half turn of R let it be the lowest." -/
theorem n62_wide (F : FrameN P p q a b t o x5 y5) (S : AdjFull P p q)
    (h0 : (o 0).swap = false) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) (h4 : (o 4).swap = false) : False := by
  cases hy : (o 4).negY
  · exact n62_low F S h0 h1 h2 h3 h4 hy
  · obtain ⟨t', F'⟩ := F.halfTurn
    exact n62_low F' S (by simpa using h2) (by simpa using h3) (by simpa using h0)
      (by simpa using h1) (by simpa using h4) (by simp [hy])

/-- `report-A2.md`, 6.2: "The frame is invariant under a quarter turn; let F of
T_5 be horizontal." -/
theorem n62_alt (F : FrameN P p q a b t o x5 y5) (S : AdjFull P p q)
    (h0 : (o 0).swap = false) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) : False := by
  cases h4 : (o 4).swap
  · exact n62_wide F S h0 h1 h2 h3 h4
  · obtain ⟨t', F'⟩ := F.transpose
    obtain ⟨t'', F''⟩ := F'.flipX
    exact n62_wide F'' S (by simpa using h3) (by simpa using h0) (by simpa using h1)
      (by simpa using h2) (by simp [h4])

/-- **`report-A2.md`, 6.2.** Pattern N with two adjacent occupied corners does
not occur ("reflect R so that F is on the bottom for T_1, right for T_2, top for
T_3, left for T_4"). -/
theorem adj_N (F : FrameN P p q a b t o x5 y5) (S : Adjacent P p q) : False := by
  have S' := S.full F.toFrame5
  rcases n62_types F S' with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩
  · exact n62_alt F S' h0 h1 h2 h3
  · obtain ⟨t', F'⟩ := F.flipX
    exact n62_alt F' S' (by simpa using h1) (by simpa using h0) (by simpa using h3)
      (by simpa using h2)

end PolyominoOddOrder
