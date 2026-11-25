module

public import PolyominoOddOrder.AllEqual

/-!
# Case (I), four occupied corners (`FourCorners.lean`)

Blueprint unit C1 (third increment), with `AllEqual.lean`. `report-A2.md`,
section 4: `|S| = 4` does not occur, in pattern O (4.1) and in pattern N (4.2).
Both entry statements assume `q ≤ p` (the closure file exchanges the axes of
`box(P)` otherwise).

By (Full) both runs of every mark are whole sides (`four_runs`), so the side
equations (1) are equations between the widths `W_i` alone.

Entry statements (binding): `four_O`, `four_N`. A proof unit may reshape the
nodes marked PROVISIONAL.

Source: `theoretician/report-A2.md` (goals lab, commit `076d663`), section 4.
-/

@[expose] public section

namespace PolyominoOddOrder

open Orient (cornerP)

variable {P : Finset Cell} {p q a b : ℤ} {t : Fin 5 → Finset Cell} {o : Fin 5 → Orient}
  {x5 y5 : ℤ}

/-- `report-A2.md`, section 4, first sentence: by (Full) both runs of every mark
are whole sides, `u_i = W_i` and `v_i = H_i`. -/
theorem four_runs (F : Frame5 P p q a b t o x5 y5) (S : Four P p q) {i : Fin 5} (hi : i ≠ 4) :
    (o i).rowLine p q P 0 = (o i).W p q ∧ (o i).colLine p q P 0 = (o i).H p q :=
  ⟨F.hrun_of_far hi (S.corner_mem _ _), F.vrun_of_far hi (S.corner_mem _ _)⟩

/-- With four occupied corners the row of `box(P)` at a mark is full. -/
theorem mark_row_full (F : Frame5 P p q a b t o x5 y5) (S : Four P p q) {i : Fin 5}
    (hi : i ≠ 4) : rowCount P (if (o i).negY then q - 1 else 0) = p := by
  obtain ⟨hu, hv⟩ := four_runs F S hi
  rw [Orient.hrun_eq] at hu
  rw [Orient.vrun_eq] at hv
  cases hs : (o i).swap <;> simp [hs, Orient.W, Orient.H] at hu hv <;> assumption

/-- With four occupied corners the column of `box(P)` at a mark is full. -/
theorem mark_col_full (F : Frame5 P p q a b t o x5 y5) (S : Four P p q) {i : Fin 5}
    (hi : i ≠ 4) : colCount P (if (o i).negX then p - 1 else 0) = q := by
  obtain ⟨hu, hv⟩ := four_runs F S hi
  rw [Orient.hrun_eq] at hu
  rw [Orient.vrun_eq] at hv
  cases hs : (o i).swap <;> simp [hs, Orient.W, Orient.H] at hu hv <;> assumption

/-! ## 4.1 Pattern O -/

/-- `report-A2.md`, 4.1, the count: by (1) `W_3 + W_4 > W_1 + W_2` and
`W_3 - W_1 = W_4 - W_2`, so `W_3 = W_4 = p`, `W_1 = W_2 = q`, `p > q`, `a = 2p`,
`b = p + q`. -/
theorem o41_dims (F : FrameO P p q a b t o x5 y5) (S : Four P p q) (hpq : q ≤ p) :
    q < p ∧ (o 0).swap = true ∧ (o 1).swap = true ∧ (o 2).swap = false ∧
      (o 3).swap = false ∧ a = 2 * p ∧ b = p + q := by
  have hb := F.side_bottom
  have ht := F.side_top
  have hl := F.side_left
  have hr := F.side_right
  have hmu := F.mu_pos
  rw [(four_runs F.toFrame5 S (i := 0) (by decide)).1,
    (four_runs F.toFrame5 S (i := 1) (by decide)).1] at hb
  rw [(four_runs F.toFrame5 S (i := 2) (by decide)).1,
    (four_runs F.toFrame5 S (i := 3) (by decide)).1] at ht
  rw [(four_runs F.toFrame5 S (i := 0) (by decide)).2,
    (four_runs F.toFrame5 S (i := 3) (by decide)).2] at hl
  rw [(four_runs F.toFrame5 S (i := 1) (by decide)).2,
    (four_runs F.toFrame5 S (i := 2) (by decide)).2] at hr
  simp only [Orient.W, Orient.H] at hb ht hl hr
  cases h0 : (o 0).swap <;> cases h1 : (o 1).swap <;> cases h2 : (o 2).swap <;>
    cases h3 : (o 3).swap <;> simp [h0, h1, h2, h3] at hb ht hl hr ⊢ <;> omega

/-- **`report-A2.md`, 4.1.** Pattern O with four occupied corners does not occur.
After `o41_dims`: `H_1 = H_2 = p` and `H_5 ≤ p`, so the rows `[p, p + q)` lie in
`T_3` and `T_4`; their boxes `[p, 2p) x [p, p + q)` and `[0, p) x [p, p + q)` are
disjoint, so `T_3` fills its box, against `Frame5.exists_hole`. A cell argument:
take the hole of `T_3`, `Frame5.cover_cases`, `omega`. -/
theorem four_O (F : FrameO P p q a b t o x5 y5) (S : Four P p q) (hpq : q ≤ p) : False := by
  obtain ⟨-, h0, h1, h2, h3, ha, hb⟩ := o41_dims F S hpq
  have F5 := F.toFrame5
  have hy5 := F.y5_eq
  have hH0 : (o 0).H p q = p := by simp [Orient.H, h0]
  have hH1 : (o 1).H p q = p := by simp [Orient.H, h1]
  have hW2 : (o 2).W p q = p := by simp [Orient.W, h2]
  have hH2 : (o 2).H p q = q := by simp [Orient.H, h2]
  have hW3 : (o 3).W p q = p := by simp [Orient.W, h3]
  have hH4 : (o 4).H p q ≤ p := by
    unfold Orient.H
    split <;> omega
  -- the hole of `T_3` in its box `[p, 2p) x [p, p + q)` lies in no tile
  obtain ⟨l, ⟨⟨hl1, hl2⟩, hl3, hl4⟩, hlP⟩ := F5.exists_hole (o 2)
  have hc2 : ((a - 1 - l.1, b - 1 - l.2) : Cell) ∉ t 2 := by
    rw [F5.mem2]
    simpa using hlP
  have hcR : ((a - 1 - l.1, b - 1 - l.2) : Cell) ∈ R a b :=
    mem_R.2 ⟨⟨by simp only; omega, by simp only; omega⟩, by simp only; omega, by simp only; omega⟩
  rcases F5.cover_cases hcR with h | h | h | h | h
  · obtain ⟨-, -, h'⟩ := h
    simp only at h'
    omega
  · obtain ⟨-, -, h'⟩ := h
    simp only at h'
    omega
  · exact hc2 h.1
  · obtain ⟨-, h', -⟩ := h
    simp only at h'
    omega
  · obtain ⟨-, -, -, h'⟩ := h
    simp only at h'
    omega

/-! ## 4.2 Pattern N -/

/-- `report-A2.md`, 4.2, first sentence: by (1) `W_1 = W_3` and `W_2 = W_4`. -/
theorem n42_swaps (F : FrameN P p q a b t o x5 y5) (S : Four P p q) :
    (o 0).W p q = (o 2).W p q ∧ (o 1).W p q = (o 3).W p q := by
  have hb := F.side_bottom
  have ht := F.side_top
  have hl := F.side_left
  have hr := F.side_right
  rw [(four_runs F.toFrame5 S (i := 0) (by decide)).1,
    (four_runs F.toFrame5 S (i := 1) (by decide)).1] at hb
  rw [(four_runs F.toFrame5 S (i := 2) (by decide)).1,
    (four_runs F.toFrame5 S (i := 3) (by decide)).1] at ht
  rw [(four_runs F.toFrame5 S (i := 0) (by decide)).2,
    (four_runs F.toFrame5 S (i := 3) (by decide)).2] at hl
  rw [(four_runs F.toFrame5 S (i := 1) (by decide)).2,
    (four_runs F.toFrame5 S (i := 2) (by decide)).2] at hr
  have e0 := (o 0).W_add_H p q
  have e1 := (o 1).W_add_H p q
  have e2 := (o 2).W_add_H p q
  have e3 := (o 3).W_add_H p q
  omega

/-- `report-A2.md`, 4.2, "W_1 = W_2", the crossing in the quadrant `Q_1`: a
connected part of `T_5` inside `box(T_1) = [0, W) x [0, H)` with a cell in the
right column and a cell in the top row of that box does not exist, because
`T_1` joins `(0, 0)` to `(W - 1, H - 1)` inside the same box (`interlace`).
PROVISIONAL: a leaf of `n42_quadrants`; the unit chooses how the part of the
path is given. -/
theorem n42_quad_Q1 (F : FrameN P p q a b t o x5 y5) (S : Four P p q) (C : Finset Cell)
    (hC : EdgeConnected C) (hsub : C ⊆ t 4)
    (hbox : ∀ c ∈ C, c.1 < (o 0).W p q ∧ c.2 < (o 0).H p q) {x y : ℤ}
    (h1 : (((o 0).W p q - 1, y) : Cell) ∈ C) (h2 : ((x, (o 0).H p q - 1) : Cell) ∈ C) :
    False := by
  have G := F.toFrame5
  have c0 : ((0, 0) : Cell) ∈ t 0 := G.corner0
  have c1 : (((o 0).W p q - 1, (o 0).H p q - 1) : Cell) ∈ t 0 := by
    rw [G.mem0, Orient.back_WH]
    exact S.corner_mem _ _
  have hW2 : 2 ≤ (o 0).W p q := by
    have := G.two_le_p; have := G.two_le_q; unfold Orient.W; split <;> omega
  have hH2 : 2 ≤ (o 0).H p q := by
    have := G.two_le_p; have := G.two_le_q; unfold Orient.H; split <;> omega
  have hT : t 0 ⊆ R ((o 0).W p q) ((o 0).H p q) := fun c hc => by
    have := G.box0 hc
    exact mem_R.2 ⟨this.1, this.2⟩
  have hCR : C ⊆ R ((o 0).W p q) ((o 0).H p q) := fun c hc => by
    have h4 := mem_R.1 (G.sub_R 4 (hsub hc))
    have hb := hbox c hc
    exact mem_R.2 ⟨⟨h4.1.1, hb.1⟩, h4.2.1, hb.2⟩
  have hd : Disjoint (t 0) C :=
    Finset.disjoint_of_subset_right hsub (G.tiling.disjoint 0 4 (by decide))
  have r1 := mem_R.1 (hCR h1)
  have r2 := mem_R.1 (hCR h2)
  simp only at r1 r2
  have hy : y ≠ (o 0).H p q - 1 := by
    rintro rfl
    exact Finset.disjoint_left.1 hd c1 h1
  have hx : x ≠ (o 0).W p q - 1 := by
    rintro rfl
    exact Finset.disjoint_left.1 hd c1 h2
  -- the four cells in the order of `bpos`: `(0, 0)`, the right column, the
  -- opposite corner, the top row
  have hm := interlace hW2 hH2 hT (G.conn 0) hCR hC
    (p := (0, 0)) (q := ((o 0).W p q - 1, y)) (p' := ((o 0).W p q - 1, (o 0).H p q - 1))
    (q' := (x, (o 0).H p q - 1))
    ⟨hT c0, Or.inl rfl⟩ ⟨hCR h1, Or.inr (Or.inl rfl)⟩ ⟨hT c1, Or.inr (Or.inl rfl)⟩
    ⟨hCR h2, Or.inr (Or.inr (Or.inr rfl))⟩ c0 c1 h1 h2
    (by rw [bpos_bottom, bpos_right]; omega)
    (by rw [bpos_right, bpos_right]; omega)
    (by rw [bpos_right, bpos_top hH2]; omega)
  exact hm.not_disjoint hd

/-- A connected set `K` with a cell `u` in a region `Q` and a cell outside it:
the component `L` of `u` in `K ∩ Q` has a cell next to a cell of `K` outside
`Q`. The step "between its last cell in Q_2 ... and that first cell in Q_4 it
stays in Q_1 or stays in Q_3" of `report-A2.md`, 4.2. -/
private theorem q4_exit {K : Finset Cell} (hK : EdgeConnected K) (Q : Cell → Prop)
    {u c : Cell} (hu : u ∈ K) (hQu : Q u) (hc : c ∈ K) (hQc : ¬ Q c) :
    ∃ L : Finset Cell, EdgeConnected L ∧ u ∈ L ∧ (∀ z ∈ L, z ∈ K ∧ Q z) ∧
      ∃ u' v' : Cell, u' ∈ L ∧ v' ∈ K ∧ Adj u' v' ∧ ¬ Q v' := by
  classical
  have hsub : ∀ z ∈ component (K.filter Q) u, z ∈ K ∧ Q z := fun z hz =>
    Finset.mem_filter.1 (mem_component.1 hz).1
  have huL : u ∈ component (K.filter Q) u :=
    mem_component.2 ⟨Finset.mem_filter.2 ⟨hu, hQu⟩, Reach.refl _ _⟩
  have hcL : c ∉ component (K.filter Q) u := fun h => hQc (hsub c h).2
  obtain ⟨u', v', -, hv', huv, hu'L, hv'L⟩ :=
    hK.exists_adj_leaving (fun z => z ∈ component (K.filter Q) u) hu hc huL hcL
  exact ⟨_, edgeConnected_component _ _, huL, hsub, u', v', hu'L, hv', huv,
    fun hQ => hv'L (component_closed hu'L (Finset.mem_filter.2 ⟨hv', hQ⟩) huv)⟩

/-- `report-A2.md`, 4.2, "W_1 = W_2": "Q_3 is the same after a half turn of R".
The crossing in `box(T_3) = [a - W_3, a) x [b - H_3, b)`, from the left column
to the bottom row of that box, is the crossing in `Q_1` of the half-turned frame
(`FrameN.halfTurn`; its `T_5` is the image of `T_5`, by `Frame5.mem4`). -/
private theorem q4_quad_Q3 (F : FrameN P p q a b t o x5 y5) (S : Four P p q) (C : Finset Cell)
    (hC : EdgeConnected C) (hsub : C ⊆ t 4)
    (hbox : ∀ c ∈ C, a - (o 2).W p q ≤ c.1 ∧ b - (o 2).H p q ≤ c.2) {x y : ℤ}
    (h1 : ((a - (o 2).W p q, y) : Cell) ∈ C) (h2 : ((x, b - (o 2).H p q) : Cell) ∈ C) :
    False := by
  obtain ⟨t', F'⟩ := F.halfTurn
  have G := F.toFrame5
  refine n42_quad_Q1 F' S (C.image (GridIso.halfTurn a b).apply)
    (GridIso.edgeConnected_image _ hC) ?_ ?_ (x := a - 1 - x) (y := b - 1 - y) ?_ ?_
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hc
    have hd4 := (G.mem4 d).1 (hsub hd)
    rw [F'.toFrame5.mem4]
    simp only [GridIso.halfTurn_apply, Matrix.cons_val, Orient.back_turn]
    convert hd4 using 2
    ext <;> simp <;> ring
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hc
    have := hbox d hd
    simp only [GridIso.halfTurn_apply, Matrix.cons_val]
    omega
  · refine Finset.mem_image.2 ⟨_, h1, ?_⟩
    simp only [GridIso.halfTurn_apply, Matrix.cons_val, Prod.mk.injEq, and_true]
    omega
  · refine Finset.mem_image.2 ⟨_, h2, ?_⟩
    simp only [GridIso.halfTurn_apply, Matrix.cons_val, Prod.mk.injEq, true_and]
    omega

/-- `report-A2.md`, 4.2, "W_1 = W_2": the four boxes are the quadrants of
`R a b`; `T_5` is the union of the sets `Q_i \ T_i` and meets `Q_2` and `Q_4`; a
path in `T_5` from `Q_2` to `Q_4` has a part that stays in `Q_1` or in `Q_3` and
runs from the side next to `Q_2` to the side next to `Q_4`; in `Q_1` this is
against `n42_quad_Q1`, and `Q_3` is `Q_1` after a half turn of `R a b`
(`FrameN.halfTurn`; the tiles of the turned frame are the images of the old
ones, by `Frame5.mem`). -/
theorem n42_quadrants (F : FrameN P p q a b t o x5 y5) (S : Four P p q)
    (h : (o 0).W p q = (o 1).W p q) : False := by
  classical
  have G := F.toFrame5
  obtain ⟨h02, h13⟩ := n42_swaps F S
  have e0 := (o 0).W_add_H p q
  have e1 := (o 1).W_add_H p q
  have e2 := (o 2).W_add_H p q
  have e3 := (o 3).W_add_H p q
  -- `a = 2 W`, `b = 2 H`: the boxes are the quadrants of `R a b`
  have ha : a = 2 * (o 0).W p q := by
    have hb := F.side_bottom
    rw [(four_runs G S (i := 0) (by decide)).1, (four_runs G S (i := 1) (by decide)).1] at hb
    omega
  have hb : b = 2 * (o 0).H p q := by
    have hl := F.side_left
    rw [(four_runs G S (i := 0) (by decide)).2, (four_runs G S (i := 3) (by decide)).2] at hl
    omega
  -- `T_5` meets `Q_2` and `Q_4`: a hole of `T_2`, of `T_4`
  have hQ2 : ∃ c ∈ t 4, (o 0).W p q ≤ c.1 ∧ c.2 < (o 0).H p q := by
    obtain ⟨⟨l1, l2⟩, hl, hlP⟩ := G.exists_hole (o 1)
    simp only at hl
    have hR : ((a - 1 - l1, l2) : Cell) ∈ R a b := mem_R.2 (by simp only; omega)
    refine ⟨(a - 1 - l1, l2), ?_, show (o 0).W p q ≤ a - 1 - l1 by omega,
      show l2 < (o 0).H p q by omega⟩
    rcases G.cover_cases hR with ⟨-, h', -⟩ | ⟨h', -⟩ | ⟨-, -, h'⟩ | ⟨-, h', -⟩ | ⟨h', -⟩
    · simp only at h'; omega
    · simp only [G.mem1, sub_sub_cancel] at h'
      exact absurd h' hlP
    · simp only at h'; omega
    · simp only at h'; omega
    · exact h'
  have hQ4 : ∃ c ∈ t 4, c.1 < (o 0).W p q ∧ (o 0).H p q ≤ c.2 := by
    obtain ⟨⟨l1, l2⟩, hl, hlP⟩ := G.exists_hole (o 3)
    simp only at hl
    have hR : ((l1, b - 1 - l2) : Cell) ∈ R a b := mem_R.2 (by simp only; omega)
    refine ⟨(l1, b - 1 - l2), ?_, show l1 < (o 0).W p q by omega,
      show (o 0).H p q ≤ b - 1 - l2 by omega⟩
    rcases G.cover_cases hR with ⟨-, -, h'⟩ | ⟨-, h', -⟩ | ⟨-, h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩
    · simp only at h'; omega
    · simp only at h'; omega
    · simp only at h'; omega
    · simp only [G.mem3, sub_sub_cancel] at h'
      exact absurd h' hlP
    · exact h'
  obtain ⟨c2, hc2, hc2x, hc2y⟩ := hQ2
  obtain ⟨c4, hc4, hc4x, hc4y⟩ := hQ4
  -- the component `K` of `c2` in `T_5` minus `Q_4` is left from `Q_1` or `Q_3`
  obtain ⟨K, hKc, hc2K, hKsub, u, v, huK, -, huv, hvQ⟩ := q4_exit (G.conn 4)
    (fun c => ¬ (c.1 < (o 0).W p q ∧ (o 0).H p q ≤ c.2)) hc2 (by omega) hc4 (by simp; omega)
  have huQ := (hKsub u huK).2
  simp only [not_not] at hvQ huQ
  have hcase : (u.1 < (o 0).W p q ∧ u.2 = (o 0).H p q - 1) ∨
      (u.1 = (o 0).W p q ∧ (o 0).H p q ≤ u.2) := by
    unfold Adj at huv
    omega
  rcases hcase with ⟨hu1, hu2⟩ | ⟨hu1, hu2⟩
  · -- in `Q_1`: the component of `u` in `K ∩ Q_1` reaches the right column of `Q_1`
    obtain ⟨L, hLc, huL, hLsub, u', v', hu'L, hv'K, huv', hv'Q⟩ := q4_exit hKc
      (fun c => c.1 < (o 0).W p q ∧ c.2 < (o 0).H p q) huK ⟨hu1, by omega⟩ hc2K (by omega)
    have hu'Q := (hLsub u' hu'L).2
    have hv'Q4 := (hKsub v' hv'K).2
    have hu'x : u'.1 = (o 0).W p q - 1 := by
      unfold Adj at huv'
      omega
    refine n42_quad_Q1 F S L hLc (fun z hz => (hKsub z (hLsub z hz).1).1)
      (fun z hz => (hLsub z hz).2) (y := u'.2) (x := u.1) ?_ ?_
    · rw [← hu'x]
      exact hu'L
    · rw [← hu2]
      exact huL
  · -- in `Q_3`: the component of `u` in `K ∩ Q_3` reaches the bottom row of `Q_3`
    obtain ⟨L, hLc, huL, hLsub, u', v', hu'L, hv'K, huv', hv'Q⟩ := q4_exit hKc
      (fun c => (o 0).W p q ≤ c.1 ∧ (o 0).H p q ≤ c.2) huK ⟨by omega, hu2⟩ hc2K (by omega)
    have hu'Q := (hLsub u' hu'L).2
    have hv'Q4 := (hKsub v' hv'K).2
    have hu'y : u'.2 = (o 0).H p q := by
      unfold Adj at huv'
      omega
    refine q4_quad_Q3 F S L hLc (fun z hz => (hKsub z (hLsub z hz).1).1) (fun z hz => by
        have := (hLsub z hz).2
        omega)
      (y := u.2) (x := u'.1) ?_ ?_
    · have e : a - (o 2).W p q = u.1 := by omega
      rw [e]
      exact huL
    · have e : b - (o 2).H p q = u'.2 := by omega
      rw [e]
      exact hu'L

/-- `report-A2.md`, 4.2, "W_1 not W_2": if all marks are equal, the quarter turn
of `R a b` permutes `T_1, ..., T_4`, so `p = q` by (T4). So two different
corners are used. -/
theorem n42_alt_marks (F : FrameN P p q a b t o x5 y5) (hq : q < p)
    (h0 : (o 0).swap = false) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) : ¬ SameMarks o := by
  intro hm
  have e2 : o 2 = o 0 := hm.eq_of_swap (by decide) (by decide) (h2.trans h0.symm)
  have e3 : o 3 = o 1 := hm.eq_of_swap (by decide) (by decide) (h3.trans h1.symm)
  have e1 : o 1 = (o 0).tr := by
    obtain ⟨hx, hy⟩ := hm 1 (by decide)
    apply Orient.ext
    · simp [h0, h1]
    · simpa using hx
    · simpa using hy
  have hab : a = b := by
    have hb := F.side_bottom
    have hl := F.side_left
    rw [e1, Orient.rowLine_tr] at hb
    rw [e3, e1, Orient.colLine_tr] at hl
    omega
  obtain ⟨hpq, -⟩ := F.toFrame5.T4_quarter hab e1 e2 e3
  omega

/-- `report-A2.md`, 4.2: "So two different corners are used, and at least three
sides of box(P) are full." With `|S| = 4` the row and the column of `box(P)` at
each mark are full (`mark_row_full`, `mark_col_full`); two different marks give
both rows, or both columns and one row. -/
theorem n42_three_full (F : Frame5 P p q a b t o x5 y5) (S : Four P p q)
    (hns : ¬ SameMarks o) :
    (rowCount P 0 = p ∧ rowCount P (q - 1) = p) ∨
      (colCount P 0 = q ∧ colCount P (p - 1) = q ∧
        (rowCount P 0 = p ∨ rowCount P (q - 1) = p)) := by
  obtain ⟨i, hi, hne⟩ : ∃ i : Fin 5, i ≠ 4 ∧
      ¬ ((o i).negX = (o 0).negX ∧ (o i).negY = (o 0).negY) := by
    by_contra hcon
    exact hns fun i hi => by_contra fun h => hcon ⟨i, hi, h⟩
  have r0 := mark_row_full F S (i := 0) (by decide)
  have c0 := mark_col_full F S (i := 0) (by decide)
  have ri := mark_row_full F S hi
  have ci := mark_col_full F S hi
  revert r0 c0 ri ci hne
  cases (o 0).negX <;> cases (o 0).negY <;> cases (o i).negX <;> cases (o i).negY <;>
    simp <;> tauto

/-- `report-A2.md`, 4.2, "W_1 not W_2": with `T_1`, `T_3` wide and `T_2`, `T_4`
tall, (1) gives `a = b = p + q`. -/
private theorem f4_alt_ab (F : FrameN P p q a b t o x5 y5) (S : Four P p q)
    (h0 : (o 0).swap = false) (h1 : (o 1).swap = true) (h3 : (o 3).swap = true) :
    a = p + q ∧ b = p + q := by
  have hb := F.side_bottom
  have hl := F.side_left
  rw [(four_runs F.toFrame5 S (i := 0) (by decide)).1,
    (four_runs F.toFrame5 S (i := 1) (by decide)).1] at hb
  rw [(four_runs F.toFrame5 S (i := 0) (by decide)).2,
    (four_runs F.toFrame5 S (i := 3) (by decide)).2] at hl
  simp [Orient.W, Orient.H, h0, h1, h3] at hb hl
  omega

/-- `report-A2.md`, 4.2, the first two bullets ("All four full", "Exactly one
side not full, a short one"): both long sides of `box(P)` are full. Then `T_1`
(wide, box `[0, p) x [0, q)`) contains the rows `0` and `q - 1` of its box and
its left column; `T_5` has a cell in that box (a hole of `T_1`; the four boxes
are disjoint) and a cell outside (the square `[q, p) x [q, p)`), so it leaves
the box from column `p - 1` to column `p`; but column `p`, rows `[0, q)`, is a
long side of `T_2` and lies in `T_2`. Uses `EdgeConnected.exists_adj_leaving`. -/
theorem n42_alt_long (F : FrameN P p q a b t o x5 y5) (S : Four P p q) (hq : q < p)
    (h0 : (o 0).swap = false) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) (hB : rowCount P 0 = p) (hT : rowCount P (q - 1) = p) :
    False := by
  have F5 := F.toFrame5
  obtain ⟨ha, hb⟩ := f4_alt_ab F S h0 h1 h3
  have hW0 : (o 0).W p q = p := by simp [Orient.W, h0]
  have hH0 : (o 0).H p q = q := by simp [Orient.H, h0]
  have hW1 : (o 1).W p q = q := by simp [Orient.W, h1]
  have hH2 : (o 2).H p q = q := by simp [Orient.H, h2]
  have hW3 : (o 3).W p q = q := by simp [Orient.W, h3]
  have hH3 : (o 3).H p q = p := by simp [Orient.H, h3]
  have hq2 := F5.two_le_q
  have hB' := (F5.rowCount_eq_iff 0).1 hB
  have hT' := (F5.rowCount_eq_iff (q - 1)).1 hT
  -- the row `q - 1` of `box(T_1)` lies in `T_1`
  have top0 : ∀ x : ℤ, 0 ≤ x → x < p → ((x, q - 1) : Cell) ∈ t 0 := by
    intro x hx0 hx1
    rw [F5.mem0]
    cases hx : (o 0).negX <;> cases hy : (o 0).negY <;> simp [Orient.back, h0, hx, hy] <;>
      first
      | exact hB' _ (by omega) (by omega)
      | exact hT' _ (by omega) (by omega)
  -- the column `p`, rows `[0, p)`, is the far long side of `T_2`
  have col1 : ∀ y : ℤ, 0 ≤ y → y < p → ((p, y) : Cell) ∈ t 1 := by
    intro y hy0 hy1
    rw [F5.mem1]
    show (o 1).back p q (a - 1 - p, y) ∈ P
    rw [show a - 1 - p = q - 1 by omega]
    cases hx : (o 1).negX <;> cases hy : (o 1).negY <;> simp [Orient.back, h1, hx, hy] <;>
      first
      | exact hB' _ (by omega) (by omega)
      | exact hT' _ (by omega) (by omega)
  -- a hole of `T_1` lies in `T_5`
  obtain ⟨l, ⟨⟨hl1, hl2⟩, hl3, hl4⟩, hlP⟩ := F5.exists_hole (o 0)
  have hl0 : l ∉ t 0 := by
    rw [F5.mem0]
    exact hlP
  have hlR : l ∈ R a b := mem_R.2 ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  have hl5 : l ∈ t 4 := by
    rcases F5.cover_cases hlR with h | h | h | h | h
    · exact absurd h.1 hl0
    · obtain ⟨-, h', -⟩ := h
      omega
    · obtain ⟨-, -, h'⟩ := h
      omega
    · obtain ⟨-, -, h'⟩ := h
      omega
    · exact h.1
  -- the cell `(q, q)` of the square `[q, p) x [q, p)` lies in `T_5`
  have hqq : ((q, q) : Cell) ∈ t 4 := by
    have hR : ((q, q) : Cell) ∈ R a b :=
      mem_R.2 ⟨⟨by simp only; omega, by simp only; omega⟩, by simp only; omega, by simp only; omega⟩
    rcases F5.cover_cases hR with h | h | h | h | h
    · obtain ⟨-, -, h'⟩ := h
      simp only at h'
      omega
    · obtain ⟨-, h', -⟩ := h
      simp only at h'
      omega
    · obtain ⟨-, -, h'⟩ := h
      simp only at h'
      omega
    · obtain ⟨-, h', -⟩ := h
      simp only at h'
      omega
    · exact h.1
  -- `T_5` leaves `box(T_1)` through its top row or its right column
  obtain ⟨⟨ux, uy⟩, ⟨vx, vy⟩, hu, hv, huv, hA, hnA⟩ := (F5.conn 4).exists_adj_leaving
    (fun c : Cell => c.1 < p ∧ c.2 < q) hl5 hqq ⟨by omega, by omega⟩ (fun h => lt_irrefl q h.2)
  have huR := mem_R.1 (F5.sub_R 4 hu)
  simp only [adj_iff] at huv
  simp only at hA hnA huR
  rcases (by omega : (vx = p ∧ ux = p - 1 ∧ vy = uy) ∨ (vy = q ∧ uy = q - 1 ∧ vx = ux)) with
    ⟨e1, -, e3⟩ | ⟨-, e2, -⟩
  · rw [e1, e3] at hv
    exact absurd (F5.tile_unique (col1 uy (by omega) (by omega)) hv) (by decide)
  · rw [e2] at hu
    exact absurd (F5.tile_unique (top0 ux (by omega) (by omega)) hu) (by decide)

/-- `report-A2.md`, 4.2, third bullet, with `T_5` wide: "T_5 meets box(T_1) and
box(T_3), so y_5 < q and y_5+q-1 >= p". A hole of `T_1` and a hole of `T_3` lie
in `T_5`, because the four boxes are disjoint. -/
private theorem f4_short_y5 (F : FrameN P p q a b t o x5 y5) (S : Four P p q) (hq : q < p)
    (h0 : (o 0).swap = false) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) (h4 : (o 4).swap = false) : y5 < q ∧ p < y5 + q := by
  have F5 := F.toFrame5
  obtain ⟨ha, hb⟩ := f4_alt_ab F S h0 h1 h3
  have hH4 : (o 4).H p q = q := by simp [Orient.H, h4]
  have hW0 : (o 0).W p q = p := by simp [Orient.W, h0]
  have hH0 : (o 0).H p q = q := by simp [Orient.H, h0]
  have hW1 : (o 1).W p q = q := by simp [Orient.W, h1]
  have hH1 : (o 1).H p q = p := by simp [Orient.H, h1]
  have hW2 : (o 2).W p q = p := by simp [Orient.W, h2]
  have hH2 : (o 2).H p q = q := by simp [Orient.H, h2]
  have hW3 : (o 3).W p q = q := by simp [Orient.W, h3]
  have hH3 : (o 3).H p q = p := by simp [Orient.H, h3]
  constructor
  · obtain ⟨l, ⟨⟨hl1, hl2⟩, hl3, hl4⟩, hlP⟩ := F5.exists_hole (o 0)
    have hl0 : l ∉ t 0 := by
      rw [F5.mem0]
      exact hlP
    have hlR : l ∈ R a b := mem_R.2 ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    rcases F5.cover_cases hlR with h | h | h | h | h
    · exact absurd h.1 hl0
    · obtain ⟨-, h', -⟩ := h
      omega
    · obtain ⟨-, -, h'⟩ := h
      omega
    · obtain ⟨-, -, h'⟩ := h
      omega
    · obtain ⟨-, -, h', -⟩ := h
      omega
  · obtain ⟨l, ⟨⟨hl1, hl2⟩, hl3, hl4⟩, hlP⟩ := F5.exists_hole (o 2)
    have hc2 : ((a - 1 - l.1, b - 1 - l.2) : Cell) ∉ t 2 := by
      rw [F5.mem2]
      simpa using hlP
    have hcR : ((a - 1 - l.1, b - 1 - l.2) : Cell) ∈ R a b :=
      mem_R.2 ⟨⟨by simp only; omega, by simp only; omega⟩, by simp only; omega,
        by simp only; omega⟩
    rcases F5.cover_cases hcR with h | h | h | h | h
    · obtain ⟨-, -, h'⟩ := h
      simp only at h'
      omega
    · obtain ⟨-, -, h'⟩ := h
      simp only at h'
      omega
    · exact absurd h.1 hc2
    · obtain ⟨-, h', -⟩ := h
      simp only at h'
      omega
    · obtain ⟨-, -, -, h'⟩ := h
      simp only at h'
      omega

/-- A wide tile whose two short sides of `box(P)` are full holds the whole local
column `p - 1`: it is column `0` or column `p - 1` of `box(P)`. -/
private theorem f4_short_side (F : Frame5 P p q a b t o x5 y5) {c : Orient}
    (hc : c.swap = false) (hL : colCount P 0 = q) (hR : colCount P (p - 1) = q)
    {y : ℤ} (hy0 : 0 ≤ y) (hy1 : y < q) : c.back p q (p - 1, y) ∈ P := by
  have hL' := (F.colCount_eq_iff 0).1 hL
  have hR' := (F.colCount_eq_iff (p - 1)).1 hR
  rcases c with ⟨s, nx, ny⟩
  simp only at hc
  subst hc
  cases nx <;> cases ny <;> simp [Orient.back]
  · exact hR' _ hy0 hy1
  · exact hR' _ (by omega) (by omega)
  · exact hL' _ hy0 hy1
  · exact hL' _ (by omega) (by omega)

/-- A wide tile that misses a cell of its local row `0` and a cell of its local
row `q - 1` shows that neither long side of `box(P)` is full: the two local
rows are rows `0` and `q - 1` of `box(P)`. -/
private theorem f4_rows_not_full (F : Frame5 P p q a b t o x5 y5) {c : Orient}
    (hc : c.swap = false) {x1 x2 : ℤ} (hx1 : 0 ≤ x1 ∧ x1 < p) (hx2 : 0 ≤ x2 ∧ x2 < p)
    (n1 : c.back p q (x1, 0) ∉ P) (n2 : c.back p q (x2, q - 1) ∉ P) :
    rowCount P 0 ≠ p ∧ rowCount P (q - 1) ≠ p := by
  have hB := (F.rowCount_eq_iff 0).1
  have hT := (F.rowCount_eq_iff (q - 1)).1
  rcases c with ⟨s, nx, ny⟩
  simp only at hc
  subst hc
  cases nx <;> cases ny <;> simp [Orient.back] at n1 n2
  · exact ⟨fun h => n1 (hB h _ hx1.1 hx1.2), fun h => n2 (hT h _ hx2.1 hx2.2)⟩
  · exact ⟨fun h => n2 (hB h _ hx2.1 hx2.2), fun h => n1 (hT h _ hx1.1 hx1.2)⟩
  · exact ⟨fun h => n1 (hB h _ (by omega) (by omega)),
      fun h => n2 (hT h _ (by omega) (by omega))⟩
  · exact ⟨fun h => n2 (hB h _ (by omega) (by omega)),
      fun h => n1 (hT h _ (by omega) (by omega))⟩

/-- `report-A2.md`, 4.2, third bullet, with `T_5` wide: if both short sides of
`box(P)` are full, neither long side is. `T_5` meets `box(T_1)` and `box(T_3)`,
so `y5 < q` and `y5 + q - 1 ≥ p`; it meets `box(T_4)` and `box(T_2)`, so
`x5 < q` and `x5 + p - 1 ≥ p`. The cell `(p - 1, y5)` is in `T_1` (short side of
`T_1`) and on the lower long side of `box(T_5)`; the cell `(q, y5 + q - 1)` is
in `T_3` and on the upper long side of `box(T_5)`. -/
theorem n42_alt_short_wide (F : FrameN P p q a b t o x5 y5) (S : Four P p q) (hq : q < p)
    (h0 : (o 0).swap = false) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) (hL : colCount P 0 = q) (hR : colCount P (p - 1) = q)
    (h4 : (o 4).swap = false) : rowCount P 0 ≠ p ∧ rowCount P (q - 1) ≠ p := by
  have F5 := F.toFrame5
  obtain ⟨ha, hb⟩ := f4_alt_ab F S h0 h1 h3
  obtain ⟨hy5q, hy5p⟩ := f4_short_y5 F S hq h0 h1 h2 h3 h4
  have hW4 : (o 4).W p q = p := by simp [Orient.W, h4]
  have hx5 := F.x5_pos
  have hy5 := F.y5_pos
  have hx5' := F.x5_le
  -- `(p - 1, y5)` is on the short side of `T_1` and on the lower long side of `box(T_5)`
  have m1 : ((p - 1, y5) : Cell) ∈ t 0 := by
    rw [F5.mem0]
    exact f4_short_side F5 h0 hL hR (by omega) hy5q
  have n1 : (o 4).back p q (p - 1 - x5, 0) ∉ P := by
    intro h
    have h5 : ((p - 1, y5) : Cell) ∈ t 4 := by
      rw [F5.mem4]
      show (o 4).back p q (p - 1 - x5, y5 - y5) ∈ P
      rwa [sub_self]
    exact absurd (F5.tile_unique m1 h5) (by decide)
  -- `(q, y5 + q - 1)` is on the short side of `T_3` and on the upper long side of `box(T_5)`
  have m2 : ((q, y5 + q - 1) : Cell) ∈ t 2 := by
    rw [F5.mem2]
    show (o 2).back p q (a - 1 - q, b - 1 - (y5 + q - 1)) ∈ P
    rw [show a - 1 - q = p - 1 by omega, show b - 1 - (y5 + q - 1) = p - y5 by omega]
    exact f4_short_side F5 h2 hL hR (by omega) (by omega)
  have n2 : (o 4).back p q (q - x5, q - 1) ∉ P := by
    intro h
    have h5 : ((q, y5 + q - 1) : Cell) ∈ t 4 := by
      rw [F5.mem4]
      show (o 4).back p q (q - x5, y5 + q - 1 - y5) ∈ P
      rwa [show y5 + q - 1 - y5 = q - 1 by omega]
    exact absurd (F5.tile_unique m2 h5) (by decide)
  exact f4_rows_not_full F5 h4 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ n1 n2

/-- `report-A2.md`, 4.2, third bullet: "A quarter turn of R preserves the list of
boxes; so let T_5 be p wide." The quarter turn is `FrameN.transpose` followed
by `FrameN.flipX`. -/
theorem n42_alt_short (F : FrameN P p q a b t o x5 y5) (S : Four P p q) (hq : q < p)
    (h0 : (o 0).swap = false) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) (hL : colCount P 0 = q) (hR : colCount P (p - 1) = q) :
    rowCount P 0 ≠ p ∧ rowCount P (q - 1) ≠ p := by
  cases h4 : (o 4).swap
  · exact n42_alt_short_wide F S hq h0 h1 h2 h3 hL hR h4
  · obtain ⟨t', F'⟩ := F.transpose
    obtain ⟨t'', F''⟩ := F'.flipX
    exact n42_alt_short_wide F'' S hq (by simpa using h3) (by simpa using h0)
      (by simpa using h1) (by simpa using h2) hL hR (by simp [h4])

/-- `report-A2.md`, 4.2, "W_1 not W_2", after the reflection of `R a b` that
makes `T_1`, `T_3` wide and `T_2`, `T_4` tall. -/
theorem n42_alt (F : FrameN P p q a b t o x5 y5) (S : Four P p q) (hq : q < p)
    (h0 : (o 0).swap = false) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) : False := by
  have hns : ¬ SameMarks o := n42_alt_marks F hq h0 h1 h2 h3
  rcases n42_three_full F.toFrame5 S hns with ⟨hB, hT⟩ | ⟨hL, hR, hBT⟩
  · exact n42_alt_long F S hq h0 h1 h2 h3 hB hT
  · obtain ⟨nB, nT⟩ := n42_alt_short F S hq h0 h1 h2 h3 hL hR
    rcases hBT with h | h
    · exact nB h
    · exact nT h

/-- **`report-A2.md`, 4.2.** Pattern N with four occupied corners does not
occur. -/
theorem four_N (F : FrameN P p q a b t o x5 y5) (S : Four P p q) (hpq : q ≤ p) : False := by
  obtain ⟨h02, h13⟩ := n42_swaps F S
  by_cases h01 : (o 0).W p q = (o 1).W p q
  · exact n42_quadrants F S h01
  · have hq : q < p := by
      rcases lt_or_eq_of_le hpq with h | h
      · exact h
      · exact absurd (by simp [Orient.W, h]) h01
    have hne : q ≠ p := by omega
    rw [Orient.W_eq_iff hne] at h02 h13 h01
    cases h0 : (o 0).swap
    · have h1 : (o 1).swap = true := by
        revert h01; rw [h0]; cases (o 1).swap <;> simp
      exact n42_alt F S hq h0 h1 (h02 ▸ h0) (h13 ▸ h1)
    · have h1 : (o 1).swap = false := by
        revert h01; rw [h0]; cases (o 1).swap <;> simp
      obtain ⟨t', F'⟩ := F.flipX
      exact n42_alt F' S hq (by simpa using h1) (by simpa using h0)
        (by simpa using h13 ▸ h1) (by simpa using h02 ▸ h0)

end PolyominoOddOrder
