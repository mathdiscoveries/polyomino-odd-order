module

public import PolyominoOddOrder.Frame5Sides

/-!
# Case (I), foundation 3: the tools (T2) to (T5) (`Frame5Tools.lean`)

Blueprint unit A0c (third increment). `report-A2.md`, section 2: crossing (T2),
barrier (T3), symmetry (T4), strip (T5). (T1) is in `Frame5Sides.lean`.

Every tool is stated for all the sides of `R a b` it is used at. The versions for
the top, the left and the right side follow from the one for the bottom side
through `Frame5.flipY` and `Frame5.transpose`.

| report | Lean |
|---|---|
| (T2) crossing | `crossing_T2a`, `crossing_T2b`, `Frame5.T2_bottom`, `T2_top`, `T2_left`, `T2_right` |
| (T3) barrier | `FrameO.T3_left`, `FrameO.T3_right` |
| (T4) symmetry | `Frame5.T4_sets`, `T4_flipX`, `T4_flipY`, `T4_halfTurn`, `T4_quarter` |
| (T5) strip | `Frame5.T5_bottom`, `T5_top`, `T5_left`, `T5_right` |

Source: `theoretician/report-A2.md` (goals lab, commit `076d663`), section 2.
-/

@[expose] public section

namespace PolyominoOddOrder

variable {P : Finset Cell} {p q a b : ℤ} {t : Fin 5 → Finset Cell} {o : Fin 5 → Orient}
  {x5 y5 : ℤ}

/-! ## (T2) Crossing -/

/-- (T2)(b): two disjoint connected sets in the strip of the rows `[0, H)`; the
order of their cells in row 0 is the order of their cells in row `H - 1`.
Source: `report-A2.md`, section 2, (T2)(b); by (F5) (`interlace`). The mirror
image is the same statement with `T` and `T'` exchanged. -/
theorem crossing_T2b {a b H : ℤ} {T T' : Finset Cell} (hTR : T ⊆ R a b)
    (hT : EdgeConnected T) (hT'R : T' ⊆ R a b) (hT' : EdgeConnected T')
    (hd : Disjoint T T') (hH : ∀ c ∈ T, c.2 < H) (hH' : ∀ c ∈ T', c.2 < H)
    {x₁ x₂ x₁' x₂' : ℤ} (h1 : (x₁, 0) ∈ T) (h2 : (x₂, H - 1) ∈ T) (h1' : (x₁', 0) ∈ T')
    (h2' : (x₂', H - 1) ∈ T') (hlt : x₁ < x₁') : x₂ < x₂' := by
  have hne : ∀ c, c ∈ T → c ∉ T' := fun c hc hc' => Finset.disjoint_left.1 hd hc hc'
  have b1 := mem_R.1 (hTR h1)
  have b2 := mem_R.1 (hTR h2)
  have b1' := mem_R.1 (hT'R h1')
  have b2' := mem_R.1 (hT'R h2')
  simp only at b1 b2 b1' b2'
  have hHpos : 0 < H := hH _ h1
  by_contra hcon
  have hne2 : x₂' ≠ x₂ := by
    rintro rfl
    exact hne _ h2 h2'
  have hlt2 : x₂' < x₂ := by omega
  rcases (by omega : H = 1 ∨ 2 ≤ H) with rfl | hH2
  · -- one row
    have row : ∀ {A : Finset Cell}, A ⊆ R a b → (∀ c ∈ A, c.2 < 1) → EdgeConnected A →
        ∀ {x x' z : ℤ}, (x, (0 : ℤ)) ∈ A → (x', (0 : ℤ)) ∈ A → x ≤ z → z ≤ x' →
          (z, (0 : ℤ)) ∈ A := by
      intro A hA hA1 hAc x x' z hx hx' hz hz'
      obtain ⟨y, hy⟩ := hAc.exists_in_col hx hx' hz hz'
      have := mem_R.1 (hA hy)
      have h' := hA1 _ hy
      simp only at this h'
      obtain rfl : y = 0 := by omega
      exact hy
    simp only [sub_self] at h2 h2'
    by_cases hc : x₁' ≤ x₂
    · exact hne _ (row hTR hH hT h1 h2 hlt.le hc) h1'
    · exact hne _ h2 (row hT'R hH' hT' h2' h1' hlt2.le (by omega))
  · have hsub : ∀ {A : Finset Cell}, A ⊆ R a b → (∀ c ∈ A, c.2 < H) → A ⊆ R a H := by
      intro A hA hA1 c hc
      have := mem_R.1 (hA hc)
      exact mem_R.2 ⟨this.1, this.2.1, hA1 c hc⟩
    have ha : 2 ≤ a := by omega
    have hT2 := hsub hTR hH
    have hT'2 := hsub hT'R hH'
    have hm := interlace ha hH2 hT2 hT hT'2 hT'
      (p := (x₁, 0)) (q := (x₁', 0)) (p' := (x₂, H - 1)) (q' := (x₂', H - 1))
      ⟨hT2 h1, Or.inr (Or.inr (Or.inl rfl))⟩ ⟨hT'2 h1', Or.inr (Or.inr (Or.inl rfl))⟩
      ⟨hT2 h2, Or.inr (Or.inr (Or.inr rfl))⟩ ⟨hT'2 h2', Or.inr (Or.inr (Or.inr rfl))⟩
      h1 h2 h1' h2' (by simp only [bpos_bottom]; exact hlt)
      (by simp only [bpos_bottom, bpos_top hH2]; omega)
      (by simp only [bpos_top hH2]; omega)
    exact hm.not_disjoint hd

/-- (T2)(a): `T` lies in the rows `[0, H)` and joins `(x₁, 0)` to `(x₂, H - 1)`;
a disjoint connected `T'` that starts in row 0 to the right of `x₁` and reaches
row `H - 1` or higher has a cell in row `H - 1` to the right of `x₂`. Source:
`report-A2.md`, section 2, (T2)(a). -/
theorem crossing_T2a {a b H : ℤ} {T T' : Finset Cell} (hTR : T ⊆ R a b)
    (hT : EdgeConnected T) (hT'R : T' ⊆ R a b) (hT' : EdgeConnected T')
    (hd : Disjoint T T') (hH : ∀ c ∈ T, c.2 < H)
    {x₁ x₂ x₁' : ℤ} (h1 : (x₁, 0) ∈ T) (h2 : (x₂, H - 1) ∈ T) (h1' : (x₁', 0) ∈ T')
    (hup : ∃ c ∈ T', H - 1 ≤ c.2) (hlt : x₁ < x₁') : ∃ x' : ℤ, x₂ < x' ∧ (x', H - 1) ∈ T' := by
  classical
  have hHpos : 0 < H := hH _ h1
  set A := T'.filter (fun c => c.2 < H) with hA
  have hAT : A ⊆ T' := Finset.filter_subset _ _
  set C := component A (x₁', 0) with hC
  have hCA : C ⊆ A := fun c hc => (mem_component.1 hc).1
  have hqA : ((x₁', 0) : Cell) ∈ A := Finset.mem_filter.2 ⟨h1', hHpos⟩
  have hqC : ((x₁', 0) : Cell) ∈ C := mem_component.2 ⟨hqA, Reach.refl _ _⟩
  have hCH : ∀ c ∈ C, c.2 < H := fun c hc => (Finset.mem_filter.1 (hCA hc)).2
  have hex : ∃ x' : ℤ, (x', H - 1) ∈ C := by
    by_contra hno
    push Not at hno
    obtain ⟨d, hd', hdH⟩ := hup
    have hdC : d ∉ C := by
      intro h
      have := hCH d h
      refine hno d.1 ?_
      have : d = (d.1, H - 1) := by
        ext
        · rfl
        · simp only; omega
      rwa [← this]
    obtain ⟨u, v, hu, hv, hadj, huC, hvC⟩ :=
      hT'.exists_adj_leaving (fun c => c ∈ C) h1' hd' hqC hdC
    have huH : u.2 < H := hCH u huC
    have hu1 : u.2 ≠ H - 1 := by
      intro h
      refine hno u.1 ?_
      have : u = (u.1, H - 1) := by
        ext
        · rfl
        · exact h
      rwa [← this]
    have hvH : v.2 < H := by
      unfold Adj at hadj
      omega
    exact hvC (component_closed huC (Finset.mem_filter.2 ⟨hv, hvH⟩) hadj)
  obtain ⟨x', hx'⟩ := hex
  refine ⟨x', ?_, hAT (hCA hx')⟩
  exact crossing_T2b hTR hT (fun c hc => hT'R (hAT (hCA hc))) (edgeConnected_component _ _)
    (Finset.disjoint_of_subset_right (fun c hc => hAT (hCA hc)) hd) hH hCH h1 h2 hqC hx' hlt

namespace Frame5

/-- (T2)(b) for the two corner tiles at the bottom side: if their boxes have the
same height and both contain the corner of their box opposite to the mark, the
boxes do not overlap in their columns. Used in Lemma 5.1 and in 7.1. -/
theorem T2_bottom (F : Frame5 P p q a b t o x5 y5) (hH : (o 0).H p q = (o 1).H p q)
    (h0 : (o 0).back p q ((o 0).W p q - 1, (o 0).H p q - 1) ∈ P)
    (h1 : (o 1).back p q ((o 1).W p q - 1, (o 1).H p q - 1) ∈ P) :
    (o 0).W p q + (o 1).W p q ≤ a := by
  have hlt : (o 0).W p q - 1 < a - (o 1).W p q := by
    refine crossing_T2b (F.sub_R 0) (F.conn 0) (F.sub_R 1) (F.conn 1)
      (F.tiling.disjoint 0 1 (by decide)) (H := (o 0).H p q) (fun c hc => (F.box0 hc).2.2)
      (fun c hc => hH ▸ (F.box1 hc).2.2) (x₁ := 0) (x₁' := a - 1) F.corner0 ?_ F.corner1 ?_ ?_
    · exact (F.mem0 _).2 h0
    · rw [F.mem1]
      have hx : a - 1 - (a - (o 1).W p q) = (o 1).W p q - 1 := by ring
      simp only [hx, hH]
      exact h1
    · have := F.two_le_a
      omega
  omega

/-- (T2)(b) for the two corner tiles at the top side. -/
theorem T2_top (F : Frame5 P p q a b t o x5 y5) (hH : (o 2).H p q = (o 3).H p q)
    (h2 : (o 2).back p q ((o 2).W p q - 1, (o 2).H p q - 1) ∈ P)
    (h3 : (o 3).back p q ((o 3).W p q - 1, (o 3).H p q - 1) ∈ P) :
    (o 2).W p q + (o 3).W p q ≤ a := by
  obtain ⟨t', F'⟩ := F.flipY
  have h : (o 3).W p q + (o 2).W p q ≤ a := F'.T2_bottom hH.symm h3 h2
  omega

/-- (T2)(b) for the two corner tiles at the left side. -/
theorem T2_left (F : Frame5 P p q a b t o x5 y5) (hW : (o 0).W p q = (o 3).W p q)
    (h0 : (o 0).back p q ((o 0).W p q - 1, (o 0).H p q - 1) ∈ P)
    (h3 : (o 3).back p q ((o 3).W p q - 1, (o 3).H p q - 1) ∈ P) :
    (o 0).H p q + (o 3).H p q ≤ b := by
  obtain ⟨t', F'⟩ := F.transpose
  have h : (o 0).tr.W p q + (o 3).tr.W p q ≤ b := by
    refine F'.T2_bottom ?_ ?_ ?_
    · change (o 0).tr.H p q = (o 3).tr.H p q
      simpa using hW
    · change (o 0).tr.back p q ((o 0).tr.W p q - 1, (o 0).tr.H p q - 1) ∈ P
      simpa [Orient.back_tr] using h0
    · change (o 3).tr.back p q ((o 3).tr.W p q - 1, (o 3).tr.H p q - 1) ∈ P
      simpa [Orient.back_tr] using h3
  simpa using h

/-- (T2)(b) for the two corner tiles at the right side. -/
theorem T2_right (F : Frame5 P p q a b t o x5 y5) (hW : (o 1).W p q = (o 2).W p q)
    (h1 : (o 1).back p q ((o 1).W p q - 1, (o 1).H p q - 1) ∈ P)
    (h2 : (o 2).back p q ((o 2).W p q - 1, (o 2).H p q - 1) ∈ P) :
    (o 1).H p q + (o 2).H p q ≤ b := by
  obtain ⟨t', F'⟩ := F.flipX
  exact F'.T2_left hW h1 h2

end Frame5

namespace Frame5

/-! ## Extreme lines of a tile, for any code -/

/-- A tile meets the first column of its box, whatever its code. -/
private theorem exists_first_col (F : Frame5 P p q a b t o x5 y5) (c : Orient) :
    ∃ y : ℤ, c.back p q (0, y) ∈ P := by
  have key : ∃ d ∈ P, (c.fwd p q d).1 = 0 := by
    obtain ⟨y, hy⟩ := F.left
    obtain ⟨y', hy'⟩ := F.right
    obtain ⟨x, hx⟩ := F.bottom
    obtain ⟨x', hx'⟩ := F.top
    rcases c with ⟨_ | _, _ | _, _ | _⟩
    · exact ⟨_, hy, by simp [Orient.fwd]⟩
    · exact ⟨_, hy, by simp [Orient.fwd]⟩
    · exact ⟨_, hy', by simp [Orient.fwd]⟩
    · exact ⟨_, hy', by simp [Orient.fwd]⟩
    · exact ⟨_, hx, by simp [Orient.fwd]⟩
    · exact ⟨_, hx', by simp [Orient.fwd]⟩
    · exact ⟨_, hx, by simp [Orient.fwd]⟩
    · exact ⟨_, hx', by simp [Orient.fwd]⟩
  obtain ⟨d, hd, h0⟩ := key
  refine ⟨(c.fwd p q d).2, ?_⟩
  rw [← h0]
  exact (c.back_fwd p q d).symm ▸ hd

/-- A tile meets the last column of its box, whatever its code. -/
private theorem exists_last_col (F : Frame5 P p q a b t o x5 y5) (c : Orient) :
    ∃ y : ℤ, c.back p q (c.W p q - 1, y) ∈ P := by
  obtain ⟨y, hy⟩ := F.exists_first_col c.reflX
  rw [Orient.back_reflX] at hy
  exact ⟨y, by simpa using hy⟩

/-- A tile meets the first row of its box, whatever its code. -/
private theorem exists_first_row (F : Frame5 P p q a b t o x5 y5) (c : Orient) :
    ∃ x : ℤ, c.back p q (x, 0) ∈ P := by
  obtain ⟨x, hx⟩ := F.exists_first_col c.tr
  rw [Orient.back_tr] at hx
  exact ⟨x, hx⟩

/-- A tile meets the last row of its box, whatever its code. -/
private theorem exists_last_row (F : Frame5 P p q a b t o x5 y5) (c : Orient) :
    ∃ x : ℤ, c.back p q (x, c.H p q - 1) ∈ P := by
  obtain ⟨x, hx⟩ := F.exists_last_col c.tr
  rw [Orient.back_tr] at hx
  exact ⟨x, by simpa using hx⟩

end Frame5

/-! ## (T3) Barrier -/

namespace FrameO

/-- (T3) Barrier, left: if `T_5` holds the cells `(x, y)`, `0 ≤ y < h`, and the
box of `T_1` has at most `h` rows, then the box of `T_1` lies left of column
`x`. Source: `report-A2.md`, section 2, (T3). -/
theorem T3_left (F : FrameO P p q a b t o x5 y5) {x h : ℤ}
    (hcol : ∀ y : ℤ, 0 ≤ y → y < h → ((x, y) : Cell) ∈ t 4) (hH : (o 0).H p q ≤ h) :
    (o 0).W p q ≤ x := by
  by_contra hcon
  have hb := F.toFrame5.box0 F.toFrame5.corner0
  have hx := (F.toFrame5.box4 (hcol 0 le_rfl (by omega))).1.1
  have hx5 := F.x5_pos
  obtain ⟨y, hy⟩ := F.toFrame5.exists_last_col (o 0)
  obtain ⟨z, hz⟩ := (F.toFrame5.conn 0).exists_in_col F.toFrame5.corner0
    ((F.toFrame5.mem0 _).2 hy) (x := x) (by dsimp only at hx ⊢; omega)
    (by dsimp only; omega)
  have hzb := (F.toFrame5.box0 hz).2
  have h4 := hcol z hzb.1 (by have := hzb.2; dsimp only at this; omega)
  exact absurd (F.toFrame5.tile_unique hz h4) (by decide)

/-- (T3) Barrier, right. -/
theorem T3_right (F : FrameO P p q a b t o x5 y5) {x h : ℤ}
    (hcol : ∀ y : ℤ, 0 ≤ y → y < h → ((x, y) : Cell) ∈ t 4) (hH : (o 1).H p q ≤ h) :
    (o 1).W p q ≤ a - 1 - x := by
  by_contra hcon
  have hb := F.toFrame5.box1 F.toFrame5.corner1
  have hx := (F.toFrame5.box4 (hcol 0 le_rfl (by omega))).1.2
  have hx5 := F.x5_le
  obtain ⟨y, hy⟩ := F.toFrame5.exists_last_col (o 1)
  have hy1 : ((a - (o 1).W p q, y) : Cell) ∈ t 1 := by
    rw [F.toFrame5.mem1]
    have he : a - 1 - (a - (o 1).W p q) = (o 1).W p q - 1 := by ring
    simpa only [he] using hy
  obtain ⟨z, hz⟩ := (F.toFrame5.conn 1).exists_in_col hy1 F.toFrame5.corner1 (x := x)
    (by dsimp only; omega) (by dsimp only at hx ⊢; omega)
  have hzb := (F.toFrame5.box1 hz).2
  have h4 := hcol z hzb.1 (by have := hzb.2; dsimp only at this; omega)
  exact absurd (F.toFrame5.tile_unique hz h4) (by decide)

end FrameO

/-! ## Codes: the symmetries of the box, seen in `box(P)` -/

/-- The mirror image of the box in a vertical line, seen in `box(P)`. -/
private theorem Orient.back_reflX_fwd (c : Orient) (p q : ℤ) (d : Cell) :
    c.reflX.back p q (c.fwd p q d) =
      if c.swap then (d.1, q - 1 - d.2) else (p - 1 - d.1, d.2) := by
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;> simp [Orient.reflX, Orient.back, Orient.fwd]

/-- The half turn of the box, seen in `box(P)`. -/
private theorem Orient.back_turn_fwd (c : Orient) (p q : ℤ) (d : Cell) :
    c.turn.back p q (c.fwd p q d) = (p - 1 - d.1, q - 1 - d.2) := by
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;> simp [Orient.turn, Orient.back, Orient.fwd]

/-- The quarter turn of a square box, seen in `box(P)`: a quarter turn in one or
in the other sense. -/
private theorem Orient.back_quarter_fwd (p : ℤ) :
    ∀ c : Orient,
      (∀ d : Cell, c.back p p (p - 1 - (c.fwd p p d).2, (c.fwd p p d).1) = (p - 1 - d.2, d.1)) ∨
        ∀ d : Cell, c.back p p (p - 1 - (c.fwd p p d).2, (c.fwd p p d).1) = (d.2, p - 1 - d.1) := by
  rintro ⟨_ | _, _ | _, _ | _⟩ <;> simp [Orient.back, Orient.fwd]

/-- The two reflections of a code agree after the axes are exchanged. -/
private theorem Orient.reflX_tr (c : Orient) : c.reflX.tr = c.tr.reflY := by
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;> rfl

namespace Frame5

/-! ## (T4) Symmetry -/

/-- (T4), for sets: a map of `R a b` into itself that is injective and carries
each corner tile into a corner tile (different tiles into different tiles)
carries `T_5` into `T_5`. Source: `report-A2.md`, section 2, (T4), first
sentence. -/
theorem T4_sets (F : Frame5 P p q a b t o x5 y5) (g : Cell → Cell)
    (hinj : Function.Injective g) (hR : ∀ c ∈ R a b, g c ∈ R a b) (σ : Fin 5 → Fin 5)
    (hσ : Function.Injective σ) (hσ4 : σ 4 = 4)
    (h : ∀ i : Fin 5, i ≠ 4 → ∀ c ∈ t i, g c ∈ t (σ i)) : ∀ c ∈ t 4, g c ∈ t 4 := by
  intro c hc
  obtain ⟨i, hi⟩ := F.tiling.exists_tile (hR c (F.sub_R 4 hc))
  obtain ⟨j, rfl⟩ := (Finite.injective_iff_surjective.1 hσ) i
  by_cases hj : j = 4
  · rw [hj, hσ4] at hi
    exact hi
  exfalso
  have hsub : (t j).image g ⊆ t (σ j) := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hd
    exact h j hj e he
  have hcard : (t (σ j)).card ≤ ((t j).image g).card := by
    rw [Finset.card_image_of_injective _ hinj]
    exact (F.tiling.tiles_congruent j (σ j)).card_eq.le
  rw [← Finset.eq_of_subset_of_card_le hsub hcard] at hi
  obtain ⟨d, hd, hdc⟩ := Finset.mem_image.1 hi
  rw [hinj hdc] at hd
  exact hj (F.tile_unique hd hc)

/-- The cell of `T_5` at a local position whose cell of `box(P)` is in `P`. -/
private theorem mem4_of_back (F : Frame5 P p q a b t o x5 y5) {l : Cell}
    (hl : (o 4).back p q l ∈ P) : ((l.1 + x5, l.2 + y5) : Cell) ∈ t 4 := by
  rw [F.mem4]
  simpa using hl

/-- The cell of `T_5` that is the image of the cell `c` of `P`. -/
private theorem mem4_of_fwd (F : Frame5 P p q a b t o x5 y5) {c : Cell} (hc : c ∈ P) :
    ((((o 4).fwd p q c).1 + x5, ((o 4).fwd p q c).2 + y5) : Cell) ∈ t 4 :=
  F.mem4_of_back (by rwa [Orient.back_fwd])

/-- An involution that carries `P` into itself is a symmetry of `P`. -/
private theorem iff_of_involution (f : Cell → Cell)
    (hf : ∀ c, f (f c) = c) (h : ∀ c ∈ P, f c ∈ P) (c : Cell) : c ∈ P ↔ f c ∈ P :=
  ⟨h c, fun hc => hf c ▸ h _ hc⟩

/-- (T4) for the reflection in the vertical midline: if it exchanges `T_1`, `T_2`
and `T_3`, `T_4` (equal codes), then `box(T_5)` is centred and `P` has a
reflection in an axis-parallel line as a symmetry. -/
theorem T4_flipX (F : Frame5 P p q a b t o x5 y5) (h01 : o 0 = o 1) (h23 : o 2 = o 3) :
    a = 2 * x5 + (o 4).W p q ∧
      ∀ c : Cell, c ∈ P ↔ (if (o 4).swap then (c.1, q - 1 - c.2) else (p - 1 - c.1, c.2)) ∈ P := by
  have h4 : ∀ c ∈ t 4, ((a - 1 - c.1, c.2) : Cell) ∈ t 4 := by
    refine F.T4_sets (fun c => (a - 1 - c.1, c.2)) ?_ ?_ ![1, 0, 3, 2, 4] (by decide) rfl ?_
    · rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
      simp only [Prod.mk.injEq] at hxy ⊢
      omega
    · intro c hc
      rw [mem_R] at hc ⊢
      dsimp only
      omega
    · intro i hi c hc
      fin_cases i
      · have hc' := (F.mem0 c).1 hc
        refine (F.mem1 _).2 ?_
        simpa [← h01] using hc'
      · have hc' := (F.mem1 c).1 hc
        refine (F.mem0 _).2 ?_
        simpa [h01] using hc'
      · have hc' := (F.mem2 c).1 hc
        refine (F.mem3 _).2 ?_
        simpa [← h23] using hc'
      · have hc' := (F.mem3 c).1 hc
        refine (F.mem2 _).2 ?_
        simpa [h23] using hc'
      · exact absurd rfl hi
  have ha : a = 2 * x5 + (o 4).W p q := by
    obtain ⟨y, hy⟩ := F.exists_first_col (o 4)
    obtain ⟨y', hy'⟩ := F.exists_last_col (o 4)
    have h1 := (F.box4 (h4 _ (F.mem4_of_back hy))).1.2
    have h2 := (F.box4 (h4 _ (F.mem4_of_back hy'))).1.1
    dsimp only at h1 h2
    omega
  refine ⟨ha, iff_of_involution _ ?_ ?_⟩
  · rintro ⟨x, y⟩
    cases (o 4).swap <;> simp
  · intro c hc
    have h5 := (F.mem4 _).1 (h4 _ (F.mem4_of_fwd hc))
    have he : a - 1 - (((o 4).fwd p q c).1 + x5) - x5 =
        (o 4).W p q - 1 - ((o 4).fwd p q c).1 := by omega
    simp only [he, add_sub_cancel_right] at h5
    rw [← Orient.back_reflX, Orient.back_reflX_fwd] at h5
    exact h5

/-- (T4) for the reflection in the horizontal midline. -/
theorem T4_flipY (F : Frame5 P p q a b t o x5 y5) (h03 : o 0 = o 3) (h12 : o 1 = o 2) :
    b = 2 * y5 + (o 4).H p q ∧
      ∀ c : Cell, c ∈ P ↔ (if (o 4).swap then (p - 1 - c.1, c.2) else (c.1, q - 1 - c.2)) ∈ P := by
  obtain ⟨t', F'⟩ := F.transpose
  have h01 : (o 0).tr = (o 3).tr := by rw [h03]
  have h23 : (o 2).tr = (o 1).tr := by rw [h12]
  have h := F'.T4_flipX h01 h23
  have hb : b = 2 * y5 + (o 4).tr.W p q := h.1
  have hP : ∀ c : Cell, c ∈ P ↔
      (if (o 4).tr.swap then (c.1, q - 1 - c.2) else (p - 1 - c.1, c.2)) ∈ P := h.2
  refine ⟨by simpa using hb, fun c => ?_⟩
  rw [hP c, Orient.tr_swap]
  cases (o 4).swap <;> simp

/-- (T4) for the half turn: if it exchanges `T_1`, `T_3` and `T_2`, `T_4`, then
`P` has a half turn as a symmetry. -/
theorem T4_halfTurn (F : Frame5 P p q a b t o x5 y5) (h02 : o 0 = o 2) (h13 : o 1 = o 3) :
    a = 2 * x5 + (o 4).W p q ∧ b = 2 * y5 + (o 4).H p q ∧
      ∀ c : Cell, c ∈ P ↔ (p - 1 - c.1, q - 1 - c.2) ∈ P := by
  have h4 : ∀ c ∈ t 4, ((a - 1 - c.1, b - 1 - c.2) : Cell) ∈ t 4 := by
    refine F.T4_sets (fun c => (a - 1 - c.1, b - 1 - c.2)) ?_ ?_ ![2, 3, 0, 1, 4] (by decide)
      rfl ?_
    · rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
      simp only [Prod.mk.injEq] at hxy ⊢
      omega
    · intro c hc
      rw [mem_R] at hc ⊢
      dsimp only
      omega
    · intro i hi c hc
      fin_cases i
      · have hc' := (F.mem0 c).1 hc
        refine (F.mem2 _).2 ?_
        simpa [← h02] using hc'
      · have hc' := (F.mem1 c).1 hc
        refine (F.mem3 _).2 ?_
        simpa [← h13] using hc'
      · have hc' := (F.mem2 c).1 hc
        refine (F.mem0 _).2 ?_
        simpa [h02] using hc'
      · have hc' := (F.mem3 c).1 hc
        refine (F.mem1 _).2 ?_
        simpa [h13] using hc'
      · exact absurd rfl hi
  have ha : a = 2 * x5 + (o 4).W p q := by
    obtain ⟨y, hy⟩ := F.exists_first_col (o 4)
    obtain ⟨y', hy'⟩ := F.exists_last_col (o 4)
    have h1 := (F.box4 (h4 _ (F.mem4_of_back hy))).1.2
    have h2 := (F.box4 (h4 _ (F.mem4_of_back hy'))).1.1
    dsimp only at h1 h2
    omega
  have hb : b = 2 * y5 + (o 4).H p q := by
    obtain ⟨x, hx⟩ := F.exists_first_row (o 4)
    obtain ⟨x', hx'⟩ := F.exists_last_row (o 4)
    have h1 := (F.box4 (h4 _ (F.mem4_of_back hx))).2.2
    have h2 := (F.box4 (h4 _ (F.mem4_of_back hx'))).2.1
    dsimp only at h1 h2
    omega
  refine ⟨ha, hb, iff_of_involution _ ?_ ?_⟩
  · rintro ⟨x, y⟩
    simp
  · intro c hc
    have h5 := (F.mem4 _).1 (h4 _ (F.mem4_of_fwd hc))
    have he : a - 1 - (((o 4).fwd p q c).1 + x5) - x5 =
        (o 4).W p q - 1 - ((o 4).fwd p q c).1 := by omega
    have he' : b - 1 - (((o 4).fwd p q c).2 + y5) - y5 =
        (o 4).H p q - 1 - ((o 4).fwd p q c).2 := by omega
    simp only [he, he'] at h5
    rw [← Orient.back_turn, Orient.back_turn_fwd] at h5
    exact h5

/-- (T4) for the quarter turn of a square `R a a`: if it takes `T_1` to `T_2`,
`T_2` to `T_3`, `T_3` to `T_4` and `T_4` to `T_1`, then `p = q` and `P` has a
quarter turn as a symmetry. In codes: each corner tile has the code of the one
before it with the two axes exchanged. -/
theorem T4_quarter (F : Frame5 P p q a b t o x5 y5) (hab : a = b) (h1 : o 1 = (o 0).tr)
    (h2 : o 2 = o 0) (h3 : o 3 = o 1) :
    p = q ∧ ∀ c : Cell, c ∈ P ↔ (q - 1 - c.2, c.1) ∈ P := by
  subst hab
  have h4 : ∀ c ∈ t 4, ((a - 1 - c.2, c.1) : Cell) ∈ t 4 := by
    refine F.T4_sets (fun c => (a - 1 - c.2, c.1)) ?_ ?_ ![1, 2, 3, 0, 4] (by decide) rfl ?_
    · rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
      simp only [Prod.mk.injEq] at hxy ⊢
      omega
    · intro c hc
      rw [mem_R] at hc ⊢
      dsimp only
      omega
    · intro i hi c hc
      fin_cases i
      · have hc' := (F.mem0 c).1 hc
        refine (F.mem1 _).2 ?_
        simpa [h1, Orient.back_tr] using hc'
      · have hc' := (F.mem1 c).1 hc
        refine (F.mem2 _).2 ?_
        simpa [h1, h2, Orient.back_tr] using hc'
      · have hc' := (F.mem2 c).1 hc
        refine (F.mem3 _).2 ?_
        simpa [h1, h2, h3, Orient.back_tr] using hc'
      · have hc' := (F.mem3 c).1 hc
        refine (F.mem0 _).2 ?_
        simpa [h1, h3, Orient.back_tr] using hc'
      · exact absurd rfl hi
  obtain ⟨y, hy⟩ := F.exists_first_col (o 4)
  obtain ⟨y', hy'⟩ := F.exists_last_col (o 4)
  obtain ⟨x, hx⟩ := F.exists_first_row (o 4)
  obtain ⟨x', hx'⟩ := F.exists_last_row (o 4)
  have e1 := (F.box4 (h4 _ (F.mem4_of_back hy))).2.1
  have e2 := (F.box4 (h4 _ (F.mem4_of_back hy'))).2.2
  have e3 := (F.box4 (h4 _ (F.mem4_of_back hx))).1.2
  have e4 := (F.box4 (h4 _ (F.mem4_of_back hx'))).1.1
  dsimp only at e1 e2 e3 e4
  have hWH : (o 4).W p q = (o 4).H p q := by omega
  have hxy : x5 = y5 := by omega
  have ha : a = 2 * x5 + (o 4).H p q := by omega
  have hpq : p = q := by
    rcases hs : (o 4).swap with _ | _ <;> simp [Orient.W, Orient.H, hs] at hWH <;> omega
  subst hpq
  have hHp : (o 4).H p p = p := by simp [Orient.H]
  have hrot : ∀ c ∈ P,
      (o 4).back p p (p - 1 - ((o 4).fwd p p c).2, ((o 4).fwd p p c).1) ∈ P := by
    intro c hc
    have h5 := (F.mem4 _).1 (h4 _ (F.mem4_of_fwd hc))
    have he : a - 1 - (((o 4).fwd p p c).2 + y5) - x5 = p - 1 - ((o 4).fwd p p c).2 := by omega
    have he' : ((o 4).fwd p p c).1 + x5 - y5 = ((o 4).fwd p p c).1 := by omega
    simpa only [he, he'] using h5
  refine ⟨rfl, ?_⟩
  rcases Orient.back_quarter_fwd p (o 4) with hq | hq
  · have step : ∀ c ∈ P, ((p - 1 - c.2, c.1) : Cell) ∈ P := fun c hc => hq c ▸ hrot c hc
    exact fun c => ⟨step c, fun hc => by simpa using step _ (step _ (step _ hc))⟩
  · have step : ∀ c ∈ P, ((c.2, p - 1 - c.1) : Cell) ∈ P := fun c hc => hq c ▸ hrot c hc
    exact fun c => ⟨fun hc => by simpa using step _ (step _ (step _ hc)),
      fun hc => by simpa using step _ hc⟩

/-! ## (T5) Strip -/

/-- (T5) at a free bottom side: `T_2` is not the image of `T_1` under the half
turn of the strip of the `H_1` rows next to the side. In codes: `o 1` is not
`o 0` with the local vertical direction reversed (the two boxes then have the
same height). Source: `report-A2.md`, section 2, (T5); uses (F4)
(`three_copy`). -/
theorem T5_bottom (F : Frame5 P p q a b t o x5 y5) (hfree : 1 ≤ y5)
    (h : o 1 = (o 0).reflY) : False := by
  have hH1 : (o 1).H p q = (o 0).H p q := by rw [h, Orient.H_reflY]
  -- the half turn of the strip exchanges the two tiles
  have hturn : ∀ x y : ℤ, ((x, y) : Cell) ∈ t 1 ↔
      ((a - 1 - x, (o 0).H p q - 1 - y) : Cell) ∈ t 0 := by
    intro x y
    rw [F.mem1, F.mem0, h, Orient.back_reflY]
  have hside := F.side_bottom hfree
  have hrow0 : ∀ x : ℤ, 0 ≤ x → x < a → ((x, 0) : Cell) ∈ t 0 ∨ ((x, 0) : Cell) ∈ t 1 := by
    intro x hx0 hxa
    by_cases hx : x < (o 0).rowLine p q P 0
    · exact Or.inl ((F.mem0 _).2 ((F.hside (by decide) x).2 ⟨hx0, hx⟩))
    · exact Or.inr ((F.mem1 _).2 ((F.hside (by decide) (a - 1 - x)).2 ⟨by omega, by omega⟩))
  have hrowH : ∀ x : ℤ, 0 ≤ x → x < a →
      ((x, (o 0).H p q - 1) : Cell) ∈ t 0 ∨ ((x, (o 0).H p q - 1) : Cell) ∈ t 1 := by
    intro x hx0 hxa
    rcases hrow0 (a - 1 - x) (by omega) (by omega) with h' | h'
    · refine Or.inr ((hturn _ _).2 ?_)
      rwa [sub_self]
    · rw [hturn] at h'
      have e1 : a - 1 - (a - 1 - x) = x := by ring
      rw [e1, sub_zero] at h'
      exact Or.inl h'
  -- every other tile misses the row `H - 1`
  have hmiss : ∀ i : Fin 5, i ≠ 0 → i ≠ 1 → ∀ x : ℤ, ((x, (o 0).H p q - 1) : Cell) ∉ t i := by
    intro i hi0 hi1 x hx
    have hxR := mem_R.1 (F.sub_R i hx)
    dsimp only at hxR
    rcases hrowH x hxR.1.1 hxR.1.2 with h' | h'
    · exact hi0 (F.tile_unique hx h')
    · exact hi1 (F.tile_unique hx h')
  have habove : ∀ i : Fin 5, i ≠ 0 → i ≠ 1 → (∃ d ∈ t i, (o 0).H p q ≤ d.2) →
      ∀ c ∈ t i, (o 0).H p q ≤ c.2 := by
    rintro i hi0 hi1 ⟨d, hd, hdH⟩ c hc
    by_contra hlt
    obtain ⟨x, hx⟩ := (F.conn i).exists_in_row hc hd (y := (o 0).H p q - 1) (by omega) (by omega)
    exact hmiss i hi0 hi1 x hx
  have hHb : (o 0).H p q ≤ b - 1 := F.H_le (by decide)
  have hH0 : 0 ≤ (o 0).H p q := by
    have := (F.box0 F.corner0).2
    dsimp only at this
    omega
  have h2 : ∀ c ∈ t 2, (o 0).H p q ≤ c.2 :=
    habove 2 (by decide) (by decide) ⟨_, F.corner2, hHb⟩
  have h3 : ∀ c ∈ t 3, (o 0).H p q ≤ c.2 :=
    habove 3 (by decide) (by decide) ⟨_, F.corner3, hHb⟩
  have h0 : ∀ c ∈ t 0, c.2 < (o 0).H p q := fun c hc => (F.box0 hc).2.2
  have h1 : ∀ c ∈ t 1, c.2 < (o 0).H p q := fun c hc => hH1 ▸ (F.box1 hc).2.2
  by_cases h4 : ∃ d ∈ t 4, (o 0).H p q ≤ d.2
  · -- `T_5` is above: three copies tile the rows `[H, b)`
    have h4' := habove 4 (by decide) (by decide) h4
    refine three_copy P F.poly F.notRect a (b - (o 0).H p q) _
      (F.tiling.upper_part ![2, 3, 4] (by decide) hH0 (by omega) ?_ ?_)
    · intro j
      fin_cases j
      · exact h2
      · exact h3
      · exact h4'
    · intro i hi
      fin_cases i
      · exact h0
      · exact h1
      · exact absurd rfl (hi 0)
      · exact absurd rfl (hi 1)
      · exact absurd rfl (hi 2)
  · -- `T_5` is below: three copies tile the strip
    push Not at h4
    refine three_copy P F.poly F.notRect a ((o 0).H p q) _
      (F.tiling.lower_part ![0, 1, 4] (by decide) hH0 (by omega) ?_ ?_)
    · intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h4
    · intro i hi
      fin_cases i
      · exact absurd rfl (hi 0)
      · exact absurd rfl (hi 1)
      · exact h2
      · exact h3
      · exact absurd rfl (hi 2)

/-- (T5) at a free top side. -/
theorem T5_top (F : Frame5 P p q a b t o x5 y5) (hfree : y5 + (o 4).H p q ≤ b - 1)
    (h : o 3 = (o 2).reflY) : False := by
  obtain ⟨t', F'⟩ := F.flipY
  refine F'.T5_bottom (by omega) ?_
  change o 2 = (o 3).reflY
  rw [h, Orient.reflY_reflY]

/-- (T5) at a free left side. -/
theorem T5_left (F : Frame5 P p q a b t o x5 y5) (hfree : 1 ≤ x5)
    (h : o 3 = (o 0).reflX) : False := by
  obtain ⟨t', F'⟩ := F.transpose
  refine F'.T5_bottom hfree ?_
  change (o 3).tr = (o 0).tr.reflY
  rw [h, Orient.reflX_tr]

/-- (T5) at a free right side. -/
theorem T5_right (F : Frame5 P p q a b t o x5 y5) (hfree : x5 + (o 4).W p q ≤ a - 1)
    (h : o 2 = (o 1).reflX) : False := by
  obtain ⟨t', F'⟩ := F.flipX
  exact F'.T5_left (by omega) h

end Frame5

end PolyominoOddOrder
