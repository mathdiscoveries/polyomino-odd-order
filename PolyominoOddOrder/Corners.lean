module

public import PolyominoOddOrder.Crossing

/-!
# Two corner cells in one tile (`Corners.lean`)

Blueprint unit C. Lemma 2 and Lemma 3 of `report.md` section 2, the images of
Lemma 3 on the other three sides, and the reduction "after an isometry of the
grid the rectangle is R(a, b) and a tile T contains all of row 0" that opens
case (II) of Theorem 6 and the proof of Theorem 62.

Standing assumptions (`report.md`, lines 47-48): `P` is a polyomino, `k >= 2`,
`t` is a `k`-copy tiling of `R a b` by `P`. Commit `e5ca51d`.
-/

@[expose] public section

namespace PolyominoOddOrder

/-! ## Helpers: the box of a tile that touches two opposite sides -/

/-- A set inside `R a b` with a cell in column 0 and a cell in column `a - 1` has
width `a` ("box(T) = R", `report.md`, proof of Lemma 2, horizontally). -/
theorem width_eq_of_cols {S : Finset Cell} {a b y y' : ℤ} (h : S ⊆ R a b)
    (h0 : (0, y) ∈ S) (h1 : (a - 1, y') ∈ S) : width S = a := by
  have ha : 0 < a := (mem_R.1 (h h0)).1.2
  have hs : xSpan S = Finset.Ico 0 a := by
    refine Finset.Subset.antisymm (xSpan_subset_of_subset_R h) fun x hx => ?_
    rw [Finset.mem_Ico] at hx
    exact mem_xSpan.2 ⟨_, h0, _, h1, hx.1, by dsimp only; omega⟩
  rw [width, hs, Int.card_Ico]
  omega

/-- A set inside `R a b` with a cell in row 0 and a cell in row `b - 1` has
height `b`. -/
theorem height_eq_of_rows {S : Finset Cell} {a b x x' : ℤ} (h : S ⊆ R a b)
    (h0 : (x, 0) ∈ S) (h1 : (x', b - 1) ∈ S) : height S = b := by
  have hb : 0 < b := (mem_R.1 (h h0)).2.2
  have hs : ySpan S = Finset.Ico 0 b := by
    refine Finset.Subset.antisymm (ySpan_subset_of_subset_R h) fun y hy => ?_
    rw [Finset.mem_Ico] at hy
    exact mem_ySpan.2 ⟨_, h0, _, h1, hy.1, by dsimp only; omega⟩
  rw [height, hs, Int.card_Ico]
  omega

/-- Conversely, a set inside `R a b` of width `a` meets the left and the right
column. -/
theorem exists_cols_of_width_eq {S : Finset Cell} {a b : ℤ} (h : S ⊆ R a b) (ha : 0 < a)
    (hw : width S = a) : (∃ y, (0, y) ∈ S) ∧ ∃ y, (a - 1, y) ∈ S := by
  have hs := xSpan_eq_of_width_eq h ha hw
  constructor
  · have h0 : (0 : ℤ) ∈ xSpan S := by rw [hs, Finset.mem_Ico]; omega
    obtain ⟨c, hc, _, _, hle, _⟩ := mem_xSpan.1 h0
    have hcR := mem_R.1 (h hc)
    have : c.1 = 0 := by omega
    exact ⟨c.2, by rw [← this]; exact hc⟩
  · have h1 : a - 1 ∈ xSpan S := by rw [hs, Finset.mem_Ico]; omega
    obtain ⟨_, _, d, hd, _, hle⟩ := mem_xSpan.1 h1
    have hdR := mem_R.1 (h hd)
    have : d.1 = a - 1 := by omega
    exact ⟨d.2, by rw [← this]; exact hd⟩

/-- In a set inside `R a b` that touches row 0, every cell lies below row
`height S` ("let box(T) = [0, a) x [0, d)", `report.md`, proof of Lemma 3). -/
theorem snd_lt_height {S : Finset Cell} {a b x : ℤ} (h : S ⊆ R a b) (h0 : (x, 0) ∈ S)
    {c : Cell} (hc : c ∈ S) : c.2 < height S := by
  have hcR := mem_R.1 (h hc)
  have hsub : Finset.Icc 0 c.2 ⊆ ySpan S := by
    intro y hy
    rw [Finset.mem_Icc] at hy
    exact mem_ySpan.2 ⟨_, h0, _, hc, hy.1, hy.2⟩
  have hle := Finset.card_le_card hsub
  rw [Int.card_Icc] at hle
  rw [height]
  omega

/-- A tiling with at least two tiles has a tile other than a given one. -/
theorem exists_other_tile {k : ℕ} (hk : 2 ≤ k) (i : Fin k) : ∃ i' : Fin k, i' ≠ i := by
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 hk
  exact exists_ne i

/-- The main case of Lemma 2: in a rectangle with `a, b >= 2` no tile has box `R`.
Source: `report.md`, section 2, Lemma 2 (proof). -/
theorem not_full_box (P : Finset Cell) (hP : IsPolyomino P) (k : ℕ) (hk : 2 ≤ k) (a b : ℤ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (t : Fin k → Finset Cell) (ht : IsTiling P a b t) (i : Fin k)
    (hw : width (t i) = a) (hl : ∃ x, (x, 0) ∈ t i) (hr : ∃ x, (x, b - 1) ∈ t i) : False := by
  obtain ⟨i', hne⟩ := exists_other_tile hk i
  obtain ⟨x₀, hx₀⟩ := hl
  obtain ⟨x₁, hx₁⟩ := hr
  have hT := ht.subset_R i
  have hT' := ht.subset_R i'
  have hh : height (t i) = b := height_eq_of_rows hT hx₀ hx₁
  have hw'le := width_le_of_subset_R hT' (by omega)
  have hh'le := height_le_of_subset_R hT' (by omega)
  have hw' : width (t i') = a := by
    rcases ht.dims i i' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  obtain ⟨⟨y₀, hy₀⟩, y₁, hy₁⟩ := exists_cols_of_width_eq hT' (by omega) hw'
  obtain ⟨c, hc', hc⟩ := crossing a b ha hb (t i') (t i) hT'
    (ht.tile_isPolyomino hP i').2
    ⟨_, hy₀, mem_leftCol.2 ⟨hT' hy₀, rfl⟩⟩ ⟨_, hy₁, mem_rightCol.2 ⟨hT' hy₁, rfl⟩⟩
    hT (ht.tile_isPolyomino hP i).2
    ⟨_, hx₀, mem_bottomRow.2 ⟨hT hx₀, rfl⟩⟩ ⟨_, hx₁, mem_topRow.2 ⟨hT hx₁, rfl⟩⟩
  exact hne (ht.tile_unique hc' hc)

/-- The strip case of Lemma 2: if `a = 1` or `b = 1`, no tile touches both the
first and the last column and both the first and the last row. Source:
`report.md`, section 2, Lemma 2 (proof, first sentence). -/
theorem not_full_strip (P : Finset Cell) (hP : IsPolyomino P) (k : ℕ) (hk : 2 ≤ k) (a b : ℤ)
    (hab : a = 1 ∨ b = 1) (t : Fin k → Finset Cell) (ht : IsTiling P a b t) (i : Fin k)
    {c d : Cell} (hc : c ∈ t i) (hd : d ∈ t i) (hcx : c.1 = 0) (hdx : d.1 = a - 1)
    (hcd : (c.2 = 0 ∧ d.2 = b - 1) ∨ (c.2 = b - 1 ∧ d.2 = 0)) : False := by
  obtain ⟨i', hne⟩ := exists_other_tile hk i
  obtain ⟨e, he⟩ := (ht.tile_isPolyomino hP i').1
  have heR := mem_R.1 (ht.subset_R i' he)
  have hcon := (ht.tile_isPolyomino hP i).2
  apply hne
  rcases hab with rfl | rfl
  · obtain ⟨x, hx⟩ : ∃ x, (x, e.2) ∈ t i := by
      rcases hcd with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hcon.exists_in_row hc hd (by omega) (by omega)
      · exact hcon.exists_in_row hd hc (by omega) (by omega)
    have hxR := mem_R.1 (ht.subset_R i hx)
    dsimp only at hxR
    have hxe : x = e.1 := by omega
    subst hxe
    exact ht.tile_unique he hx
  · obtain ⟨y, hy⟩ : ∃ y, (e.1, y) ∈ t i :=
      hcon.exists_in_col hc hd (by omega) (by omega)
    have hyR := mem_R.1 (ht.subset_R i hy)
    dsimp only at hyR
    have hye : y = e.2 := by omega
    subst hye
    exact ht.tile_unique he hy

/-! ## Lemmas 2 and 3 -/

/-- Lemma 2: the internal statement behind the frozen `lemma2_no_opposite_corners`.
Source: `report.md`, section 2, Lemma 2 (line 136): "No tile contains two opposite
corner cells of R." Proof idea: a strip (`a = 1` or `b = 1`) would be one tile;
otherwise `box(T) = R`, every tile has box `R`, and another tile crosses `T`
(`crossing`). -/
theorem no_opposite_corners (P : Finset Cell) (hP : IsPolyomino P)
    (k : ℕ) (hk : 2 ≤ k) (a b : ℤ) (t : Fin k → Finset Cell) (ht : IsTiling P a b t)
    (i : Fin k) :
    ¬ ((0, 0) ∈ t i ∧ (a - 1, b - 1) ∈ t i) ∧ ¬ ((a - 1, 0) ∈ t i ∧ (0, b - 1) ∈ t i) := by
  obtain ⟨ha, hb⟩ := ht.pos hP (by omega)
  have hT := ht.subset_R i
  by_cases hab : a = 1 ∨ b = 1
  · exact ⟨fun ⟨h0, h1⟩ =>
        not_full_strip P hP k hk a b hab t ht i h0 h1 rfl rfl (Or.inl ⟨rfl, rfl⟩),
      fun ⟨h0, h1⟩ =>
        not_full_strip P hP k hk a b hab t ht i h1 h0 rfl rfl (Or.inr ⟨rfl, rfl⟩)⟩
  · exact ⟨fun ⟨h0, h1⟩ =>
        not_full_box P hP k hk a b (by omega) (by omega) t ht i (width_eq_of_cols hT h0 h1)
          ⟨_, h0⟩ ⟨_, h1⟩,
      fun ⟨h0, h1⟩ =>
        not_full_box P hP k hk a b (by omega) (by omega) t ht i (width_eq_of_cols hT h1 h0)
          ⟨_, h0⟩ ⟨_, h1⟩⟩

/-- Lemma 3, step (i). Source: `report.md`, Lemma 3 (i) (lines 155-160): if `T`
holds `(0, 0)` and `(a - 1, 0)` and another tile `T'` holds `(x, 0)`, `0 < x < a - 1`,
then `T'` has no cell in the left or the right column. Proof idea:
`interlace_bottom`. -/
theorem lemma3_step_i (P : Finset Cell) (hP : IsPolyomino P) (k : ℕ) (a b : ℤ)
    (ha : 3 ≤ a) (hb : 2 ≤ b) (t : Fin k → Finset Cell) (ht : IsTiling P a b t)
    (i i' : Fin k) (hii' : i ≠ i') (h0 : (0, 0) ∈ t i) (h1 : (a - 1, 0) ∈ t i)
    (x : ℤ) (hx0 : 0 < x) (hxa : x < a - 1) (hx : (x, 0) ∈ t i') :
    ∀ c ∈ t i', 0 < c.1 ∧ c.1 < a - 1 := by
  intro c hc
  have hcR := ht.subset_R i' hc
  have hcR' := mem_R.1 hcR
  by_contra hcon
  have hcol : c.1 = 0 ∨ c.1 = a - 1 := by omega
  obtain ⟨e, he, he'⟩ := interlace_bottom (by omega) hb (ht.subset_R i)
    (ht.tile_isPolyomino hP i).2 (ht.subset_R i') (ht.tile_isPolyomino hP i').2 hx0 hxa h0 h1
    hx (q' := c) ⟨hcR, by rcases hcol with h | h <;> simp [h]⟩ hc (by omega)
  exact hii' (ht.tile_unique he he')

/-- Lemma 3, step (ii). Source: `report.md`, Lemma 3 (ii) (lines 162-166): with
`box(T) = [0, a) x [0, d)`, the tile `T'` has no cell in a row `>= d`. Proof idea:
enlarge `T'` by the full rows `d, ..., b - 1` and apply `interlace_bottom` with
`q' = (0, b - 1)`. -/
theorem lemma3_step_ii (P : Finset Cell) (hP : IsPolyomino P) (k : ℕ) (a b : ℤ)
    (ha : 3 ≤ a) (hb : 2 ≤ b) (t : Fin k → Finset Cell) (ht : IsTiling P a b t)
    (i i' : Fin k) (hii' : i ≠ i') (h0 : (0, 0) ∈ t i) (h1 : (a - 1, 0) ∈ t i)
    (x : ℤ) (hx0 : 0 < x) (hxa : x < a - 1) (hx : (x, 0) ∈ t i') :
    ∀ c ∈ t i', c.2 < height (t i) := by
  intro c hc
  by_contra hcon
  have hT := ht.subset_R i
  have hcR := mem_R.1 (ht.subset_R i' hc)
  have hd0 : 0 < height (t i) := snd_lt_height hT h0 h0
  have hcd : height (t i) ≤ c.2 := by omega
  -- the full rows `d, ..., b - 1`
  set U : Finset Cell := Finset.Ico 0 a ×ˢ Finset.Ico (height (t i)) b with hU
  have hmemU : ∀ e : Cell, e ∈ U ↔ (0 ≤ e.1 ∧ e.1 < a) ∧ height (t i) ≤ e.2 ∧ e.2 < b := by
    intro e
    rw [hU, Finset.mem_product, Finset.mem_Ico, Finset.mem_Ico]
  have hUR : U ⊆ R a b := by
    intro e he
    rw [hmemU] at he
    exact mem_R.2 ⟨he.1, by omega, he.2.2⟩
  have hcU : c ∈ U := (hmemU c).2 ⟨hcR.1, hcd, hcR.2.2⟩
  have hcon' : EdgeConnected (t i' ∪ U) :=
    (ht.tile_isPolyomino hP i').2.union (edgeConnected_rect 0 a (height (t i)) b) ⟨c, hc, hcU⟩
  have hqU : ((0, b - 1) : Cell) ∈ U := (hmemU _).2 ⟨by dsimp only; omega, by dsimp only; omega⟩
  obtain ⟨e, he, he'⟩ := interlace_bottom (by omega) hb hT (ht.tile_isPolyomino hP i).2
    (Finset.union_subset (ht.subset_R i') hUR) hcon' hx0 hxa h0 h1
    (Finset.mem_union_left _ hx) (q' := (0, b - 1)) ⟨hUR hqU, Or.inl rfl⟩
    (Finset.mem_union_right _ hqU) (by dsimp only; omega)
  rcases Finset.mem_union.1 he' with h | h
  · exact hii' (ht.tile_unique he h)
  · have h2 := ((hmemU e).1 h).2.1
    have h3 := snd_lt_height hT h0 he
    omega

/-- Lemma 3: the internal statement behind the frozen
`lemma3_adjacent_corners_full_row`. Source: `report.md`, section 2, Lemma 3
(lines 147-148). Proof idea: by steps (i) and (ii) the box of `T'` is at most
`a - 2` wide and `d` high, but its dimensions are `(a, d)` or `(d, a)`. -/
theorem adjacent_corners_full_row (P : Finset Cell) (hP : IsPolyomino P)
    (k : ℕ) (hk : 2 ≤ k) (a b : ℤ) (t : Fin k → Finset Cell) (ht : IsTiling P a b t)
    (i : Fin k) (h0 : (0, 0) ∈ t i) (h1 : (a - 1, 0) ∈ t i)
    (x : ℤ) (hx0 : 0 ≤ x) (hxa : x < a) :
    (x, 0) ∈ t i := by
  obtain ⟨ha, hb⟩ := ht.pos hP (by omega)
  have hT := ht.subset_R i
  by_cases hb1 : b = 1
  · -- in a strip of one row the columns of the connected tile have no gap
    obtain ⟨y, hy⟩ := (ht.tile_isPolyomino hP i).2.exists_in_col h0 h1 (x := x) hx0
      (by dsimp only; omega)
    have hyR := mem_R.1 (hT hy)
    dsimp only at hyR
    have hy0 : y = 0 := by omega
    subst hy0
    exact hy
  by_contra hx
  have hxne : x ≠ 0 := by rintro rfl; exact hx h0
  have hxne' : x ≠ a - 1 := by rintro rfl; exact hx h1
  obtain ⟨i', hi'⟩ := ht.exists_tile (c := (x, 0)) (mem_R.2 ⟨⟨hx0, hxa⟩, le_rfl, hb⟩)
  have hii' : i ≠ i' := by rintro rfl; exact hx hi'
  have hI := lemma3_step_i P hP k a b (by omega) (by omega) t ht i i' hii' h0 h1 x (by omega)
    (by omega) hi'
  have hII := lemma3_step_ii P hP k a b (by omega) (by omega) t ht i i' hii' h0 h1 x (by omega)
    (by omega) hi'
  have hw : width (t i) = a := width_eq_of_cols hT h0 h1
  have hw' : width (t i') ≤ a - 2 := by
    have hsub : xSpan (t i') ⊆ Finset.Icc 1 (a - 2) := by
      intro v hv
      obtain ⟨c, hc, d, hd, h2, h3⟩ := mem_xSpan.1 hv
      have hc1 := hI c hc
      have hd1 := hI d hd
      rw [Finset.mem_Icc]
      omega
    have hle := Finset.card_le_card hsub
    rw [Int.card_Icc] at hle
    rw [width]
    omega
  have hh' : height (t i') ≤ height (t i) := by
    have hsub : ySpan (t i') ⊆ Finset.Ico 0 (height (t i)) := by
      intro v hv
      obtain ⟨c, hc, d, hd, h2, h3⟩ := mem_ySpan.1 hv
      have hc1 := mem_R.1 (ht.subset_R i' hc)
      have hd1 := hII d hd
      rw [Finset.mem_Ico]
      omega
    have hle := Finset.card_le_card hsub
    rw [Int.card_Ico] at hle
    have hd0 : 0 < height (t i) := snd_lt_height hT h0 h0
    have hle' : height (t i') ≤ ((height (t i) - 0).toNat : ℤ) := Int.ofNat_le.2 hle
    omega
  rcases ht.dims i i' with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> omega

/-- Lemma 3 on the top side (image under the reflection `F`). Source:
`report-4.md`, Theorem 22, Step 1: "by Lemma 3 (applied after the reflection
y -> b - 1 - y) it contains row b - 1". -/
theorem adjacent_corners_full_top (P : Finset Cell) (hP : IsPolyomino P)
    (k : ℕ) (hk : 2 ≤ k) (a b : ℤ) (t : Fin k → Finset Cell) (ht : IsTiling P a b t)
    (i : Fin k) (h0 : (0, b - 1) ∈ t i) (h1 : (a - 1, b - 1) ∈ t i)
    (x : ℤ) (hx0 : 0 ≤ x) (hxa : x < a) :
    (x, b - 1) ∈ t i := by
  have h := adjacent_corners_full_row P hP k hk a b _ ht.flipY i
    (Finset.mem_image.2 ⟨_, h0, by simp⟩) (Finset.mem_image.2 ⟨_, h1, by simp⟩) x hx0 hxa
  obtain ⟨c, hc, hce⟩ := Finset.mem_image.1 h
  rw [GridIso.flipY_apply, Prod.mk.injEq] at hce
  have hc' : c = (x, b - 1) := Prod.ext hce.1 (by dsimp only; omega)
  rw [← hc']
  exact hc

/-- Lemma 3 on the left side (image under the transposition). -/
theorem adjacent_corners_full_left (P : Finset Cell) (hP : IsPolyomino P)
    (k : ℕ) (hk : 2 ≤ k) (a b : ℤ) (t : Fin k → Finset Cell) (ht : IsTiling P a b t)
    (i : Fin k) (h0 : (0, 0) ∈ t i) (h1 : (0, b - 1) ∈ t i)
    (y : ℤ) (hy0 : 0 ≤ y) (hyb : y < b) :
    (0, y) ∈ t i := by
  have h := adjacent_corners_full_row P hP k hk b a _ ht.transpose i
    (Finset.mem_image.2 ⟨_, h0, by simp⟩) (Finset.mem_image.2 ⟨_, h1, by simp⟩) y hy0 hyb
  obtain ⟨c, hc, hce⟩ := Finset.mem_image.1 h
  rw [GridIso.transpose_apply, Prod.mk.injEq] at hce
  have hc' : c = (0, y) := Prod.ext hce.2 hce.1
  rw [← hc']
  exact hc

/-- Lemma 3 on the right side. -/
theorem adjacent_corners_full_right (P : Finset Cell) (hP : IsPolyomino P)
    (k : ℕ) (hk : 2 ≤ k) (a b : ℤ) (t : Fin k → Finset Cell) (ht : IsTiling P a b t)
    (i : Fin k) (h0 : (a - 1, 0) ∈ t i) (h1 : (a - 1, b - 1) ∈ t i)
    (y : ℤ) (hy0 : 0 ≤ y) (hyb : y < b) :
    (a - 1, y) ∈ t i := by
  have h := adjacent_corners_full_left P hP k hk a b _ ht.flipX i
    (Finset.mem_image.2 ⟨_, h0, by simp⟩) (Finset.mem_image.2 ⟨_, h1, by simp⟩) y hy0 hyb
  obtain ⟨c, hc, hce⟩ := Finset.mem_image.1 h
  rw [GridIso.flipX_apply, Prod.mk.injEq] at hce
  have hc' : c = (a - 1, y) := Prod.ext (by dsimp only; omega) hce.2
  rw [← hc']
  exact hc

/-- The reduction that opens case (II). Source: `report.md`, proof of Theorem 6
(lines 263-265):

> Suppose (I) fails: some tile T contains two corner cells. By Lemma 2 they are
> adjacent corners. Apply the isometry of the grid that moves the side joining them to
> row 0 of a rectangle R(a, b). By Lemma 3, T contains row 0.

If a tile holds two of the four labelled corners, some tiling of a rectangle by
the same polyomino, with the same number of tiles, has a tile containing row 0.
Proof idea: Lemma 2 leaves four pairs of adjacent corners; the bottom pair is
Lemma 3, the others are carried to it by `IsTiling.flipY` and
`IsTiling.transpose`. `a, b >= 2` keeps the four labelled corners distinct cells;
both uses (Theorem 62, Corollary 63) have it from the remark "Thin rectangles". -/
theorem row_tiling_of_two_corners (P : Finset Cell) (hP : IsPolyomino P)
    (k : ℕ) (hk : 2 ≤ k) (a b : ℤ) (ha : 2 ≤ a) (hb : 2 ≤ b) (t : Fin k → Finset Cell)
    (ht : IsTiling P a b t) (i : Fin k) (j j' : Fin 4) (hjj' : j ≠ j') (hj : corner a b j ∈ t i)
    (hj' : corner a b j' ∈ t i) :
    ∃ (a' b' : ℤ) (t' : Fin k → Finset Cell), IsTiling P a' b' t' ∧
      ∀ x : ℤ, 0 ≤ x → x < a' → (x, 0) ∈ t' i := by
  have _ := ha -- not needed: if two labelled corners coincide the proof still goes through
  have _ := hb
  have hopp := no_opposite_corners P hP k hk a b t ht i
  -- the four sides, each carried to row 0
  have hbot : (0, 0) ∈ t i → (a - 1, 0) ∈ t i → ∃ (a' b' : ℤ) (t' : Fin k → Finset Cell),
      IsTiling P a' b' t' ∧ ∀ x : ℤ, 0 ≤ x → x < a' → (x, 0) ∈ t' i := fun h0 h1 =>
    ⟨a, b, t, ht, fun x => adjacent_corners_full_row P hP k hk a b t ht i h0 h1 x⟩
  have hright : (a - 1, 0) ∈ t i → (a - 1, b - 1) ∈ t i →
      ∃ (a' b' : ℤ) (t' : Fin k → Finset Cell),
      IsTiling P a' b' t' ∧ ∀ x : ℤ, 0 ≤ x → x < a' → (x, 0) ∈ t' i := fun h0 h1 =>
    ⟨b, a, _, ht.flipX.transpose, fun x hx0 hxb => Finset.mem_image.2 ⟨(0, x),
      Finset.mem_image.2 ⟨_,
        adjacent_corners_full_right P hP k hk a b t ht i h0 h1 x hx0 hxb, by simp⟩, by simp⟩⟩
  have htop : (0, b - 1) ∈ t i → (a - 1, b - 1) ∈ t i →
      ∃ (a' b' : ℤ) (t' : Fin k → Finset Cell),
      IsTiling P a' b' t' ∧ ∀ x : ℤ, 0 ≤ x → x < a' → (x, 0) ∈ t' i := fun h0 h1 =>
    ⟨a, b, _, ht.flipY, fun x hx0 hxa => Finset.mem_image.2 ⟨_,
      adjacent_corners_full_top P hP k hk a b t ht i h0 h1 x hx0 hxa, by simp⟩⟩
  have hleft : (0, 0) ∈ t i → (0, b - 1) ∈ t i → ∃ (a' b' : ℤ) (t' : Fin k → Finset Cell),
      IsTiling P a' b' t' ∧ ∀ x : ℤ, 0 ≤ x → x < a' → (x, 0) ∈ t' i := fun h0 h1 =>
    ⟨b, a, _, ht.transpose, fun x hx0 hxb => Finset.mem_image.2 ⟨_,
      adjacent_corners_full_left P hP k hk a b t ht i h0 h1 x hx0 hxb, by simp⟩⟩
  have key : ∀ j j' : Fin 4, j < j' → corner a b j ∈ t i → corner a b j' ∈ t i →
      ∃ (a' b' : ℤ) (t' : Fin k → Finset Cell), IsTiling P a' b' t' ∧
        ∀ x : ℤ, 0 ≤ x → x < a' → (x, 0) ∈ t' i := by
    intro j j' hlt hj hj'
    fin_cases j <;> fin_cases j' <;> first
      | exact absurd hlt (by decide)
      | exact hbot hj hj'
      | exact (hopp.1 (And.intro hj hj')).elim
      | exact hleft hj hj'
      | exact hright hj hj'
      | exact (hopp.2 (And.intro hj hj')).elim
      | exact htop hj' hj
  rcases lt_or_gt_of_ne hjj' with h | h
  · exact key j j' h hj hj'
  · exact key j' j h hj' hj

end PolyominoOddOrder
