module

public import PolyominoOddOrder.H1Top

/-!
# Case (II.3) with a square box does not occur (`CaseII3Square.lean`)

Blueprint unit II3a. Type H2 with five tiles and `d = a`: `report-4.md`, section
5d (Lemma 40, Theorem 41).

The binding statement of this file is `theorem41`. The statements of Lemma 40
are marked PROVISIONAL: the owner of the file may restate them.

Notation: `T = t i₀` on row 0, `T' = t i₁` with spine row `b - 1`;
`u_0 = colCount (t i₀) 0`, `u_1 = colCount (t i₀) (a - 1)`,
`t = rowCount (t i₀) (d - 1)`; `G = F` when `(κ i₁).negX = false` and `G = H` when
it is `true` (`TypeH2.mirror_form`).

Commit `e5ca51d`.
-/

@[expose] public section

namespace PolyominoOddOrder

variable {a b d : ℤ} {t : Fin 5 → Finset Cell} {i₀ i₁ : Fin 5} {κ : Fin 5 → GridIso}

/-- In a 5-copy tiling of type H2 a vertical tile exists. -/
theorem exists_vertical5 (i₀ i₁ : Fin 5) : ∃ v : Fin 5, v ≠ i₀ ∧ v ≠ i₁ := by
  fin_cases i₀ <;> fin_cases i₁ <;> decide

/-! ## Working lemmas of this file -/

/-- Two sets with the same cells in rows `y` and `y'` have equal row counts. -/
private theorem rowCount_congr {S S' : Finset Cell} {y y' : ℤ}
    (h : ∀ x : ℤ, (x, y) ∈ S ↔ (x, y') ∈ S') : rowCount S y = rowCount S' y' := by
  unfold rowCount
  congr 1
  refine Finset.card_nbij' (fun c => (c.1, y')) (fun c => (c.1, y)) ?_ ?_ ?_ ?_
  · rintro ⟨x, z⟩ hc
    simp only [Finset.mem_coe, Finset.mem_filter] at hc ⊢
    obtain ⟨hc, rfl⟩ := hc
    exact ⟨(h x).1 hc, trivial⟩
  · rintro ⟨x, z⟩ hc
    simp only [Finset.mem_coe, Finset.mem_filter] at hc ⊢
    obtain ⟨hc, rfl⟩ := hc
    exact ⟨(h x).2 hc, trivial⟩
  · rintro ⟨x, z⟩ hc
    simp only [Finset.mem_coe, Finset.mem_filter] at hc
    exact Prod.ext rfl hc.2.symm
  · rintro ⟨x, z⟩ hc
    simp only [Finset.mem_coe, Finset.mem_filter] at hc
    exact Prod.ext rfl hc.2.symm

/-- A set that meets column `x` in an interval starting at row 0 meets it in the rows
`[0, colCount S x)`. -/
private theorem mem_col_iff {S : Finset Cell} {x : ℤ} (hI : ColInterval S x)
    (h0 : (x, 0) ∈ S) (hnn : ∀ y : ℤ, (x, y) ∈ S → 0 ≤ y) (y : ℤ) :
    (x, y) ∈ S ↔ 0 ≤ y ∧ y < colCount S x := by
  obtain ⟨⟨x', m⟩, hm, hmax⟩ := Finset.exists_max_image (S.filter fun c => c.1 = x)
    (fun c => c.2) ⟨(x, 0), Finset.mem_filter.2 ⟨h0, rfl⟩⟩
  rw [Finset.mem_filter] at hm
  obtain ⟨hm, hx⟩ := hm
  dsimp only at hx
  subst hx
  have hmem : ∀ z : ℤ, (x', z) ∈ S ↔ 0 ≤ z ∧ z < m + 1 := by
    intro z
    constructor
    · intro hz
      have h1 := hmax (x', z) (Finset.mem_filter.2 ⟨hz, rfl⟩)
      dsimp only at h1
      exact ⟨hnn z hz, by omega⟩
    · rintro ⟨h1, h2⟩
      exact hI 0 z m h1 (by omega) h0 hm
  have hm0 := hnn m hm
  have hcol : (S.filter fun c => c.1 = x') = ({x'} : Finset ℤ) ×ˢ Finset.Ico 0 (m + 1) := by
    ext ⟨u, z⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico]
    constructor
    · rintro ⟨hc, rfl⟩
      exact ⟨rfl, (hmem z).1 hc⟩
    · rintro ⟨rfl, hz⟩
      exact ⟨(hmem z).2 hz, rfl⟩
  have hcount : colCount S x' = m + 1 := by
    unfold colCount
    rw [hcol, Finset.card_product, Finset.card_singleton, one_mul, Int.card_Ico]
    omega
  rw [hcount, hmem]

/-- Membership in the mirror image. -/
private theorem mem_image_flipX {S : Finset Cell} {x y : ℤ} :
    (x, y) ∈ S.image (GridIso.flipX a).apply ↔ (a - 1 - x, y) ∈ S := by
  constructor
  · intro h
    obtain ⟨⟨u, v⟩, hc, he⟩ := Finset.mem_image.1 h
    rw [GridIso.flipX_apply] at he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rwa [show a - 1 - (a - 1 - u) = u by ring]
  · intro h
    refine Finset.mem_image.2 ⟨_, h, ?_⟩
    rw [GridIso.flipX_apply]
    simp

/-- Membership in the image under the reflection `F`. -/
private theorem mem_image_flipY {S : Finset Cell} {x y : ℤ} :
    (x, y) ∈ S.image (GridIso.flipY b).apply ↔ (x, b - 1 - y) ∈ S := by
  constructor
  · intro h
    obtain ⟨⟨u, v⟩, hc, he⟩ := Finset.mem_image.1 h
    rw [GridIso.flipY_apply] at he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rwa [show b - 1 - (b - 1 - v) = v by ring]
  · intro h
    refine Finset.mem_image.2 ⟨_, h, ?_⟩
    rw [GridIso.flipY_apply]
    simp

/-- Two grid isometries with the same switches and the same shift are equal. -/
private theorem gridIso_eq {g g' : GridIso} (h1 : g.swap = g'.swap) (h2 : g.negX = g'.negX)
    (h3 : g.negY = g'.negY) (h4 : g.shift.1 = g'.shift.1) (h5 : g.shift.2 = g'.shift.2) :
    g = g' := by
  obtain ⟨s, n, m, u, v⟩ := g
  obtain ⟨s', n', m', u', v'⟩ := g'
  dsimp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  rfl

/-- The first row of the box of a reflected vertical tile. -/
private theorem boxY_flipY_comp (b a : ℤ) (g : GridIso) :
    ((GridIso.flipY b).comp g).boxY a = b - a - g.boxY a := by
  obtain ⟨s, n, m, u, v⟩ := g
  cases m <;> simp [GridIso.comp, GridIso.boxY, GridIso.flipY, GridIso.apply] <;> omega

section Frames

variable {k : ℕ} {t : Fin k → Finset Cell} {i₀ : Fin k} {κ : Fin k → GridIso}

/-- Coordinates of a cell of a tile. -/
private theorem tile_bounds (F : Frame a b d t i₀ κ) {i : Fin k} {x y : ℤ}
    (hc : (x, y) ∈ t i) : (0 ≤ x ∧ x < a) ∧ 0 ≤ y ∧ y < b :=
  mem_R.1 (F.isTiling.subset_R i hc)

/-- For `d = a` the box of every tile has the columns `[0, a)`. Source: `report-4.md`,
Lemma 40 (a), proof: "Every box has the columns [0, a)". -/
private theorem square_xSpan (F : Frame a b d t i₀ κ) (hd : d = a) (i : Fin k) :
    xSpan (t i) = Finset.Ico 0 a := by
  cases hi : (κ i).swap
  · refine Finset.Subset.antisymm (xSpan_subset_of_subset_R (F.isTiling.subset_R i)) ?_
    intro x hx
    rw [Finset.mem_Ico] at hx
    have h := (F.horizontal_spine hi).2.2.1 x hx.1 hx.2
    exact mem_xSpan.2 ⟨_, h, _, h, le_rfl, le_rfl⟩
  · obtain ⟨-, hxs, -, hx, -⟩ := F.vertical_spine hi
    rw [hxs, show (κ i).boxX d = 0 by omega, zero_add, hd]

/-- For `d = a` every tile meets column 0. -/
private theorem square_left (F : Frame a b d t i₀ κ) (hd : d = a) (i : Fin k) :
    ∃ y, (0, y) ∈ t i := by
  have ha := F.two_le.1
  have h : (0 : ℤ) ∈ xSpan (t i) := by
    rw [square_xSpan F hd, Finset.mem_Ico]
    omega
  obtain ⟨⟨x, y⟩, hc, -, -, h1, -⟩ := mem_xSpan.1 h
  have hb := tile_bounds F hc
  dsimp only at h1
  obtain rfl : x = 0 := by omega
  exact ⟨y, hc⟩

/-- For `d = a` every tile meets column `a - 1`. -/
private theorem square_right (F : Frame a b d t i₀ κ) (hd : d = a) (i : Fin k) :
    ∃ y, (a - 1, y) ∈ t i := by
  have ha := F.two_le.1
  have h : a - 1 ∈ xSpan (t i) := by
    rw [square_xSpan F hd, Finset.mem_Ico]
    omega
  obtain ⟨-, -, ⟨x, y⟩, hc, -, h1⟩ := mem_xSpan.1 h
  have hb := tile_bounds F hc
  dsimp only at h1
  obtain rfl : x = a - 1 := by omega
  exact ⟨y, hc⟩

/-- For `d = a` every tile meets column 0 in an interval. Source: `report-4.md`,
Lemma 40 (a). -/
private theorem square_left_interval (F : Frame a b d t i₀ κ) (hd : d = a) (i : Fin k) :
    ColInterval (t i) 0 := by
  intro y₁ y₂ y₃ h12 h23 h1 h3
  by_contra h2
  obtain ⟨ha, hb⟩ := F.two_le
  have n1 : y₁ ≠ y₂ := fun h => h2 (h ▸ h1)
  have n3 : y₃ ≠ y₂ := fun h => h2 (h ▸ h3)
  have b1 := tile_bounds F h1
  have b3 := tile_bounds F h3
  obtain ⟨j, hj⟩ := F.isTiling.exists_tile (c := (0, y₂)) (mem_R.2 (by dsimp only; omega))
  have hij : i ≠ j := fun h => h2 (h ▸ hj)
  obtain ⟨z, hz⟩ := square_right F hd j
  have hm := interlace_left ha hb (F.isTiling.subset_R i)
    (F.isTiling.tile_isPolyomino F.poly i).2 (F.isTiling.subset_R j)
    (F.isTiling.tile_isPolyomino F.poly j).2 (by omega : y₁ < y₂) (by omega : y₂ < y₃) h1 h3 hj
    (q' := (a - 1, z)) ⟨F.isTiling.subset_R j hz, Or.inr (Or.inl rfl)⟩ hz
    (fun h => by have := h.1; dsimp only at this; omega)
  exact hm.not_disjoint (F.disjoint i j hij)

/-- For `d = a` every tile meets column `a - 1` in an interval: the mirror image. -/
private theorem square_right_interval (F : Frame a b d t i₀ κ) (hd : d = a) (i : Fin k) :
    ColInterval (t i) (a - 1) := by
  intro y₁ y₂ y₃ h12 h23 h1 h3
  have h := square_left_interval F.mirror hd i y₁ y₂ y₃ h12 h23
  simp only [mem_image_flipX, sub_zero] at h
  exact h h1 h3

/-- Two tiles do not change order between the walls. Source: `report-4.md`, Lemma
40 (b), proof: "If A is below B on the left wall and above it on the right, four such
cells are again interlaced." -/
private theorem no_cross (F : Frame a b d t i₀ κ) {i j : Fin k} (hij : i ≠ j) {y y' z z' : ℤ}
    (hi : (0, y) ∈ t i) (hj : (0, y') ∈ t j) (hi' : (a - 1, z) ∈ t i) (hj' : (a - 1, z') ∈ t j)
    (hy : y < y') (hz : z' < z) : False := by
  obtain ⟨ha, hb⟩ := F.two_le
  have ht := F.isTiling
  have B : ∀ {m : Fin k} {v : ℤ}, (0, v) ∈ t m → OnBoundary a b (0, v) := fun h =>
    ⟨ht.subset_R _ h, Or.inl rfl⟩
  have B' : ∀ {m : Fin k} {v : ℤ}, (a - 1, v) ∈ t m → OnBoundary a b (a - 1, v) := fun h =>
    ⟨ht.subset_R _ h, Or.inr (Or.inl rfl)⟩
  have ci := (ht.tile_isPolyomino F.poly i).2
  have cj := (ht.tile_isPolyomino F.poly j).2
  have bi := tile_bounds F hi
  have bj := tile_bounds F hj
  have bi' := tile_bounds F hi'
  have bj' := tile_bounds F hj'
  have p' := bpos_left (b := b) ha (by omega : y' ≠ 0)
  by_cases h0 : y = 0
  · subst h0
    refine (interlace ha hb (ht.subset_R i) ci (ht.subset_R j) cj (B hi) (B' hj') (B' hi') (B hj)
      hi hi' hj' hj ?_ ?_ ?_).not_disjoint (F.disjoint i j hij)
    · rw [bpos_bottom, bpos_right]; omega
    · rw [bpos_right, bpos_right]; omega
    · rw [bpos_right, p']; omega
  · have p := bpos_left (b := b) ha h0
    refine (interlace ha hb (ht.subset_R j) cj (ht.subset_R i) ci (B' hj') (B' hi') (B hj) (B hi)
      hj' hj hi' hi ?_ ?_ ?_).not_disjoint (F.disjoint j i hij.symm)
    · rw [bpos_right, bpos_right]; omega
    · rw [bpos_right, p']; omega
    · rw [p, p']; omega

/-- For `d = a` the box of a vertical tile starts in column 0, and the spine is column
0 or column `a - 1`. -/
private theorem square_spine (F : Frame a b d t i₀ κ) (hd : d = a) {i : Fin k}
    (hi : (κ i).swap = true) :
    (κ i).boxX d = 0 ∧ ((κ i).negX = false → (κ i).shift.1 = 0) ∧
      ((κ i).negX = true → (κ i).shift.1 = a - 1) := by
  obtain ⟨-, -, -, hx, -⟩ := F.vertical_spine hi
  have h0 : (κ i).boxX d = 0 := by omega
  refine ⟨h0, fun h => ?_, fun h => ?_⟩
  · simpa [GridIso.boxX, h] using h0
  · simp only [GridIso.boxX, h, ite_true] at h0
    omega

/-- The rows of a vertical tile lie in its box. -/
private theorem vertical_row (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true)
    {x y : ℤ} (hc : (x, y) ∈ t i) : (κ i).boxY a ≤ y ∧ y < (κ i).boxY a + a := by
  obtain ⟨-, -, hys, -, -⟩ := F.vertical_spine hi
  have h : y ∈ ySpan (t i) := mem_ySpan.2 ⟨_, hc, _, hc, le_rfl, le_rfl⟩
  rwa [hys, Finset.mem_Ico] at h

/-- The end rows of the box of a vertical tile are the images of the end columns of
`T` (`report-4.md`, Theorem 41 (4): "under one the bottom row of the box receives u_0
cells, under the other u_1"). -/
private theorem vertical_end_rows (F : Frame a b d t i₀ κ) {i : Fin k}
    (hi : (κ i).swap = true) :
    rowCount (t i) ((κ i).boxY a) = colCount (t i₀) (if (κ i).negY then a - 1 else 0) ∧
      rowCount (t i) ((κ i).boxY a + a - 1) =
        colCount (t i₀) (if (κ i).negY then 0 else a - 1) := by
  have h0 := F.vertical_rowCount hi 0
  have h1 := F.vertical_rowCount hi (a - 1)
  cases hn : (κ i).negY <;>
    simp only [hn, GridIso.boxY, Bool.false_eq_true, ite_true, ite_false] at h0 h1 ⊢
  · exact ⟨by rw [← h0, zero_add], by rw [← h1]; congr 1; omega⟩
  · exact ⟨by rw [← h1]; congr 1; omega, by rw [← h0]; congr 1; omega⟩

end Frames

/-! ## Section 5d: the square box -/

/-- Lemma 40 (a). PROVISIONAL. Source: `report-4.md`, Lemma 40 (a) (line 315): for
`d = a`, "Every tile meets column 0 and column a - 1, each in an interval of
rows." Proof idea: every box has the columns `[0, a)`; `interlace_left`. -/
theorem lemma40a (H : TypeH2 a b d t i₀ i₁ κ) (hd : d = a) (i : Fin 5) :
    (∃ y, (0, y) ∈ t i) ∧ (∃ y, (a - 1, y) ∈ t i) ∧
      ColInterval (t i) 0 ∧ ColInterval (t i) (a - 1) := by
  exact ⟨square_left H.frame hd i, square_right H.frame hd i, square_left_interval H.frame hd i,
    square_right_interval H.frame hd i⟩

/-- Lemma 40 (b). PROVISIONAL. Source: `report-4.md`, Lemma 40 (b) (line 315): "The
five tiles occur in the same order, from the bottom, on both walls". -/
theorem lemma40b (H : TypeH2 a b d t i₀ i₁ κ) (hd : d = a) (i j : Fin 5) (hij : i ≠ j) :
    (∀ y y' : ℤ, (0, y) ∈ t i → (0, y') ∈ t j → y < y') ↔
      ∀ y y' : ℤ, (a - 1, y) ∈ t i → (a - 1, y') ∈ t j → y < y' := by
  have F := H.frame
  obtain ⟨y, hy⟩ := square_left F hd i
  obtain ⟨y', hy'⟩ := square_left F hd j
  obtain ⟨z, hz⟩ := square_right F hd i
  obtain ⟨z', hz'⟩ := square_right F hd j
  constructor
  · intro h w w' hw hw'
    by_contra hlt
    have hne : w ≠ w' := fun e => hij (F.isTiling.tile_unique hw (e ▸ hw'))
    exact no_cross F hij hy hy' hw hw' (h y y' hy hy') (by omega)
  · intro h w w' hw hw'
    by_contra hlt
    have hne : w ≠ w' := fun e => hij (F.isTiling.tile_unique hw (e ▸ hw'))
    exact no_cross F hij.symm hw' hw hz' hz (by omega) (h z z' hz hz')

/-- Lemma 40 (c), second sentence. PROVISIONAL. Source: `report-4.md`, Lemma 40 (c)
(line 315): "A vertical tile with spine column 0 has a cells in column 0 and t in
column a - 1; with spine column a - 1, t and a." For `d = a` the box of a vertical
tile has the columns `[0, a)`. -/
theorem lemma40c (H : TypeH2 a b d t i₀ i₁ κ) (hd : d = a) {v : Fin 5} (hv₀ : v ≠ i₀)
    (hv₁ : v ≠ i₁) :
    (κ v).boxX d = 0 ∧
      colCount (t v) 0 = (if (κ v).negX then rowCount (t i₀) (d - 1) else a) ∧
      colCount (t v) (a - 1) = (if (κ v).negX then a else rowCount (t i₀) (d - 1)) := by
  have F := H.frame
  have hv := H.vert v hv₀ hv₁
  obtain ⟨hx, h0, h1⟩ := square_spine F hd hv
  have hrow0 : rowCount (t i₀) 0 = a := by
    have ha := F.two_le.1
    have hrow : ((t i₀).filter fun c => c.2 = 0) = Finset.Ico 0 a ×ˢ ({0} : Finset ℤ) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_singleton]
      constructor
      · rintro ⟨hc, rfl⟩
        exact ⟨(tile_bounds F hc).1, rfl⟩
      · rintro ⟨hc, rfl⟩
        exact ⟨F.row0 x hc.1 hc.2, rfl⟩
    unfold rowCount
    rw [hrow, Finset.card_product, Finset.card_singleton, mul_one, Int.card_Ico]
    omega
  have c0 := F.vertical_colCount hv 0
  have c1 := F.vertical_colCount hv (d - 1)
  refine ⟨hx, ?_⟩
  cases hn : (κ v).negX <;>
    simp only [hn, Bool.false_eq_true, ite_true, ite_false, neg_zero, zero_add] at c0 c1 ⊢
  · rw [h0 hn] at c0 c1
    rw [add_zero, hd] at c1
    exact ⟨c0.trans hrow0, by rw [c1, hd]⟩
  · rw [h1 hn] at c0 c1
    rw [show -(d - 1) + (a - 1) = 0 by omega] at c1
    exact ⟨c1, c0.trans hrow0⟩

/-! ## Theorem 41 -/

/-- The end columns of `T`, for `d = a`: rows `[0, u_0)` of column 0 and `[0, u_1)` of
column `a - 1`, with `u_0, u_1 >= 1`. -/
private theorem square_T_walls {k : ℕ} {t : Fin k → Finset Cell} {i₀ : Fin k}
    {κ : Fin k → GridIso} (F : Frame a b d t i₀ κ) (hd : d = a) :
    (∀ y : ℤ, (0, y) ∈ t i₀ ↔ 0 ≤ y ∧ y < colCount (t i₀) 0) ∧
      (∀ y : ℤ, (a - 1, y) ∈ t i₀ ↔ 0 ≤ y ∧ y < colCount (t i₀) (a - 1)) ∧
      1 ≤ colCount (t i₀) 0 ∧ 1 ≤ colCount (t i₀) (a - 1) := by
  have ha := F.two_le.1
  have r0 := F.row0 0 le_rfl (by omega)
  have r1 := F.row0 (a - 1) (by omega) (by omega)
  have h0 := mem_col_iff (square_left_interval F hd i₀) r0 fun y hy => (tile_bounds F hy).2.1
  have h1 := mem_col_iff (square_right_interval F hd i₀) r1 fun y hy => (tile_bounds F hy).2.1
  have p0 := (h0 0).1 r0
  have p1 := (h1 0).1 r1
  exact ⟨h0, h1, by omega, by omega⟩

/-- Theorem 41, steps (1) and (2). Source: `report-4.md`, Theorem 41 (1), (2)
(lines 325-326): for `T' = F(T)` and `u_0 < u_1` the tile `V_1` on the cell `(0, u_0)`
has spine column 0 and the box `[0, a) x [u_0, u_0 + a)`, and row `u_0` lies in `T` and
`V_1`. -/
private theorem square_first (H : TypeH2 a b d t i₀ i₁ κ) (hd : d = a)
    (hF : (κ i₁).negX = false) (hu : colCount (t i₀) 0 < colCount (t i₀) (a - 1)) :
    ∃ v, v ≠ i₀ ∧ v ≠ i₁ ∧ (κ v).negX = false ∧ (κ v).boxY a = colCount (t i₀) 0 ∧
      ∀ x : ℤ, (x, colCount (t i₀) 0) ∈ t v ↔
        (0 ≤ x ∧ x < a) ∧ (x, colCount (t i₀) 0) ∉ t i₀ := by
  have F := H.frame
  have ht := F.isTiling
  have ha := F.two_le.1
  obtain ⟨hT0, hT1, hu0, -⟩ := square_T_walls F hd
  generalize colCount (t i₀) 0 = u₀ at *
  generalize colCount (t i₀) (a - 1) = u₁ at *
  have hT' : ∀ y : ℤ, (0, y) ∈ t i₁ ↔ b - u₀ ≤ y ∧ y < b := by
    intro y
    rw [H.top_mem, hF, ite_eq_right Bool.false_ne_true, hT0]
    omega
  have huniq : ∀ {i j : Fin 5} {c : Cell}, c ∈ t i → i ≠ j → c ∉ t j := fun hi hij hj =>
    hij (ht.tile_unique hi hj)
  -- some vertical tile meets column 0 between `T` and `T'`
  have hgap : u₀ < b - u₀ := by
    obtain ⟨w, hw0, hw1⟩ := exists_vertical5 i₀ i₁
    obtain ⟨y, hy⟩ := square_left F hd w
    have hb := tile_bounds F hy
    have n0 := huniq hy hw0
    have n1 := huniq hy hw1
    rw [hT0] at n0
    rw [hT'] at n1
    omega
  obtain ⟨v, hv⟩ := ht.exists_tile (c := (0, u₀)) (mem_R.2 (by dsimp only; omega))
  have hv0 : v ≠ i₀ := by
    rintro rfl
    rw [hT0] at hv
    omega
  have hv1 : v ≠ i₁ := by
    rintro rfl
    rw [hT'] at hv
    omega
  have hs := H.vert v hv0 hv1
  -- a spine in column `a - 1` starts at or above row `u₁`
  have hright : ∀ w, w ≠ i₀ → w ≠ i₁ → (κ w).negX = true → u₁ ≤ (κ w).boxY a := by
    intro w hw0 hw1 hn
    have hsw := H.vert w hw0 hw1
    have hc := (F.vertical_spine hsw).1 ((κ w).boxY a) le_rfl (by omega)
    rw [(square_spine F hd hsw).2.2 hn] at hc
    have hb := tile_bounds F hc
    have n0 := huniq hc hw0
    rw [hT1] at n0
    omega
  have hn : (κ v).negX = false := by
    by_contra hn
    rw [Bool.not_eq_false] at hn
    have h1 := hright v hv0 hv1 hn
    have h2 := vertical_row F hs hv
    omega
  have hspine : ∀ y : ℤ, (κ v).boxY a ≤ y → y < (κ v).boxY a + a → (0, y) ∈ t v := by
    have h := (F.vertical_spine hs).1
    rwa [(square_spine F hd hs).2.1 hn] at h
  have hY : (κ v).boxY a = u₀ := by
    have h1 := vertical_row F hs hv
    have h2 := hspine ((κ v).boxY a) le_rfl (by omega)
    have hb := tile_bounds F h2
    have n0 := huniq h2 hv0
    rw [hT0] at n0
    omega
  rw [hY] at hspine
  -- `T'` starts at or above row `2 u₀`
  have hbig : u₀ + a ≤ b - u₀ := by
    have h := hspine (u₀ + a - 1) (by omega) (by omega)
    have hb := tile_bounds F h
    have n1 := huniq h hv1
    rw [hT'] at n1
    omega
  refine ⟨v, hv0, hv1, hn, hY, fun x => ⟨fun hx => ⟨(tile_bounds F hx).1, huniq hx hv0⟩, ?_⟩⟩
  rintro ⟨hx, hxT⟩
  obtain ⟨j, hj⟩ := ht.exists_tile (c := (x, u₀)) (mem_R.2 (by dsimp only; omega))
  have hj0 : j ≠ i₀ := fun h => hxT (h ▸ hj)
  by_cases hj1 : j = i₁
  · exfalso
    rw [hj1] at hj
    have h := (F.horizontal_spine H.horiz).2.2.2 _ hj
    rw [H.down, ite_eq_left rfl, H.top] at h
    dsimp only at h
    omega
  by_cases hjv : j = v
  · rwa [hjv] at hj
  exfalso
  have hsj := H.vert j hj0 hj1
  have hrow := vertical_row F hsj hj
  cases hnj : (κ j).negX
  · have hc := (F.vertical_spine hsj).1 ((κ j).boxY a) le_rfl (by omega)
    rw [(square_spine F hd hsj).2.1 hnj] at hc
    have hb := tile_bounds F hc
    have n0 := huniq hc hj0
    rw [hT0] at n0
    exact huniq hc hjv (hspine _ (by omega) (by omega))
  · have h1 := hright j hj0 hj1 hnj
    omega

/-- Theorem 41, step (3): for `T' = F(T)` the reflection `F` maps the tiling to a
tiling of type H2 with the same `T` and `T'`. Source: `report-4.md`, Theorem 41 (3)
(line 327). -/
theorem square_reflect (H : TypeH2 a b d t i₀ i₁ κ) (hF : (κ i₁).negX = false) :
    (t i₁).image (GridIso.flipY b).apply = t i₀ ∧
      TypeH2 a b d (fun i => (t (Equiv.swap i₀ i₁ i)).image (GridIso.flipY b).apply) i₀ i₁
        (fun i => (GridIso.flipY b).comp (κ (Equiv.swap i₀ i₁ i))) := by
  have F := H.frame
  have hT : (t i₁).image (GridIso.flipY b).apply = t i₀ := by
    ext ⟨x, y⟩
    rw [mem_image_flipY, H.top_mem, hF, ite_eq_right Bool.false_ne_true,
      show b - 1 - (b - 1 - y) = y by ring]
  have hκ : κ i₁ = GridIso.flipY b := by
    refine gridIso_eq H.horiz hF H.down ?_ H.top
    rcases H.mirror_form with h | h
    · exact h.2
    · rw [hF] at h
      exact absurd h.1 Bool.false_ne_true
  have hinv : (GridIso.flipY b).comp (GridIso.flipY b) = GridIso.one := by
    simp [GridIso.comp, GridIso.one, GridIso.flipY, GridIso.apply]
  have ht := F.isTiling.flipY.reindex (Equiv.swap i₀ i₁)
  refine ⟨hT, ⟨ht.disjoint, ht.cover, ?_, ?_, ?_, ?_, ?_, ?_⟩, H.ne, ?_, ?_, ?_, ?_⟩
  · simpa only [Equiv.swap_apply_left, hT] using F.poly
  · simpa only [Equiv.swap_apply_left, hT] using F.nonrect
  · simpa only [Equiv.swap_apply_left, hT] using F.row0
  · simpa only [Equiv.swap_apply_left, hT] using F.rows
  · intro i
    rw [Equiv.swap_apply_left, hT, GridIso.image_comp, ← F.image]
  · rw [Equiv.swap_apply_left, hκ, hinv]
  · simp [F.base, GridIso.comp, GridIso.one, GridIso.flipY]
  · simp [F.base, GridIso.comp, GridIso.one, GridIso.flipY]
  · simp [F.base, GridIso.comp, GridIso.one, GridIso.flipY, GridIso.apply]
  · intro i h0 h1
    simp [Equiv.swap_apply_of_ne_of_ne h0 h1, GridIso.comp, GridIso.flipY, H.vert i h0 h1]

/-- Theorem 41 for `T' = F(T)` and `u_0 < u_1`, steps (3) to (5). Source:
`report-4.md`, Theorem 41 (3), (4), (5) (lines 327-329): `V_1 = F(V_3)`, so
`F(V_2) = V_2` and `u_0 = u_1`. -/
private theorem square_main (H : TypeH2 a b d t i₀ i₁ κ) (hd : d = a)
    (hF : (κ i₁).negX = false) (hu : colCount (t i₀) 0 < colCount (t i₀) (a - 1)) : False := by
  have F := H.frame
  have ht := F.isTiling
  have ha := F.two_le.1
  obtain ⟨hT, H'⟩ := square_reflect H hF
  have F' := H'.frame
  obtain ⟨hT0, hT1, hu0, -⟩ := square_T_walls F hd
  obtain ⟨v, hv0, hv1, hvn, hvY, hvrow⟩ := square_first H hd hF hu
  have hF' : ((GridIso.flipY b).comp (κ (Equiv.swap i₀ i₁ i₁))).negX = false := by
    simp [F.base, GridIso.comp, GridIso.one, GridIso.flipY]
  have key := square_first H' hd hF'
  simp only [Equiv.swap_apply_left, hT] at key
  obtain ⟨w, hw0, hw1, hwn, hwY, hwrow⟩ := key hu
  rw [Equiv.swap_apply_of_ne_of_ne hw0 hw1] at hwn hwY hwrow
  have hsv := H.vert v hv0 hv1
  have hsw := H.vert w hw0 hw1
  have hsw' := H'.vert w hw0 hw1
  -- step (4): the two tiles are the same image of `T`
  have hrows := rowCount_congr fun x => (hvrow x).trans (hwrow x).symm
  have ev := (vertical_end_rows F hsv).1
  have ew := (vertical_end_rows F' hsw').1
  simp only [Equiv.swap_apply_left, hT, Equiv.swap_apply_of_ne_of_ne hw0 hw1, hwY] at ew
  rw [hvY, hrows, ew] at ev
  have hnY : (κ v).negY = ((GridIso.flipY b).comp (κ w)).negY := by
    cases h1 : (κ v).negY <;> cases h2 : ((GridIso.flipY b).comp (κ w)).negY <;>
      simp only [h1, h2, Bool.false_eq_true, ite_true, ite_false] at ev <;>
      first | rfl | omega
  have hκ : κ v = (GridIso.flipY b).comp (κ w) := by
    have s1 := (square_spine F hd hsv).2.1 hvn
    have s2 := (square_spine F' hd hsw').2.1
    simp only [Equiv.swap_apply_of_ne_of_ne hw0 hw1] at s2
    simp only [Equiv.swap_apply_of_ne_of_ne hw0 hw1] at hsw'
    refine gridIso_eq (hsv.trans hsw'.symm) (hvn.trans hwn.symm) hnY
      (s1.trans (s2 hwn).symm) ?_
    have e := hvY.trans hwY.symm
    simp only [GridIso.boxY, ← hnY] at e
    cases h1 : (κ v).negY <;>
      simp only [h1, Bool.false_eq_true, ite_true, ite_false] at e <;> omega
  have htv : t v = (t w).image (GridIso.flipY b).apply := by
    rw [F.image v, hκ, GridIso.image_comp, ← F.image w]
  have hwv : w ≠ v := by
    rintro rfl
    rw [boxY_flipY_comp, hvY] at hwY
    -- `T`, `V_1`, `T'` fill column 0, but another vertical tile meets it
    have hex : ∃ j : Fin 5, j ∉ ({i₀, i₁, w} : Finset (Fin 5)) := by
      by_contra h
      push Not at h
      have h1 := Finset.card_le_card fun j (_ : j ∈ Finset.univ) => h j
      have h2 : ({i₀, i₁, w} : Finset (Fin 5)).card ≤ 3 := Finset.card_le_three
      rw [Finset.card_univ, Fintype.card_fin] at h1
      omega
    obtain ⟨j, hj⟩ := hex
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    obtain ⟨y, hy⟩ := square_left F hd j
    have hb := tile_bounds F hy
    have n0 : (0, y) ∉ t i₀ := fun h => hj.1 (ht.tile_unique hy h)
    have n1 : (0, y) ∉ t i₁ := fun h => hj.2.1 (ht.tile_unique hy h)
    rw [hT0] at n0
    rw [H.top_mem, hF, ite_eq_right Bool.false_ne_true, hT0] at n1
    refine hj.2.2 (ht.tile_unique hy ?_)
    have h := (F.vertical_spine hsv).1 y (by omega) (by omega)
    rwa [(square_spine F hd hsv).2.1 hvn] at h
  -- the fifth tile
  have hex : ∃ j : Fin 5, j ∉ ({i₀, i₁, v, w} : Finset (Fin 5)) := by
    by_contra h
    push Not at h
    have h1 := Finset.card_le_card fun j (_ : j ∈ Finset.univ) => h j
    have h2 : ({i₀, i₁, v, w} : Finset (Fin 5)).card ≤ 4 := Finset.card_le_four
    rw [Finset.card_univ, Fintype.card_fin] at h1
    omega
  obtain ⟨m, hm⟩ := hex
  have hall : ∀ j : Fin 5, j = m ∨ j = i₀ ∨ j = i₁ ∨ j = v ∨ j = w := by
    have hcard : (insert m ({i₀, i₁, v, w} : Finset (Fin 5))).card = 5 := by
      rw [Finset.card_insert_of_notMem hm, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_pair hwv.symm]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hv1.symm, hw1.symm⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨H.ne.symm, hv0.symm, hw0.symm⟩
    have huniv := Finset.eq_univ_of_card _ (hcard.trans (Fintype.card_fin 5).symm)
    intro j
    have hj : j ∈ insert m ({i₀, i₁, v, w} : Finset (Fin 5)) := huniv ▸ Finset.mem_univ j
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hj
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
  obtain ⟨hm0, hm1, hmv, hmw⟩ := hm
  have hsm := H.vert m hm0 hm1
  -- step (5): `F(V_2) = V_2`
  have hsym : ∀ x y : ℤ, (x, y) ∈ t m → (x, b - 1 - y) ∈ t m := by
    intro x y hc
    have hbd := tile_bounds F hc
    obtain ⟨j, hj⟩ := ht.exists_tile (c := (x, b - 1 - y)) (mem_R.2 (by dsimp only; omega))
    have back : b - 1 - (b - 1 - y) = y := by ring
    rcases hall j with h | h | h | h | h <;> rw [h] at hj
    · exact hj
    · exact absurd (ht.tile_unique hc (by
        rwa [H.top_mem, hF, ite_eq_right Bool.false_ne_true])) hm1
    · rw [H.top_mem, hF, ite_eq_right Bool.false_ne_true, back] at hj
      exact absurd (ht.tile_unique hc hj) hm0
    · rw [htv, mem_image_flipY, back] at hj
      exact absurd (ht.tile_unique hc hj) hmw
    · refine absurd (ht.tile_unique hc ?_) hmv
      rwa [htv, mem_image_flipY]
  have hspine := (F.vertical_spine hsm).1
  have e1 := vertical_row F hsm (hsym _ _ (hspine ((κ m).boxY a) le_rfl (by omega)))
  have e2 := vertical_row F hsm
    (hsym _ _ (hspine ((κ m).boxY a + a - 1) (by omega) (by omega)))
  have hcount : rowCount (t m) ((κ m).boxY a) = rowCount (t m) ((κ m).boxY a + a - 1) := by
    refine rowCount_congr fun x => ⟨fun h => ?_, fun h => ?_⟩
    · have h' := hsym _ _ h
      rwa [show b - 1 - (κ m).boxY a = (κ m).boxY a + a - 1 by omega] at h'
    · have h' := hsym _ _ h
      rwa [show b - 1 - ((κ m).boxY a + a - 1) = (κ m).boxY a by omega] at h'
  rw [(vertical_end_rows F hsm).1, (vertical_end_rows F hsm).2] at hcount
  cases h1 : (κ m).negY <;>
    simp only [h1, Bool.false_eq_true, ite_true, ite_false] at hcount <;> omega

/-- Theorem 41. Source: `report-4.md`, section 5d, Theorem 41 (line 321): "Case
(II.3) with d = a does not occur." Proof (lines 323-329): a full end column of `T`
gives an even number of tiles (`Frame.even_of_full_column`); otherwise count the
two walls, compare with the reflected tiling, and get `V_1 = F(V_3)`,
`F(V_2) = V_2`, `u_0 = u_1`. -/
theorem theorem41 (H : TypeH2 a b d t i₀ i₁ κ) (hd : d = a) : False := by
  have F := H.frame
  have ha := F.two_le.1
  have hb := F.two_le.2
  obtain ⟨hT0, hT1, hu0, hu1⟩ := square_T_walls F hd
  have hodd : ¬ Even 5 := by decide
  -- `T` holds neither end column of its box in full
  have hua : colCount (t i₀) 0 < a := by
    by_contra h
    exact hodd (F.even_of_full_column hd (Or.inl fun y h1 h2 => (hT0 y).2 ⟨h1, by omega⟩))
  have hua' : colCount (t i₀) (a - 1) < a := by
    by_contra h
    exact hodd (F.even_of_full_column hd (Or.inr fun y h1 h2 => (hT1 y).2 ⟨h1, by omega⟩))
  have ht : rowCount (t i₀) (d - 1) < a := by
    by_contra h
    have hsub : ((t i₀).filter fun c => c.2 = d - 1) ⊆ Finset.Ico 0 a ×ˢ ({d - 1} : Finset ℤ) := by
      rintro ⟨x, y⟩ hc
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico,
        Finset.mem_singleton] at hc ⊢
      exact ⟨(tile_bounds F hc.1).1, hc.2⟩
    have hcard : (Finset.Ico 0 a ×ˢ ({d - 1} : Finset ℤ)).card ≤
        ((t i₀).filter fun c => c.2 = d - 1).card := by
      unfold rowCount at h
      rw [Finset.card_product, Finset.card_singleton, mul_one, Int.card_Ico]
      omega
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have hmem : ((0, d - 1) : Cell) ∈ (t i₀).filter fun c => c.2 = d - 1 := by
      rw [heq, Finset.mem_product, Finset.mem_Ico, Finset.mem_singleton]
      exact ⟨⟨le_rfl, by dsimp only; omega⟩, rfl⟩
    have h1 := (hT0 _).1 (Finset.mem_filter.1 hmem).1
    omega
  -- the three vertical tiles
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ : ∃ p q r : Fin 5, p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      (Finset.univ.erase i₀).erase i₁ = {p, q, r} := by
    rw [← Finset.card_eq_three, Finset.card_erase_of_mem
      (Finset.mem_erase.2 ⟨H.ne, Finset.mem_univ _⟩), Finset.card_erase_of_mem
      (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hvert : ∀ v ∈ ({p, q, r} : Finset (Fin 5)), v ≠ i₀ ∧ v ≠ i₁ := by
    intro v hv
    rw [← hset, Finset.mem_erase, Finset.mem_erase] at hv
    exact ⟨hv.2.1, hv.1⟩
  have hp := hvert p (by simp)
  have hq := hvert q (by simp)
  have hr := hvert r (by simp)
  have hsum : ∀ f : Fin 5 → ℤ, ∑ i, f i = f i₀ + f i₁ + f p + f q + f r := by
    intro f
    rw [← Finset.add_sum_erase _ f (Finset.mem_univ i₀),
      ← Finset.add_sum_erase _ f (Finset.mem_erase.2 ⟨H.ne, Finset.mem_univ i₁⟩), hset,
      Finset.sum_insert (by simp [hpq, hpr]), Finset.sum_pair hqr]
    ring
  -- the two walls
  have w0 := sum_colCount_of_cover t F.disjoint F.cover (by omega) (x := 0) le_rfl (by omega)
  have w1 := sum_colCount_of_cover t F.disjoint F.cover (by omega) (x := a - 1) (by omega)
    (by omega)
  rw [hsum, H.top_colCount, (lemma40c H hd hp.1 hp.2).2.1, (lemma40c H hd hq.1 hq.2).2.1,
    (lemma40c H hd hr.1 hr.2).2.1] at w0
  rw [hsum, H.top_colCount, (lemma40c H hd hp.1 hp.2).2.2, (lemma40c H hd hq.1 hq.2).2.2,
    (lemma40c H hd hr.1 hr.2).2.2] at w1
  rw [sub_zero] at w0
  rw [sub_self] at w1
  cases hF : (κ i₁).negX
  · -- `T' = F(T)`: the end columns of `T` differ
    have hne : colCount (t i₀) 0 ≠ colCount (t i₀) (a - 1) := by
      intro he
      rw [hF] at w0 w1
      cases h1 : (κ p).negX <;> cases h2 : (κ q).negX <;> cases h3 : (κ r).negX <;>
        simp only [h1, h2, h3, Bool.false_eq_true, ite_true, ite_false] at w0 w1 <;> omega
    rcases lt_or_gt_of_ne hne with h | h
    · exact square_main H hd hF h
    · refine square_main H.mirror hd (by simp [GridIso.comp, GridIso.flipX, H.horiz, hF]) ?_
      simpa only [colCount_image_flipX, sub_zero, sub_self] using h
  · -- `T'` is the half turn of `T`
    rw [hF] at w0 w1
    cases h1 : (κ p).negX <;> cases h2 : (κ q).negX <;> cases h3 : (κ r).negX <;>
      simp only [h1, h2, h3, Bool.false_eq_true, ite_true, ite_false] at w0 w1 <;> omega

end PolyominoOddOrder
