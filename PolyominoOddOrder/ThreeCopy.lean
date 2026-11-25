module

public import PolyominoOddOrder.H1Top

/-!
# Three copies (`ThreeCopy.lean`)

Blueprint unit T. Proposition 61 and Theorem 62 of `report-4.md` section 8: no
rectangle is tiled by exactly three congruent non-rectangular polyominoes.

This is printed prior work, credited to S. J. Maltby, "Trisecting a rectangle",
J. Combin. Theory Ser. A 66 (1994) (`report.md`, section 3, lines 323-326); the
proof formalized here is the reports' own second route.

The proof of `three_copy` below is complete given its five inputs:
`IsTiling.two_le` (thin rectangles), `row_tiling_of_two_corners` (Lemmas 2 and
3), `theorem6_three` (Lemmas 4 and 5 with `k = 3`), `TypeH1.proposition27` and
`proposition61`.

Sources: `report-4.md`, section 8, Proposition 61 (lines 577-585), Theorem 62
(lines 587-593). Commit `e5ca51d`.
-/

@[expose] public section

namespace PolyominoOddOrder

/-! ## Counting helpers -/

namespace Prop61

/-- A row with no cell of `S` has count 0. -/
theorem rowCount_eq_zero {S : Finset Cell} {y : ℤ} (h : ∀ c ∈ S, c.2 ≠ y) :
    rowCount S y = 0 := by
  unfold rowCount
  rw [Finset.filter_eq_empty_iff.2 fun c hc => h c hc, Finset.card_empty, Nat.cast_zero]

/-- A column with no cell of `S` has count 0. -/
theorem colCount_eq_zero {S : Finset Cell} {x : ℤ} (h : ∀ c ∈ S, c.1 ≠ x) :
    colCount S x = 0 := by
  unfold colCount
  rw [Finset.filter_eq_empty_iff.2 fun c hc => h c hc, Finset.card_empty, Nat.cast_zero]

/-- A row count is positive exactly when the row holds a cell. -/
theorem rowCount_pos_iff {S : Finset Cell} {y : ℤ} :
    0 < rowCount S y ↔ ∃ x : ℤ, (x, y) ∈ S := by
  unfold rowCount
  rw [Nat.cast_pos, Finset.card_pos]
  constructor
  · rintro ⟨⟨x, y'⟩, hc⟩
    obtain ⟨hcS, rfl⟩ := Finset.mem_filter.1 hc
    exact ⟨x, hcS⟩
  · rintro ⟨x, hx⟩
    exact ⟨(x, y), Finset.mem_filter.2 ⟨hx, rfl⟩⟩

/-- A column count is positive exactly when the column holds a cell. -/
theorem colCount_pos_iff {S : Finset Cell} {x : ℤ} :
    0 < colCount S x ↔ ∃ y : ℤ, (x, y) ∈ S := by
  unfold colCount
  rw [Nat.cast_pos, Finset.card_pos]
  constructor
  · rintro ⟨⟨x', y⟩, hc⟩
    obtain ⟨hcS, rfl⟩ := Finset.mem_filter.1 hc
    exact ⟨y, hcS⟩
  · rintro ⟨y, hy⟩
    exact ⟨(x, y), Finset.mem_filter.2 ⟨hy, rfl⟩⟩

/-- The row segment `[0, a) x {y}` has `a` cells. -/
theorem card_rowSegment {a : ℤ} (ha : 0 ≤ a) (y : ℤ) :
    ((Finset.Ico 0 a ×ˢ ({y} : Finset ℤ)).card : ℤ) = a := by
  rw [Finset.card_product, Finset.card_singleton, mul_one, Int.card_Ico]
  omega

/-- A set that holds the row segment `[0, a) x {y}` has at least `a` cells in row
`y`. -/
theorem le_rowCount_of_full {S : Finset Cell} {a y : ℤ} (ha : 0 ≤ a)
    (h : ∀ x : ℤ, 0 ≤ x → x < a → (x, y) ∈ S) : a ≤ rowCount S y := by
  unfold rowCount
  rw [← card_rowSegment ha y]
  refine Nat.cast_le.2 (Finset.card_le_card ?_)
  rintro ⟨x, y'⟩ hc
  simp only [Finset.mem_product, Finset.mem_Ico, Finset.mem_singleton] at hc
  obtain ⟨⟨hx0, hxa⟩, rfl⟩ := hc
  exact Finset.mem_filter.2 ⟨h x hx0 hxa, rfl⟩

/-- A set whose cells in row `y` lie in the columns `[0, a)`, with at least `a`
cells in that row, holds the whole row segment. -/
theorem full_of_le_rowCount {S : Finset Cell} {a y : ℤ} (ha : 0 ≤ a)
    (hS : ∀ x : ℤ, (x, y) ∈ S → 0 ≤ x ∧ x < a) (h : a ≤ rowCount S y) :
    ∀ x : ℤ, 0 ≤ x → x < a → (x, y) ∈ S := by
  have hsub : (S.filter fun c => c.2 = y) ⊆ Finset.Ico 0 a ×ˢ ({y} : Finset ℤ) := by
    rintro ⟨x, y'⟩ hc
    obtain ⟨hcS, rfl⟩ := Finset.mem_filter.1 hc
    simp only [Finset.mem_product, Finset.mem_Ico, Finset.mem_singleton, and_true]
    exact hS x hcS
  have heq : (S.filter fun c => c.2 = y) = Finset.Ico 0 a ×ˢ ({y} : Finset ℤ) := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [← Nat.cast_le (α := ℤ), card_rowSegment ha y]
    exact h
  intro x hx0 hxa
  have hmem : (x, y) ∈ Finset.Ico 0 a ×ˢ ({y} : Finset ℤ) := by
    simp only [Finset.mem_product, Finset.mem_Ico, Finset.mem_singleton, and_true]
    exact ⟨hx0, hxa⟩
  rw [← heq] at hmem
  exact (Finset.mem_filter.1 hmem).1

/-- A sum over three indices, listed as three distinct ones. -/
theorem sum_fin_three (f : Fin 3 → ℤ) {i₀ i₁ v : Fin 3} (h₁ : i₁ ≠ i₀) (hv₀ : v ≠ i₀)
    (hv₁ : v ≠ i₁) : ∑ i, f i = f i₀ + f i₁ + f v := by
  rw [Fin.sum_univ_three]
  fin_cases i₀ <;> fin_cases i₁ <;> fin_cases v <;> simp_all <;> omega

/-- Three distinct indices exhaust `Fin 3`. -/
theorem fin_three_cases {i₀ i₁ v : Fin 3} (h₁ : i₁ ≠ i₀) (hv₀ : v ≠ i₀) (hv₁ : v ≠ i₁)
    (i : Fin 3) : i = i₀ ∨ i = i₁ ∨ i = v := by
  omega

end Prop61

/-! ## Proposition 61: three tiles, two of them horizontal -/

/-- Proposition 61, step (2), rows. Source: `report-4.md`, Proposition 61 (2)
(line 583): counting the rows of `R`, the rows `[y, y + a)` of the vertical tile
`V` are symmetric under `r -> b - 1 - r`, so `2y = b - a`, and the column counts
of `T` are symmetric: `mu(i) = mu(a - 1 - i)`. -/
theorem proposition61_rows {a b d : ℤ} {t : Fin 3 → Finset Cell} {i₀ i₁ : Fin 3}
    {κ : Fin 3 → GridIso} (H : TypeH2 a b d t i₀ i₁ κ) {v : Fin 3} (hv₀ : v ≠ i₀)
    (hv₁ : v ≠ i₁) :
    2 * (κ v).boxY a = b - a ∧ ∀ x : ℤ, colCount (t i₀) x = colCount (t i₀) (a - 1 - x) := by
  have F := H.frame
  have hsub : ∀ i, ∀ c ∈ t i, (0 ≤ c.1 ∧ c.1 < a) ∧ 0 ≤ c.2 ∧ c.2 < b := fun i c hc =>
    mem_R.1 (F.isTiling.subset_R i hc)
  obtain ⟨ha, hb⟩ := F.two_le
  have hvs := H.vert v hv₀ hv₁
  obtain ⟨hspine, -, hspan, -, hy1, hyb⟩ := F.vertical_spine hvs
  -- the rows of `V` are symmetric under `r -> b - 1 - r`
  have hrow : ∀ r : ℤ, 0 ≤ r → r < b →
      rowCount (t i₀) r + rowCount (t i₀) (b - 1 - r) + rowCount (t v) r = a := by
    intro r hr0 hrb
    have h := sum_rowCount_of_cover t F.disjoint F.cover (by omega) hr0 hrb
    rw [Prop61.sum_fin_three (fun i => rowCount (t i) r) H.ne hv₀ hv₁] at h
    simp only [H.top_rowCount r] at h
    exact h
  have hsymm : ∀ r : ℤ, rowCount (t v) r = rowCount (t v) (b - 1 - r) := by
    intro r
    by_cases hr : 0 ≤ r ∧ r < b
    · have h1 := hrow r hr.1 hr.2
      have h2 := hrow (b - 1 - r) (by omega) (by omega)
      rw [show b - 1 - (b - 1 - r) = r by omega] at h2
      omega
    · rw [Prop61.rowCount_eq_zero fun c hc h => hr (by have := (hsub v c hc).2; omega),
        Prop61.rowCount_eq_zero fun c hc h => hr (by have := (hsub v c hc).2; omega)]
  have hpos : ∀ r : ℤ, (κ v).boxY a ≤ r → r < (κ v).boxY a + a → 0 < rowCount (t v) r :=
    fun r h1 h2 => Prop61.rowCount_pos_iff.2 ⟨_, hspine r h1 h2⟩
  have hin : ∀ r : ℤ, 0 < rowCount (t v) r → (κ v).boxY a ≤ r ∧ r < (κ v).boxY a + a := by
    intro r hr
    obtain ⟨x, hx⟩ := Prop61.rowCount_pos_iff.1 hr
    have hmem : r ∈ ySpan (t v) := mem_ySpan.2 ⟨_, hx, _, hx, le_rfl, le_rfl⟩
    rw [hspan, Finset.mem_Ico] at hmem
    exact hmem
  have hlow := hin (b - 1 - (κ v).boxY a)
    (hsymm ((κ v).boxY a) ▸ hpos _ le_rfl (by omega))
  have hhigh := hin (b - 1 - ((κ v).boxY a + a - 1))
    (hsymm ((κ v).boxY a + a - 1) ▸ hpos _ (by omega) (by omega))
  have h2y : 2 * (κ v).boxY a = b - a := by omega
  refine ⟨h2y, fun x => ?_⟩
  rw [← F.vertical_rowCount hvs x, ← F.vertical_rowCount hvs (a - 1 - x), hsymm]
  congr 1
  unfold GridIso.boxY at h2y
  split_ifs at h2y ⊢ <;> omega

/-- Proposition 61, step (3), columns. Source: `report-4.md`, Proposition 61 (3)
(line 584): counting the columns of `R`, the columns of `box(V)` are symmetric
under `x -> a - 1 - x`, so the far column of `V` has as many cells as its spine:
`rho(d - 1) = a`, and `T` contains row `d - 1` of `R`. -/
theorem proposition61_cols {a b d : ℤ} {t : Fin 3 → Finset Cell} {i₀ i₁ : Fin 3}
    {κ : Fin 3 → GridIso} (H : TypeH2 a b d t i₀ i₁ κ) {v : Fin 3} (hv₀ : v ≠ i₀)
    (hv₁ : v ≠ i₁) :
    ∀ x : ℤ, 0 ≤ x → x < a → (x, d - 1) ∈ t i₀ := by
  have F := H.frame
  have hsub : ∀ i, ∀ c ∈ t i, (0 ≤ c.1 ∧ c.1 < a) ∧ 0 ≤ c.2 ∧ c.2 < b := fun i c hc =>
    mem_R.1 (F.isTiling.subset_R i hc)
  obtain ⟨ha, hb⟩ := F.two_le
  obtain ⟨hd, -⟩ := F.two_le_d
  have hvs := H.vert v hv₀ hv₁
  obtain ⟨-, hspan, -, ⟨hx0, hxa⟩, -⟩ := F.vertical_spine hvs
  have hmu := (proposition61_rows H hv₀ hv₁).2
  -- `T'` has `mu(x)` cells in column `x`
  have htop : ∀ x : ℤ, colCount (t i₁) x = colCount (t i₀) x := by
    intro x
    rw [H.top_colCount x]
    split_ifs
    · exact (hmu x).symm
    · rfl
  -- the columns of `V` are symmetric under `x -> a - 1 - x`
  have hcol : ∀ x : ℤ, 0 ≤ x → x < a → 2 * colCount (t i₀) x + colCount (t v) x = b := by
    intro x h0 h1
    have h := sum_colCount_of_cover t F.disjoint F.cover (by omega) h0 h1
    rw [Prop61.sum_fin_three (fun i => colCount (t i) x) H.ne hv₀ hv₁] at h
    simp only [htop x] at h
    omega
  have hsymm : ∀ x : ℤ, 0 ≤ x → x < a → colCount (t v) x = colCount (t v) (a - 1 - x) := by
    intro x h0 h1
    have e1 := hcol x h0 h1
    have e2 := hcol (a - 1 - x) (by omega) (by omega)
    have e3 := hmu x
    omega
  have hin : ∀ x : ℤ, 0 < colCount (t v) x → (κ v).boxX d ≤ x ∧ x < (κ v).boxX d + d := by
    intro x hx
    obtain ⟨y, hy⟩ := Prop61.colCount_pos_iff.1 hx
    have hmem : x ∈ xSpan (t v) := mem_xSpan.2 ⟨_, hy, _, hy, le_rfl, le_rfl⟩
    rw [hspan, Finset.mem_Ico] at hmem
    exact hmem
  -- every column of `box(V)` is the image of a row of `box(T)`, and holds a cell
  have hdist : ∀ j : ℤ, 0 ≤ j → j < d →
      0 < colCount (t v) ((if (κ v).negX then -j else j) + (κ v).shift.1) := by
    intro j h0 h1
    rw [F.vertical_colCount hvs j]
    exact Prop61.rowCount_pos_iff.2 (F.exists_in_row h0 h1)
  have hzero := hdist 0 le_rfl (by omega)
  have hfar := hdist (d - 1) (by omega) (by omega)
  have hin' : ∀ x : ℤ, 0 < colCount (t v) x →
      (κ v).boxX d ≤ a - 1 - x ∧ a - 1 - x < (κ v).boxX d + d := by
    intro x hx
    have hx' := hin x hx
    refine hin _ ?_
    rw [← hsymm x (by omega) (by omega)]
    exact hx
  have hkey : rowCount (t i₀) (d - 1) = rowCount (t i₀) 0 := by
    have hzin := hin _ hzero
    have hfin := hin _ hfar
    have hzin' := hin' _ hzero
    have hfin' := hin' _ hfar
    rw [← F.vertical_colCount hvs (d - 1), ← F.vertical_colCount hvs 0,
      hsymm ((if (κ v).negX then -(d - 1) else d - 1) + (κ v).shift.1) (by omega) (by omega)]
    congr 1
    unfold GridIso.boxX at hzin hfin hzin' hfin' hx0 hxa
    split_ifs at hzin hfin hzin' hfin' hx0 hxa ⊢ <;> omega
  refine Prop61.full_of_le_rowCount (by omega) (fun x hx => (hsub i₀ _ hx).1) ?_
  rw [hkey]
  exact Prop61.le_rowCount_of_full (by omega) F.row0

/-- Proposition 61, step (4), the end. Source: `report-4.md`, Proposition 61 (4)
(line 585): if `T` contains row `d - 1`, then `T'` contains row `b - d`, the
vertical tile lies in the rows `[d, b - d)`, and `T` is its box. -/
theorem proposition61_end {a b d : ℤ} {t : Fin 3 → Finset Cell} {i₀ i₁ : Fin 3}
    {κ : Fin 3 → GridIso} (H : TypeH2 a b d t i₀ i₁ κ) {v : Fin 3} (hv₀ : v ≠ i₀)
    (hv₁ : v ≠ i₁) (hfull : ∀ x : ℤ, 0 ≤ x → x < a → (x, d - 1) ∈ t i₀) : False := by
  have F := H.frame
  obtain ⟨hd2, hda, hab⟩ := H.bounds hv₀ hv₁
  have hvs := H.vert v hv₀ hv₁
  obtain ⟨hspine, -, hspan, ⟨hx0, hxa⟩, hy1, hyb⟩ := F.vertical_spine hvs
  -- the spine column of `V` is a column of `R`
  have hc : 0 ≤ (κ v).shift.1 ∧ (κ v).shift.1 < a := by
    have h := mem_R.1 (F.isTiling.subset_R v (hspine _ le_rfl (by omega)))
    exact h.1
  -- `T'` contains row `b - d`
  have hfull' : ∀ x : ℤ, 0 ≤ x → x < a → (x, b - d) ∈ t i₁ := by
    intro x h0 h1
    rw [H.top_mem, show b - 1 - (b - d) = d - 1 by omega]
    split_ifs
    · exact hfull _ (by omega) (by omega)
    · exact hfull _ h0 h1
  -- the rows `d - 1` and `b - d` hold no spine cell of `V`
  have hno : ¬ ((κ v).boxY a ≤ d - 1 ∧ d - 1 < (κ v).boxY a + a) := fun h =>
    Finset.disjoint_left.1 (F.disjoint v i₀ hv₀) (hspine _ h.1 h.2) (hfull _ hc.1 hc.2)
  have hno' : ¬ ((κ v).boxY a ≤ b - d ∧ b - d < (κ v).boxY a + a) := fun h =>
    Finset.disjoint_left.1 (F.disjoint v i₁ hv₁) (hspine _ h.1 h.2) (hfull' _ hc.1 hc.2)
  -- so `V` lies in the rows `[d, b - d)`
  have hlow : d ≤ (κ v).boxY a ∧ (κ v).boxY a + a ≤ b - d := by omega
  refine F.nonrect (Finset.Subset.antisymm (subset_boundingBox _) ?_)
  rintro ⟨x, y⟩ hxy
  rw [mem_boundingBox, F.cols, F.rows, Finset.mem_Ico, Finset.mem_Ico] at hxy
  obtain ⟨⟨h0, h1⟩, h2, h3⟩ := hxy
  obtain ⟨i, hi⟩ := F.isTiling.exists_tile
    (mem_R.2 ⟨⟨h0, h1⟩, h2, by dsimp only at h3 ⊢; omega⟩)
  rcases Prop61.fin_three_cases H.ne hv₀ hv₁ i with rfl | rfl | rfl
  · exact hi
  · exfalso
    rw [H.top_mem] at hi
    have hmem : b - 1 - y ∈ ySpan (t i₀) := mem_ySpan.2 ⟨_, hi, _, hi, le_rfl, le_rfl⟩
    rw [F.rows, Finset.mem_Ico] at hmem
    dsimp only at h3
    omega
  · exfalso
    have hmem : y ∈ ySpan (t i) := mem_ySpan.2 ⟨_, hi, _, hi, le_rfl, le_rfl⟩
    rw [hspan, Finset.mem_Ico] at hmem
    dsimp only at h3
    omega

/-- Proposition 61. Source: `report-4.md`, section 8, Proposition 61 (line 579):

> No rectangle R(a, b) has a 3-copy tiling by a non-rectangular polyomino in which, in
> the setting of Lemma 4, T contains row 0, a second tile T' is horizontal with spine
> row b - 1, and the third tile V is vertical.
-/
theorem proposition61 {a b d : ℤ} {t : Fin 3 → Finset Cell} {i₀ i₁ : Fin 3}
    {κ : Fin 3 → GridIso} (H : TypeH2 a b d t i₀ i₁ κ) : False := by
  have hv : ∃ v : Fin 3, v ≠ i₀ ∧ v ≠ i₁ := by
    have hne := H.ne
    revert hne
    fin_cases i₀ <;> fin_cases i₁ <;> decide
  obtain ⟨v, hv₀, hv₁⟩ := hv
  exact proposition61_end H hv₀ hv₁ (proposition61_cols H hv₀ hv₁)

/-! ## Theorem 62 -/

/-- Theorem 62 (three copies): the internal statement behind the frozen
`theorem62_no_three_copy_tiling`. Source: `report-4.md`, section 8, Theorem 62
(line 589):

> No rectangle is tiled by exactly three congruent non-rectangular polyominoes (grid
> isometries, reflections included).

Proof (line 591): thin rectangles; the four corner cells lie in three tiles, so a
tile holds two of them; after an isometry it contains row 0; Lemmas 4 and 5 with
`k = 3` leave type H1 (Proposition 27) and type H2 (Proposition 61). -/
theorem three_copy (P : Finset Cell) (hP : IsPolyomino P)
    (hnr : ¬ IsRectangular P) (a b : ℤ) (t : Fin 3 → Finset Cell) :
    ¬ IsTiling P a b t := by
  intro ht
  obtain ⟨ha, hb⟩ := ht.two_le hP hnr (by norm_num)
  have hex : ∀ j : Fin 4, ∃ i, corner a b j ∈ t i := fun j =>
    ht.exists_tile (corner_mem_R (by omega) (by omega) j)
  choose f hf using hex
  obtain ⟨j, j', hjj', hff⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have hj' : corner a b j' ∈ t (f j) := by
    rw [hff]
    exact hf j'
  obtain ⟨a', b', t', ht', hrow⟩ :=
    row_tiling_of_two_corners P hP 3 (by norm_num) a b ha hb t ht (f j) j j' hjj' (hf j) hj'
  rcases theorem6_three P hP hnr a' b' t' ht' (f j) hrow with ⟨d, κ, H⟩ | ⟨d, κ, i₁, H⟩
  · exact H.proposition27
  · exact proposition61 H

end PolyominoOddOrder
