module

public import PolyominoOddOrder.Corners

/-!
# Spines, horizontal and vertical tiles, blocks (`Spine.lean`)

Blueprint unit S. Lemmas 4 and 5 and Theorem 6 of `report.md` section 2 and
Lemma 9 of `report-2.md` section 1, in coordinates.

**The setting as data.** The reports choose isometries `g_T`, `g_i` with
`T = g_T(P)`, `T_i = g_i(P)` and call `g_i(g_T^{-1}(row 0))` the spine of `T_i`.
Here `κ i` stands for `g_i g_T^{-1}`: the tile `t i` is the image of the tile
`T = t i₀` on row 0 under `κ i`, and `κ i₀` is the identity. Then:

* `T_i` is *vertical* exactly when `(κ i).swap = true`, *horizontal* when it is
  `false` (`report-2.md`, Lemma 9: "The 8 symmetries of the square either keep
  both axis directions or exchange them");
* the spine of a vertical tile is the column `(κ i).shift.1`, and the cell
  `(x, j)` of `T` goes to the cell at distance `j` from the spine in the row
  `(κ i).shift.2 + x` (order kept, `negY = false`) or `(κ i).shift.2 - x`
  (order reversed, `negY = true`); the box lies to the right of the spine
  (*right-type*, `negX = false`) or to the left (*left-type*, `negX = true`);
* the spine of a horizontal tile is the row `(κ i).shift.2`, and the tile is
  *up-type* (`negY = false`) or *down-type* (`negY = true`).

So every count of the reports about a tile (`u[x]`, `v[y]`, spine column, box,
"keeps the order") is a statement about the three switches and the shift of
`κ i` and about `T`.

Sources: `report.md` section 2, Lemma 4 (lines 170-200), Lemma 5 (lines 202-230),
Theorem 6 (lines 232-276); `report-2.md` section 1, Lemma 9 (lines 33-49).
Commit `e5ca51d`.
-/

@[expose] public section

namespace PolyominoOddOrder

/-! ## Coordinates of a tile that exchanges the axis directions -/

namespace GridIso

/-- The image of a cell under an isometry that exchanges the axis directions. -/
theorem apply_of_swap {g : GridIso} (h : g.swap = true) (c : Cell) :
    g.apply c =
      ((if g.negX then -c.2 else c.2) + g.shift.1, (if g.negY then -c.1 else c.1) + g.shift.2) := by
  simp [apply, h]

/-- The image of a cell under an isometry that keeps the axis directions. -/
theorem apply_of_not_swap {g : GridIso} (h : g.swap = false) (c : Cell) :
    g.apply c =
      ((if g.negX then -c.1 else c.1) + g.shift.1, (if g.negY then -c.2 else c.2) + g.shift.2) := by
  simp [apply, h]

/-- The first column of the box of a vertical tile whose box is `d` wide: the spine
column for a right-type tile, `d - 1` columns to its left for a left-type tile
(`x_i` of `report-2.md`, Theorem 10, Step 1). -/
def boxX (g : GridIso) (d : ℤ) : ℤ :=
  if g.negX then g.shift.1 - (d - 1) else g.shift.1

/-- The first row of the box of a vertical tile whose box is `a` high (`y_i` of
`report-4.md`, Lemma 24). -/
def boxY (g : GridIso) (a : ℤ) : ℤ :=
  if g.negY then g.shift.2 - (a - 1) else g.shift.2

end GridIso

/-- `e < e'` are neighbours in the finite set `E`: no element of `E` lies strictly
between them. The blocks of `report.md`, Lemma 5 (b), and of `report-2.md`,
Theorem 10, Step 3, are the intervals `[e, e')` between neighbours. -/
def Consecutive (E : Finset ℤ) (e e' : ℤ) : Prop :=
  e ∈ E ∧ e' ∈ E ∧ e < e' ∧ ∀ m ∈ E, m ≤ e ∨ e' ≤ m

/-- Counting cells of an image by a condition that the isometry carries back. -/
private theorem card_filter_image (g : GridIso) (S : Finset Cell) (p q : Cell → Prop)
    [DecidablePred p] [DecidablePred q] (h : ∀ c, q (g.apply c) ↔ p c) :
    ((S.image g.apply).filter q).card = (S.filter p).card := by
  rw [Finset.filter_image, Finset.card_image_of_injective _ g.apply_injective]
  congr 1
  exact Finset.filter_congr fun c _ => h c

/-! ## The setting of Lemma 4 -/

/-- The setting of `report.md`, Lemma 4 (lines 172-176), with the isometries
chosen:

> Suppose P is not rectangular and a tile T contains row 0. Let box(T) = [0, a) x [0, d).
> Then d >= 2. Choose the isometry g_T with T = g_T(P) and put s_0 = g_T^{-1}(row 0): a
> full side of box(P), of a cells, contained in P. For each tile T_i = g_i(P) define its
> *spine* g_i(s_0)

`t i₀` is `T`; `κ i` is `g_i g_T^{-1}`. -/
structure Frame (a b d : ℤ) {k : ℕ} (t : Fin k → Finset Cell) (i₀ : Fin k)
    (κ : Fin k → GridIso) : Prop where
  /-- Distinct tiles share no cell. -/
  disjoint : ∀ i j, i ≠ j → Disjoint (t i) (t j)
  /-- The tiles together are `R a b`. -/
  cover : Finset.univ.biUnion t = R a b
  /-- `T` is a polyomino. -/
  poly : IsPolyomino (t i₀)
  /-- `T` is not rectangular. -/
  nonrect : ¬ IsRectangular (t i₀)
  /-- `T` contains row 0. -/
  row0 : ∀ x : ℤ, 0 ≤ x → x < a → (x, 0) ∈ t i₀
  /-- `box(T)` has the rows `[0, d)`. -/
  rows : ySpan (t i₀) = Finset.Ico 0 d
  /-- Every tile is the image of `T` under its isometry. -/
  image : ∀ i, t i = (t i₀).image (κ i).apply
  /-- The isometry of `T` itself is the identity. -/
  base : κ i₀ = GridIso.one

namespace Frame

variable {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell} {i₀ : Fin k} {κ : Fin k → GridIso}

/-- A frame is a tiling by its tile on row 0. -/
theorem isTiling (F : Frame a b d t i₀ κ) : IsTiling (t i₀) a b t :=
  ⟨fun i => ⟨κ i, (F.image i).symm⟩, F.disjoint, F.cover⟩

/-- A cell is in `t i` exactly when its preimage under `κ i` is in `T`. -/
theorem mem_tile_iff (F : Frame a b d t i₀ κ) (i : Fin k) (c : Cell) :
    c ∈ t i ↔ (κ i).inv.apply c ∈ t i₀ := by
  rw [F.image i, GridIso.mem_image_iff]

/-! ### Working lemmas of this file -/

/-- The rectangle of a frame is not empty. -/
private theorem size_pos (F : Frame a b d t i₀ κ) : 0 < a ∧ 0 < b :=
  F.isTiling.pos F.poly (Fin.pos i₀)

/-- Coordinates of a cell of a tile. -/
private theorem cell_bounds (F : Frame a b d t i₀ κ) {i : Fin k} {c : Cell} (hc : c ∈ t i) :
    (0 ≤ c.1 ∧ c.1 < a) ∧ 0 ≤ c.2 ∧ c.2 < b :=
  mem_R.1 (F.isTiling.subset_R i hc)

/-- The place of a cell of `T` in the tile `t i`. -/
private theorem apply_mem_iff (F : Frame a b d t i₀ κ) (i : Fin k) (c : Cell) :
    (κ i).apply c ∈ t i ↔ c ∈ t i₀ := by
  rw [F.mem_tile_iff, GridIso.inv_apply_apply]

/-- Every cell of the tile `t i` is the place of a cell of `T`. -/
private theorem exists_apply_eq (F : Frame a b d t i₀ κ) {i : Fin k} {c : Cell}
    (hc : c ∈ t i) : ∃ e ∈ t i₀, (κ i).apply e = c := by
  rw [F.image i] at hc
  exact Finset.mem_image.1 hc

/-- The cells of `T` lie in the rows `[0, d)`. -/
private theorem row_bounds (F : Frame a b d t i₀ κ) {c : Cell} (hc : c ∈ t i₀) :
    0 ≤ c.2 ∧ c.2 < d := by
  have h : c.2 ∈ ySpan (t i₀) := mem_ySpan.2 ⟨c, hc, c, hc, le_rfl, le_rfl⟩
  rwa [F.rows, Finset.mem_Ico] at h

/-- Two tiles that share a cell are the same tile. -/
private theorem eq_of_mem (F : Frame a b d t i₀ κ) {i j : Fin k} {c : Cell} (hi : c ∈ t i)
    (hj : c ∈ t j) : i = j :=
  F.isTiling.tile_unique hi hj

/-- The spine row of `T` itself is row 0. -/
private theorem base_shift (F : Frame a b d t i₀ κ) : (κ i₀).shift.2 = 0 := by
  rw [F.base]
  rfl

/-- `T` itself is horizontal. -/
private theorem base_swap (F : Frame a b d t i₀ κ) : (κ i₀).swap = false := by
  rw [F.base]
  rfl

/-- Every tiling in which a tile contains row 0 has a frame. Source: `report.md`,
Lemma 4, first paragraph. -/
theorem exists_of_row {P : Finset Cell} (hP : IsPolyomino P) (hnr : ¬ IsRectangular P)
    (ht : IsTiling P a b t) (hrow : ∀ x : ℤ, 0 ≤ x → x < a → (x, 0) ∈ t i₀) :
    ∃ (d : ℤ) (κ : Fin k → GridIso), Frame a b d t i₀ κ := by
  choose g hg using ht.congruent
  have hpos := ht.pos hP (Fin.pos i₀)
  have hpoly := ht.tile_isPolyomino hP i₀
  obtain ⟨lo, hi, -, hspan, ⟨x0, hx0⟩, -⟩ := ySpan_eq_Icc hpoly.1
  have hlo : lo = 0 := by
    have h0 : ((0, 0) : Cell) ∈ t i₀ := hrow 0 le_rfl hpos.1
    have h1 : (0 : ℤ) ∈ ySpan (t i₀) := mem_ySpan.2 ⟨_, h0, _, h0, le_rfl, le_rfl⟩
    rw [hspan, Finset.mem_Icc] at h1
    have h2 := mem_R.1 (ht.subset_R i₀ hx0)
    dsimp only at h2
    omega
  refine ⟨hi + 1, fun i => if i = i₀ then GridIso.one else (g i).comp (g i₀).inv,
    ht.disjoint, ht.cover, hpoly, ht.tile_not_isRectangular hnr i₀, hrow, ?_, ?_, by simp⟩
  · rw [hspan, hlo]
    ext y
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  · intro i
    by_cases h : i = i₀
    · have h1 : GridIso.one.apply = fun c => c := funext GridIso.one_apply
      rw [ite_eq_left h, h1, Finset.image_id', h]
    · rw [ite_eq_right h, GridIso.image_comp, ← hg i₀, GridIso.image_inv_image, hg i]

/-- In a frame `a, b >= 2` (thin rectangles). -/
theorem two_le (F : Frame a b d t i₀ κ) : 2 ≤ a ∧ 2 ≤ b := by
  exact F.isTiling.two_le F.poly F.nonrect (Fin.pos i₀)

/-- `box(T)` has the columns `[0, a)`. -/
theorem cols (F : Frame a b d t i₀ κ) : xSpan (t i₀) = Finset.Ico 0 a := by
  refine Finset.Subset.antisymm (xSpan_subset_of_subset_R (F.isTiling.subset_R i₀)) ?_
  intro x hx
  rw [Finset.mem_Ico] at hx
  have h := F.row0 x hx.1 hx.2
  exact mem_xSpan.2 ⟨_, h, _, h, le_rfl, le_rfl⟩

/-- Lemma 4, first claim: `2 <= d` (and `d <= b`). Source: `report.md`, Lemma 4,
proof: "If d = 1 then T is row 0, a rectangle, so P is rectangular; hence d >= 2." -/
theorem two_le_d (F : Frame a b d t i₀ κ) : 2 ≤ d ∧ d ≤ b := by
  have hpos := F.size_pos
  have h0 := F.row_bounds (F.row0 0 le_rfl hpos.1)
  dsimp only at h0
  constructor
  · by_contra hlt
    have hd1 : d = 1 := by omega
    apply F.nonrect
    refine Finset.Subset.antisymm (subset_boundingBox _) ?_
    rintro ⟨x, y⟩ hc
    rw [mem_boundingBox, F.cols, F.rows, Finset.mem_Ico, Finset.mem_Ico] at hc
    dsimp only at hc
    obtain rfl : y = 0 := by omega
    exact F.row0 x hc.1.1 hc.1.2
  · have h1 : d - 1 ∈ ySpan (t i₀) := by
      rw [F.rows, Finset.mem_Ico]
      omega
    have h2 := ySpan_subset_of_subset_R (F.isTiling.subset_R i₀) h1
    rw [Finset.mem_Ico] at h2
    omega

/-- `T` has a cell in every row of its box ("T is connected and its box is tight",
`report-4.md`, Proposition 61). -/
theorem exists_in_row (F : Frame a b d t i₀ κ) {y : ℤ} (hy0 : 0 ≤ y) (hyd : y < d) :
    ∃ x : ℤ, (x, y) ∈ t i₀ := by
  have h : y ∈ ySpan (t i₀) := by
    rw [F.rows, Finset.mem_Ico]
    exact ⟨hy0, hyd⟩
  obtain ⟨c, hc, e, he, h1, h2⟩ := mem_ySpan.1 h
  exact F.poly.2.exists_in_row hc he h1 h2

/-! ## Lemma 4 -/

/-- Lemma 4 (a), horizontal tiles. Source: `report.md`, Lemma 4 (a) (lines 178-181):

> (a) The spine of a horizontal tile is a full row of R. Distinct horizontal tiles have
> distinct spine rows. A horizontal tile with spine row r lies either in rows
> r, ..., r + d - 1 (*up-type*) or in rows r - d + 1, ..., r (*down-type*), and has a
> cell outside row r.

The spine row is `(κ i).shift.2`; the tile contains it, its columns are placed
by `x -> x` or `x -> a - 1 - x`, and its rows are on one side of the spine. -/
theorem horizontal_spine (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = false) :
    ((κ i).negX = false ∧ (κ i).shift.1 = 0 ∨ (κ i).negX = true ∧ (κ i).shift.1 = a - 1) ∧
      (0 ≤ (κ i).shift.2 ∧ (κ i).shift.2 < b) ∧
      (∀ x : ℤ, 0 ≤ x → x < a → (x, (κ i).shift.2) ∈ t i) ∧
      (∀ c ∈ t i, if (κ i).negY then (κ i).shift.2 - d < c.2 ∧ c.2 ≤ (κ i).shift.2
        else (κ i).shift.2 ≤ c.2 ∧ c.2 < (κ i).shift.2 + d) := by
  have hpos := F.size_pos
  have hA := F.cell_bounds ((F.apply_mem_iff i _).2 (F.row0 0 le_rfl hpos.1))
  have hB := F.cell_bounds ((F.apply_mem_iff i _).2 (F.row0 (a - 1) (by omega) (by omega)))
  simp only [GridIso.apply_of_not_swap hi, neg_zero, ite_self, zero_add] at hA hB
  have hfst : (κ i).negX = false ∧ (κ i).shift.1 = 0 ∨
      (κ i).negX = true ∧ (κ i).shift.1 = a - 1 := by
    cases hx : (κ i).negX <;> simp only [hx, Bool.false_eq_true, ite_true, ite_false] at hB
    · exact Or.inl ⟨rfl, by omega⟩
    · exact Or.inr ⟨rfl, by omega⟩
  refine ⟨hfst, hA.2, ?_, ?_⟩
  · intro x hx0 hxa
    rcases hfst with ⟨hx, hs⟩ | ⟨hx, hs⟩
    · have h := (F.apply_mem_iff i (x, 0)).2 (F.row0 x hx0 hxa)
      rwa [GridIso.apply_of_not_swap hi, hx, hs, ite_eq_right Bool.false_ne_true, neg_zero,
        ite_self, zero_add, add_zero] at h
    · have h := (F.apply_mem_iff i (a - 1 - x, 0)).2 (F.row0 (a - 1 - x) (by omega) (by omega))
      rwa [GridIso.apply_of_not_swap hi, hx, hs, ite_eq_left rfl, neg_zero, ite_self, zero_add,
        show -(a - 1 - x) + (a - 1) = x by ring] at h
  · intro c hc
    obtain ⟨e, he, rfl⟩ := F.exists_apply_eq hc
    have h := F.row_bounds he
    simp only [GridIso.apply_of_not_swap hi]
    cases (κ i).negY <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega

/-- Lemma 4 (a): distinct horizontal tiles have distinct spine rows. -/
theorem horizontal_spine_injective (F : Frame a b d t i₀ κ) {i j : Fin k}
    (hi : (κ i).swap = false) (hj : (κ j).swap = false)
    (h : (κ i).shift.2 = (κ j).shift.2) : i = j := by
  have hpos := F.size_pos
  have h1 := (F.horizontal_spine hi).2.2.1 0 le_rfl hpos.1
  have h2 := (F.horizontal_spine hj).2.2.1 0 le_rfl hpos.1
  rw [← h] at h2
  exact F.eq_of_mem h1 h2

/-- Lemma 4 (a): a horizontal tile reaches the row at distance `d - 1` from its
spine. -/
theorem horizontal_far_row (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = false) :
    ∃ x : ℤ, (x, (κ i).shift.2 + (if (κ i).negY then -(d - 1) else d - 1)) ∈ t i := by
  have hd := F.two_le_d
  obtain ⟨x, hx⟩ := F.exists_in_row (y := d - 1) (by omega) (by omega)
  have h := (F.apply_mem_iff i (x, d - 1)).2 hx
  rw [GridIso.apply_of_not_swap hi, add_comm _ (κ i).shift.2] at h
  exact ⟨_, h⟩

/-- Lemma 4 (b), vertical tiles. Source: `report.md`, Lemma 4 (b) (lines 183-184):

> (b) The spine of a vertical tile is a vertical segment of a cells, and its box has
> dimensions (d, a). If a vertical tile exists then d <= a <= b - 1.

The spine is the column `(κ i).shift.1` in the `a` rows of the box; the box is
`[boxX, boxX + d) x [boxY, boxY + a)`, inside `R a b` and above row 0. -/
theorem vertical_spine (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true) :
    (∀ y : ℤ, (κ i).boxY a ≤ y → y < (κ i).boxY a + a → ((κ i).shift.1, y) ∈ t i) ∧
      xSpan (t i) = Finset.Ico ((κ i).boxX d) ((κ i).boxX d + d) ∧
      ySpan (t i) = Finset.Ico ((κ i).boxY a) ((κ i).boxY a + a) ∧
      (0 ≤ (κ i).boxX d ∧ (κ i).boxX d + d ≤ a) ∧
      (1 ≤ (κ i).boxY a ∧ (κ i).boxY a + a ≤ b) := by
  have hpos := F.size_pos
  have hne : i ≠ i₀ := by
    rintro rfl
    rw [F.base_swap] at hi
    exact Bool.false_ne_true hi
  have hspine : ∀ y : ℤ, (κ i).boxY a ≤ y → y < (κ i).boxY a + a →
      ((κ i).shift.1, y) ∈ t i := by
    intro y h1 h2
    cases hy : (κ i).negY <;>
      simp only [GridIso.boxY, hy, Bool.false_eq_true, ite_true, ite_false] at h1 h2
    · have h := (F.apply_mem_iff i (y - (κ i).shift.2, 0)).2 (F.row0 _ (by omega) (by omega))
      rwa [GridIso.apply_of_swap hi, hy, ite_eq_right Bool.false_ne_true, neg_zero, ite_self,
        zero_add, sub_add_cancel] at h
    · have h := (F.apply_mem_iff i ((κ i).shift.2 - y, 0)).2 (F.row0 _ (by omega) (by omega))
      rwa [GridIso.apply_of_swap hi, hy, ite_eq_left rfl, neg_zero, ite_self, zero_add,
        show -((κ i).shift.2 - y) + (κ i).shift.2 = y by ring] at h
  have hxs : xSpan (t i) = Finset.Ico ((κ i).boxX d) ((κ i).boxX d + d) := by
    rw [F.image i, xSpan_image, ite_eq_left hi, F.rows]
    ext x
    simp only [Finset.mem_image, Finset.mem_Ico, GridIso.boxX]
    constructor
    · rintro ⟨v, hv, rfl⟩
      cases (κ i).negX <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega
    · intro hx
      cases hn : (κ i).negX <;> simp only [hn, Bool.false_eq_true, ite_true, ite_false] at hx ⊢
      · exact ⟨x - (κ i).shift.1, by omega, by omega⟩
      · exact ⟨(κ i).shift.1 - x, by omega, by omega⟩
  have hys : ySpan (t i) = Finset.Ico ((κ i).boxY a) ((κ i).boxY a + a) := by
    rw [F.image i, ySpan_image, ite_eq_left hi, F.cols]
    ext y
    simp only [Finset.mem_image, Finset.mem_Ico, GridIso.boxY]
    constructor
    · rintro ⟨v, hv, rfl⟩
      cases (κ i).negY <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega
    · intro hy
      cases hn : (κ i).negY <;> simp only [hn, Bool.false_eq_true, ite_true, ite_false] at hy ⊢
      · exact ⟨y - (κ i).shift.2, by omega, by omega⟩
      · exact ⟨(κ i).shift.2 - y, by omega, by omega⟩
  have hd := F.two_le_d
  have hx0 : (κ i).boxX d ∈ Finset.Ico 0 a := by
    apply xSpan_subset_of_subset_R (F.isTiling.subset_R i)
    rw [hxs, Finset.mem_Ico]
    omega
  have hx1 : (κ i).boxX d + d - 1 ∈ Finset.Ico 0 a := by
    apply xSpan_subset_of_subset_R (F.isTiling.subset_R i)
    rw [hxs, Finset.mem_Ico]
    omega
  have hy0 := F.cell_bounds (hspine ((κ i).boxY a) le_rfl (by omega))
  have hy1 := F.cell_bounds (hspine ((κ i).boxY a + a - 1) (by omega) (by omega))
  rw [Finset.mem_Ico] at hx0 hx1
  dsimp only at hy0 hy1
  refine ⟨hspine, hxs, hys, by omega, ?_, by omega⟩
  by_contra hlt
  have hz : (κ i).boxY a = 0 := by omega
  have h1 := hspine 0 (by omega) (by omega)
  exact hne (F.eq_of_mem h1 (F.row0 _ hy0.1.1 hy0.1.2))

/-- Lemma 4 (b): if a vertical tile exists then `d <= a <= b - 1`. -/
theorem vertical_bounds (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true) :
    d ≤ a ∧ a ≤ b - 1 := by
  obtain ⟨-, -, -, h1, h2⟩ := F.vertical_spine hi
  omega

/-- Lemma 4 (c). Source: `report.md`, Lemma 4 (c) (lines 186-187):

> (c) Every tile other than a horizontal tile H with spine row r lies entirely in rows
> above r or entirely in rows below r.
-/
theorem separated_by_spine_row (F : Frame a b d t i₀ κ) {i j : Fin k}
    (hi : (κ i).swap = false) (hij : j ≠ i) :
    (∀ c ∈ t j, c.2 < (κ i).shift.2) ∨ (∀ c ∈ t j, (κ i).shift.2 < c.2) := by
  have hno : ∀ x : ℤ, (x, (κ i).shift.2) ∉ t j := by
    intro x hx
    have hb := F.cell_bounds hx
    exact hij (F.eq_of_mem hx ((F.horizontal_spine hi).2.2.1 x hb.1.1 hb.1.2))
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨c, hc, h1⟩, e, he, h2⟩ := hcon
  obtain ⟨x, hx⟩ :=
    (F.isTiling.tile_isPolyomino F.poly j).2.exists_in_row he hc h2 h1
  exact hno x hx

/-! ## Lemma 9: cross-sections travel with the spine -/

/-- Lemma 9, rows. Source: `report-2.md`, section 1, Lemma 9 (lines 35-39): for a
vertical tile, the number of its cells in the row that is the image of column `x`
of `T` equals the number of cells of `T` in column `x`. -/
theorem vertical_rowCount (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true)
    (x : ℤ) :
    rowCount (t i) ((if (κ i).negY then -x else x) + (κ i).shift.2) = colCount (t i₀) x := by
  unfold rowCount colCount
  rw [F.image i, card_filter_image (κ i) (t i₀) (fun c => c.1 = x)]
  intro c
  rw [GridIso.apply_of_swap hi]
  cases (κ i).negY <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega

/-- Lemma 9, columns: the column of a vertical tile at distance `j` from its spine
has as many cells as row `j` of `T` ("row j of box(T) to the column of box(V) at
distance j from c", `report-4.md`, Proposition 61 (1)). -/
theorem vertical_colCount (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true)
    (j : ℤ) :
    colCount (t i) ((if (κ i).negX then -j else j) + (κ i).shift.1) = rowCount (t i₀) j := by
  unfold rowCount colCount
  rw [F.image i, card_filter_image (κ i) (t i₀) (fun c => c.2 = j)]
  intro c
  rw [GridIso.apply_of_swap hi]
  cases (κ i).negX <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega

/-- Lemma 9, cells: the cell `(x, j)` of `T` and its place in a vertical tile. -/
theorem vertical_mem (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true)
    (x j : ℤ) :
    ((if (κ i).negX then -j else j) + (κ i).shift.1,
        (if (κ i).negY then -x else x) + (κ i).shift.2) ∈ t i ↔ (x, j) ∈ t i₀ := by
  rw [← F.apply_mem_iff i (x, j), GridIso.apply_of_swap hi]

/-! ## Lemma 5: clean lines and blocks -/

/-- The clean lines of Lemma 5 (a), with `0` and `b`: `y = r` for an up-type
horizontal tile with spine row `r`, `y = r + 1` for a down-type one. -/
def cleanLines (b : ℤ) {k : ℕ} (κ : Fin k → GridIso) : Finset ℤ :=
  insert 0 (insert b ((Finset.univ.filter fun i => (κ i).swap = false).image fun i =>
    if (κ i).negY then (κ i).shift.2 + 1 else (κ i).shift.2))

private theorem mem_cleanLines {c : ℤ} : c ∈ cleanLines b κ ↔ c = 0 ∨ c = b ∨
    ∃ i, (κ i).swap = false ∧
      (if (κ i).negY then (κ i).shift.2 + 1 else (κ i).shift.2) = c := by
  simp [cleanLines]

/-- The clean lines of `cleanLines` lie in `[0, b]`. -/
private theorem cleanLines_bounds (F : Frame a b d t i₀ κ) {c : ℤ}
    (hc : c ∈ cleanLines b κ) : 0 ≤ c ∧ c ≤ b := by
  have hpos := F.size_pos
  rcases mem_cleanLines.1 hc with rfl | rfl | ⟨i, hi, rfl⟩
  · omega
  · omega
  · have h := (F.horizontal_spine hi).2.1
    split <;> omega

private theorem up_mem_cleanLines {i : Fin k} (hi : (κ i).swap = false)
    (hn : (κ i).negY = false) : (κ i).shift.2 ∈ cleanLines b κ :=
  mem_cleanLines.2 (Or.inr (Or.inr ⟨i, hi, by simp [hn]⟩))

private theorem down_mem_cleanLines {i : Fin k} (hi : (κ i).swap = false)
    (hn : (κ i).negY = true) : (κ i).shift.2 + 1 ∈ cleanLines b κ :=
  mem_cleanLines.2 (Or.inr (Or.inr ⟨i, hi, by simp [hn]⟩))

/-- Lemma 5 (a). Source: `report.md`, Lemma 5 (lines 204-208): a line of
`cleanLines` is clean: "no tile has cells both in rows below c and in rows at or
above c". -/
theorem clean_line (F : Frame a b d t i₀ κ) {c : ℤ} (hc : c ∈ cleanLines b κ) (j : Fin k) :
    (∀ p ∈ t j, p.2 < c) ∨ (∀ p ∈ t j, c ≤ p.2) := by
  rcases mem_cleanLines.1 hc with rfl | rfl | ⟨i, hi, rfl⟩
  · exact Or.inr fun p hp => (F.cell_bounds hp).2.1
  · exact Or.inl fun p hp => (F.cell_bounds hp).2.2
  · by_cases hj : j = i
    · subst hj
      have h := (F.horizontal_spine hi).2.2.2
      cases hn : (κ j).negY <;>
        simp only [hn, Bool.false_eq_true, ite_true, ite_false] at h ⊢
      · exact Or.inr fun p hp => (h p hp).1
      · exact Or.inl fun p hp => by have := (h p hp).2; omega
    · rcases F.separated_by_spine_row hi hj with h | h
      · exact Or.inl fun p hp => by have := h p hp; split <;> omega
      · exact Or.inr fun p hp => by have := h p hp; split <;> omega

/-- Lemma 5 (b). Source: `report.md`, Lemma 5 (b) (lines 210-214):

> Each *block* B_j, the rows c_{j-1}, ..., c_j - 1 of R, is a rectangle
> with a columns that is a union of tiles. It contains at least 2 tiles. It contains at
> most one up-type horizontal tile, whose spine is its bottom row, and at most one
> down-type horizontal tile, whose spine is its top row; all its other tiles are
> vertical.

`I` is the set of tiles lying in the block `[c, c')`. -/
theorem block (F : Frame a b d t i₀ κ) {c c' : ℤ} (hcc' : Consecutive (cleanLines b κ) c c')
    (I : Finset (Fin k)) (hI : ∀ i, i ∈ I ↔ ∀ p ∈ t i, c ≤ p.2 ∧ p.2 < c') :
    2 ≤ I.card ∧
      (∀ i ∈ I, (κ i).swap = false → (κ i).negY = false → (κ i).shift.2 = c) ∧
      (∀ i ∈ I, (κ i).swap = false → (κ i).negY = true → (κ i).shift.2 = c' - 1) ∧
      (I.filter fun i => (κ i).swap = false).card ≤ 2 := by
  obtain ⟨hc, hc', hlt, hcons⟩ := hcc'
  have hpos := F.size_pos
  have hr := F.cleanLines_bounds hc
  have hr' := F.cleanLines_bounds hc'
  have key : ∀ j p, p ∈ t j → c ≤ p.2 → p.2 < c' → j ∈ I := by
    intro j p hp h1 h2
    rw [hI]
    intro q hq
    rcases F.clean_line hc j with h | h
    · have := h p hp
      omega
    rcases F.clean_line hc' j with h' | h'
    · exact ⟨h q hq, h' q hq⟩
    · have := h' p hp
      omega
  have up : ∀ i ∈ I, (κ i).swap = false → (κ i).negY = false → (κ i).shift.2 = c := by
    intro i hi hs hn
    have hcell := (hI i).1 hi _ ((F.horizontal_spine hs).2.2.1 0 le_rfl hpos.1)
    dsimp only at hcell
    rcases hcons _ (up_mem_cleanLines hs hn) with h | h <;> omega
  have down : ∀ i ∈ I, (κ i).swap = false → (κ i).negY = true →
      (κ i).shift.2 = c' - 1 := by
    intro i hi hs hn
    have hcell := (hI i).1 hi _ ((F.horizontal_spine hs).2.2.1 0 le_rfl hpos.1)
    dsimp only at hcell
    rcases hcons _ (down_mem_cleanLines hs hn) with h | h <;> omega
  refine ⟨?_, up, down, ?_⟩
  · by_contra hlt2
    have hone : I.card ≤ 1 := by omega
    have hcell : ((0, c) : Cell) ∈ R a b := mem_R.2 ⟨⟨le_rfl, hpos.1⟩, hr.1, by
      dsimp only
      omega⟩
    obtain ⟨j, hj⟩ := F.isTiling.exists_tile hcell
    have hjI := key j _ hj le_rfl hlt
    apply F.isTiling.tile_not_isRectangular F.nonrect j
    refine Finset.Subset.antisymm (subset_boundingBox _) ?_
    rintro ⟨x, y⟩ hp
    rw [mem_boundingBox] at hp
    have hx := Finset.mem_Ico.1 (xSpan_subset_of_subset_R (F.isTiling.subset_R j) hp.1)
    obtain ⟨e, he, f, hf, h1, h2⟩ := mem_ySpan.1 hp.2
    have he' := ((hI j).1 hjI e he).1
    have hf' := ((hI j).1 hjI f hf).2
    dsimp only at hx h1 h2
    obtain ⟨m, hm⟩ := F.isTiling.exists_tile (c := (x, y))
      (mem_R.2 ⟨hx, by dsimp only; omega, by dsimp only; omega⟩)
    have hmI := key m _ hm (by dsimp only; omega) (by dsimp only; omega)
    rwa [Finset.card_le_one.1 hone m hmI j hjI] at hm
  · have h2 : (Finset.univ : Finset Bool).card = 2 := rfl
    rw [← h2]
    refine Finset.card_le_card_of_injOn (fun i => (κ i).negY) (fun _ _ => Finset.mem_univ _) ?_
    intro i hi j hj hij
    have hi' := Finset.mem_filter.1 (Finset.mem_coe.1 hi)
    have hj' := Finset.mem_filter.1 (Finset.mem_coe.1 hj)
    dsimp only at hij
    apply F.horizontal_spine_injective hi'.2 hj'.2
    cases hn : (κ i).negY
    · rw [up i hi'.1 hi'.2 hn, up j hj'.1 hj'.2 (hij ▸ hn)]
    · rw [down i hi'.1 hi'.2 hn, down j hj'.1 hj'.2 (hij ▸ hn)]

private theorem exists_next (F : Frame a b d t i₀ κ) {c : ℤ}
    (hc : c ∈ (cleanLines b κ).erase b) : ∃ c', Consecutive (cleanLines b κ) c c' := by
  rw [Finset.mem_erase] at hc
  have hcb := F.cleanLines_bounds hc.2
  have hb : b ∈ (cleanLines b κ).filter fun m => c < m :=
    Finset.mem_filter.2 ⟨mem_cleanLines.2 (Or.inr (Or.inl rfl)), by omega⟩
  refine ⟨((cleanLines b κ).filter fun m => c < m).min' ⟨b, hb⟩, hc.2, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.1 (Finset.min'_mem _ ⟨b, hb⟩)).1
  · exact (Finset.mem_filter.1 (Finset.min'_mem _ ⟨b, hb⟩)).2
  · intro m hm
    by_cases h : m ≤ c
    · exact Or.inl h
    · exact Or.inr (Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hm, by omega⟩))

/-- Lemma 5 (c), first part: `k >= 2t`, with `t` the number of blocks. Source:
`report.md`, Lemma 5 (c) (line 216). -/
theorem two_mul_blocks_le (F : Frame a b d t i₀ κ) :
    2 * ((cleanLines b κ).card - 1) ≤ k := by
  classical
  choose! nxt hnxt using fun c (hc : c ∈ (cleanLines b κ).erase b) => F.exists_next hc
  set I : ℤ → Finset (Fin k) := fun c =>
    Finset.univ.filter fun i => ∀ p ∈ t i, c ≤ p.2 ∧ p.2 < nxt c with hI
  have hmem : ∀ c i, i ∈ I c ↔ ∀ p ∈ t i, c ≤ p.2 ∧ p.2 < nxt c := by
    intro c i
    simp [hI]
  have hlt : ∀ c ∈ (cleanLines b κ).erase b, ∀ c' ∈ (cleanLines b κ).erase b, c < c' →
      Disjoint (I c) (I c') := by
    intro c hc c' hc' h
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨p, hp⟩ := (F.isTiling.tile_isPolyomino F.poly i).1
    have h1 := (hmem c i).1 hi p hp
    have h2 := (hmem c' i).1 hi' p hp
    rcases (hnxt c hc).2.2.2 c' (Finset.mem_of_mem_erase hc') with h3 | h3 <;> omega
  have hdisj : ∀ c ∈ (cleanLines b κ).erase b, ∀ c' ∈ (cleanLines b κ).erase b, c ≠ c' →
      Disjoint (I c) (I c') := by
    intro c hc c' hc' h
    rcases lt_or_gt_of_ne h with h | h
    · exact hlt c hc c' hc' h
    · exact (hlt c' hc' c hc h).symm
  have hsum : ((cleanLines b κ).erase b).card • 2 ≤
      ∑ c ∈ (cleanLines b κ).erase b, (I c).card :=
    Finset.card_nsmul_le_sum _ _ _ fun c hc => (F.block (hnxt c hc) (I c) (hmem c)).1
  rw [← Finset.card_biUnion hdisj, Finset.card_erase_of_mem
    (mem_cleanLines.2 (Or.inr (Or.inl rfl)))] at hsum
  have hk : (((cleanLines b κ).erase b).biUnion I).card ≤ k := by
    simpa using Finset.card_le_univ (((cleanLines b κ).erase b).biUnion I)
  rw [smul_eq_mul] at hsum
  omega

end Frame

/-! ## The two one-block types -/

/-- Type H1: one tile on row 0 and every other tile vertical. This is the setting
of `report-2.md` section 1 and of `report-4.md` section 1 (line 37), and case
(II.2) of Theorem 6 when `k = 5`. -/
structure TypeH1 (a b d : ℤ) {k : ℕ} (t : Fin k → Finset Cell) (i₀ : Fin k)
    (κ : Fin k → GridIso) : Prop where
  /-- The setting of Lemma 4. -/
  frame : Frame a b d t i₀ κ
  /-- Every tile other than `T` is vertical. -/
  vert : ∀ i, i ≠ i₀ → (κ i).swap = true

/-- Type H2: the tile `T` on row 0, a down-type horizontal tile `T' = t i₁` with
spine row `b - 1`, and every other tile vertical. This is case (II.3) of Theorem 6
when `k = 5` (`report-4.md`, section 5d, line 311) and the setting of
Proposition 61 when `k = 3`. -/
structure TypeH2 (a b d : ℤ) {k : ℕ} (t : Fin k → Finset Cell) (i₀ i₁ : Fin k)
    (κ : Fin k → GridIso) : Prop where
  /-- The setting of Lemma 4. -/
  frame : Frame a b d t i₀ κ
  /-- `T'` is not `T`. -/
  ne : i₁ ≠ i₀
  /-- `T'` is horizontal. -/
  horiz : (κ i₁).swap = false
  /-- `T'` is down-type. -/
  down : (κ i₁).negY = true
  /-- The spine of `T'` is row `b - 1`. -/
  top : (κ i₁).shift.2 = b - 1
  /-- Every other tile is vertical. -/
  vert : ∀ i, i ≠ i₀ → i ≠ i₁ → (κ i).swap = true

namespace TypeH2

variable {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell} {i₀ i₁ : Fin k} {κ : Fin k → GridIso}

/-- The isometry `G` carrying `T` to `T'` is the reflection `F` of `R a b`
(`negX = false`) or its half turn `H` (`negX = true`). Source: `report-4.md`,
Proposition 61 (1) ("G(x, y) = (x, b - 1 - y) or (a - 1 - x, b - 1 - y)") and
section 5e (line 343). -/
theorem mirror_form (H : TypeH2 a b d t i₀ i₁ κ) :
    (κ i₁).negX = false ∧ (κ i₁).shift.1 = 0 ∨ (κ i₁).negX = true ∧ (κ i₁).shift.1 = a - 1 :=
  (H.frame.horizontal_spine H.horiz).1

/-- The cells of `T'` in terms of `T`. -/
theorem top_mem (H : TypeH2 a b d t i₀ i₁ κ) (x y : ℤ) :
    (x, y) ∈ t i₁ ↔ ((if (κ i₁).negX then a - 1 - x else x), b - 1 - y) ∈ t i₀ := by
  have e : (κ i₁).apply ((if (κ i₁).negX then a - 1 - x else x), b - 1 - y) = (x, y) := by
    rw [GridIso.apply_of_not_swap H.horiz, H.down, H.top]
    rcases H.mirror_form with ⟨h, hs⟩ | ⟨h, hs⟩ <;> rw [h, hs] <;>
      simp only [Bool.false_eq_true, ite_true, ite_false, Prod.mk.injEq] <;> omega
  rw [← H.frame.apply_mem_iff i₁, e]

/-- `T'` has in row `r` as many cells as `T` in row `b - 1 - r`. Source:
`report-4.md`, Proposition 61 (1). -/
theorem top_rowCount (H : TypeH2 a b d t i₀ i₁ κ) (r : ℤ) :
    rowCount (t i₁) r = rowCount (t i₀) (b - 1 - r) := by
  unfold rowCount
  rw [H.frame.image i₁, card_filter_image (κ i₁) (t i₀) (fun c => c.2 = b - 1 - r)]
  intro c
  rw [GridIso.apply_of_not_swap H.horiz, H.down, H.top]
  simp only [ite_true]
  omega

/-- `T'` has in column `x` as many cells as `T` in column `x` (`G = F`) or in
column `a - 1 - x` (`G = H`). -/
theorem top_colCount (H : TypeH2 a b d t i₀ i₁ κ) (x : ℤ) :
    colCount (t i₁) x = colCount (t i₀) (if (κ i₁).negX then a - 1 - x else x) := by
  unfold colCount
  rw [H.frame.image i₁, card_filter_image (κ i₁) (t i₀)
    (fun c => c.1 = if (κ i₁).negX then a - 1 - x else x)]
  intro c
  rw [GridIso.apply_of_not_swap H.horiz]
  rcases H.mirror_form with ⟨h, hs⟩ | ⟨h, hs⟩ <;> rw [h, hs] <;>
    simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega

/-- In type H2 with a vertical tile, `2 <= d <= a <= b - 2`. Source: `report.md`,
Theorem 6 (II.3): "the spine of a vertical tile avoids rows 0 and b - 1, so
a <= b - 2". -/
theorem bounds (H : TypeH2 a b d t i₀ i₁ κ) {i : Fin k} (hi₀ : i ≠ i₀) (hi₁ : i ≠ i₁) :
    2 ≤ d ∧ d ≤ a ∧ a ≤ b - 2 := by
  have F := H.frame
  have hi := H.vert i hi₀ hi₁
  have hb := F.vertical_bounds hi
  obtain ⟨hspine, -, -, hx, hy⟩ := F.vertical_spine hi
  have hpos := F.size_pos
  refine ⟨F.two_le_d.1, hb.1, ?_⟩
  by_contra hlt
  have h1 := hspine (b - 1) (by omega) (by omega)
  have h2 := F.cell_bounds h1
  have h3 := (F.horizontal_spine H.horiz).2.2.1 (κ i).shift.1 h2.1.1 h2.1.2
  rw [H.top] at h3
  exact hi₁ (F.eq_of_mem h1 h3)

end TypeH2

/-! ## The mirror image of a setting -/

/-- Column counts of the mirror image. -/
theorem colCount_image_flipX (a : ℤ) (S : Finset Cell) (x : ℤ) :
    colCount (S.image (GridIso.flipX a).apply) x = colCount S (a - 1 - x) := by
  unfold colCount
  rw [card_filter_image (GridIso.flipX a) S (fun c => c.1 = a - 1 - x)]
  intro c
  rw [GridIso.flipX_apply]
  dsimp only
  omega

/-- Row counts of the mirror image. -/
theorem rowCount_image_flipX (a : ℤ) (S : Finset Cell) (y : ℤ) :
    rowCount (S.image (GridIso.flipX a).apply) y = rowCount S y := by
  unfold rowCount
  rw [card_filter_image (GridIso.flipX a) S (fun c => c.2 = y)]
  intro c
  rw [GridIso.flipX_apply]

/-- The mirror image `x -> a - 1 - x` of a frame is a frame; a vertical tile keeps
its spine side of the wall (`boxX` goes to `a - d - boxX`), and both `negX` and
`negY` change. Source: the reports' "mirror image" and "by the mirror image take
..." (`report-4.md`, sections 4 to 5h). -/
theorem Frame.mirror {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell} {i₀ : Fin k}
    {κ : Fin k → GridIso} (F : Frame a b d t i₀ κ) :
    Frame a b d (fun i => (t i).image (GridIso.flipX a).apply) i₀
      (fun i => (GridIso.flipX a).comp ((κ i).comp (GridIso.flipX a))) := by
  have ht := F.isTiling.flipX
  refine ⟨ht.disjoint, ht.cover, GridIso.isPolyomino_image _ F.poly, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => F.nonrect ((isRectangular_image_iff _ _).1 h)
  · intro x hx0 hxa
    refine Finset.mem_image.2 ⟨(a - 1 - x, 0), F.row0 _ (by omega) (by omega), ?_⟩
    rw [GridIso.flipX_apply]
    exact Prod.ext (by dsimp only; omega) rfl
  · rw [ySpan_image, ← F.rows]
    simp [GridIso.flipX]
  · intro i
    rw [GridIso.image_comp, GridIso.image_comp,
      ← GridIso.image_comp (GridIso.flipX a) (GridIso.flipX a)]
    have h1 : ((GridIso.flipX a).comp (GridIso.flipX a)).apply = fun c => c := by
      funext c
      rw [GridIso.comp_apply, GridIso.flipX_apply, GridIso.flipX_apply]
      exact Prod.ext (by dsimp only; omega) rfl
    rw [h1, Finset.image_id', ← F.image i]
  · rw [F.base]
    simp [GridIso.comp, GridIso.one, GridIso.flipX, GridIso.apply]

/-- The mirror image of a tiling of type H1 is of type H1. -/
theorem TypeH1.mirror {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell} {i₀ : Fin k}
    {κ : Fin k → GridIso} (H : TypeH1 a b d t i₀ κ) :
    TypeH1 a b d (fun i => (t i).image (GridIso.flipX a).apply) i₀
      (fun i => (GridIso.flipX a).comp ((κ i).comp (GridIso.flipX a))) := by
  refine ⟨H.frame.mirror, fun i hi => ?_⟩
  simp [GridIso.comp, GridIso.flipX, H.vert i hi]

/-- The mirror image of a tiling of type H2 is of type H2. -/
theorem TypeH2.mirror {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell} {i₀ i₁ : Fin k}
    {κ : Fin k → GridIso} (H : TypeH2 a b d t i₀ i₁ κ) :
    TypeH2 a b d (fun i => (t i).image (GridIso.flipX a).apply) i₀ i₁
      (fun i => (GridIso.flipX a).comp ((κ i).comp (GridIso.flipX a))) := by
  refine ⟨H.frame.mirror, H.ne, ?_, ?_, ?_, fun i hi hi' => ?_⟩
  · simp [GridIso.comp, GridIso.flipX, H.horiz]
  · simp [GridIso.comp, GridIso.flipX, H.horiz, H.down]
  · simp [GridIso.comp, GridIso.flipX, GridIso.apply, H.horiz, H.down, H.top]
  · simp [GridIso.comp, GridIso.flipX, H.vert i hi hi']

/-! ## Theorem 6 -/

/-- One block: the tiling is of type H1 or of type H2. Source: `report.md`, Theorem 6,
proof, the case `t = 1` (lines 270-273). -/
private theorem Frame.one_block {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell} {i₀ : Fin k}
    {κ : Fin k → GridIso} (F : Frame a b d t i₀ κ)
    (hcard : (Frame.cleanLines b κ).card ≤ 2) :
    TypeH1 a b d t i₀ κ ∨ ∃ i₁, TypeH2 a b d t i₀ i₁ κ := by
  have hpos := F.size_pos
  have hsub : ({0, b} : Finset ℤ) ⊆ Frame.cleanLines b κ := by
    intro m hm
    rw [Finset.mem_insert, Finset.mem_singleton] at hm
    exact Frame.mem_cleanLines.2 (by tauto)
  have hL := Finset.eq_of_subset_of_card_le hsub
    (by rw [Finset.card_pair (by omega)]; exact hcard)
  have hcons : Consecutive (Frame.cleanLines b κ) 0 b := by
    rw [← hL]
    refine ⟨by simp, by simp, hpos.2, fun m hm => ?_⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hm
    omega
  obtain ⟨-, hup, hdown, -⟩ := F.block hcons Finset.univ
    (fun i => ⟨fun _ p hp => (F.cell_bounds hp).2, fun _ => Finset.mem_univ _⟩)
  have hupT : ∀ i, (κ i).swap = false → (κ i).negY = false → i = i₀ := by
    intro i hs hn
    apply F.horizontal_spine_injective hs F.base_swap
    rw [hup i (Finset.mem_univ _) hs hn, F.base_shift]
  by_cases h : ∃ i, i ≠ i₀ ∧ (κ i).swap = false
  · obtain ⟨i₁, hne, hs⟩ := h
    have hn : (κ i₁).negY = true := by
      cases hn : (κ i₁).negY
      · exact absurd (hupT i₁ hs hn) hne
      · rfl
    refine Or.inr ⟨i₁, F, hne, hs, hn, hdown i₁ (Finset.mem_univ _) hs hn, ?_⟩
    intro i h0 h1
    cases hsi : (κ i).swap
    · exfalso
      cases hni : (κ i).negY
      · exact h0 (hupT i hsi hni)
      · apply h1
        apply F.horizontal_spine_injective hsi hs
        rw [hdown i (Finset.mem_univ _) hsi hni, hdown i₁ (Finset.mem_univ _) hs hn]
    · rfl
  · push Not at h
    refine Or.inl ⟨F, fun i hi => ?_⟩
    simpa using h i hi

/-- Theorem 6, case (II), for five tiles. Source: `report.md`, Theorem 6
(lines 240-251) and its proof (lines 263-276): if a tile contains row 0, then
(II.1) a horizontal line splits the rectangle and three of the tiles tile one of
the two parts, or (II.2) the tiling is of type H1, or (II.3) of type H2. In
(II.1) the three tiles, moved down if they are the upper part, are a 3-copy
tiling of a rectangle `R a c` by `P`. Proof idea: `Frame.exists_of_row`, then
`5 >= 2t` (`Frame.two_mul_blocks_le`) leaves `t = 1` or `t = 2`; for `t = 2` the
blocks hold 2 and 3 tiles (`Frame.block`, `IsTiling.lower_part`,
`IsTiling.upper_part`); for `t = 1` `Frame.block` gives H1 or H2. -/
theorem theorem6_five (P : Finset Cell) (hP : IsPolyomino P) (hnr : ¬ IsRectangular P)
    (a b : ℤ) (t : Fin 5 → Finset Cell) (ht : IsTiling P a b t) (i₀ : Fin 5)
    (hrow : ∀ x : ℤ, 0 ≤ x → x < a → (x, 0) ∈ t i₀) :
    (∃ (c : ℤ) (t' : Fin 3 → Finset Cell), IsTiling P a c t') ∨
      (∃ (d : ℤ) (κ : Fin 5 → GridIso), TypeH1 a b d t i₀ κ) ∨
      (∃ (d : ℤ) (κ : Fin 5 → GridIso) (i₁ : Fin 5), TypeH2 a b d t i₀ i₁ κ) := by
  classical
  obtain ⟨d, κ, F⟩ := Frame.exists_of_row hP hnr ht hrow
  have hblocks := F.two_mul_blocks_le
  by_cases h2 : (Frame.cleanLines b κ).card ≤ 2
  · rcases F.one_block h2 with h | ⟨i₁, h⟩
    · exact Or.inr (Or.inl ⟨d, κ, h⟩)
    · exact Or.inr (Or.inr ⟨d, κ, i₁, h⟩)
  refine Or.inl ?_
  have hpos := F.size_pos
  have h0L : (0 : ℤ) ∈ Frame.cleanLines b κ := Frame.mem_cleanLines.2 (Or.inl rfl)
  have hbL : b ∈ Frame.cleanLines b κ := Frame.mem_cleanLines.2 (Or.inr (Or.inl rfl))
  -- the third clean line
  obtain ⟨c, hc⟩ : ∃ c, ((Frame.cleanLines b κ).erase 0).erase b = {c} := by
    rw [← Finset.card_eq_one, Finset.card_erase_of_mem
      (Finset.mem_erase.2 ⟨by omega, hbL⟩), Finset.card_erase_of_mem h0L]
    omega
  have hmem : ∀ m, m ∈ Frame.cleanLines b κ ↔ m = 0 ∨ m = b ∨ m = c := by
    intro m
    constructor
    · intro hm
      by_cases hm0 : m = 0
      · exact Or.inl hm0
      by_cases hmb : m = b
      · exact Or.inr (Or.inl hmb)
      have : m ∈ ((Frame.cleanLines b κ).erase 0).erase b :=
        Finset.mem_erase.2 ⟨hmb, Finset.mem_erase.2 ⟨hm0, hm⟩⟩
      rw [hc, Finset.mem_singleton] at this
      exact Or.inr (Or.inr this)
    · rintro (rfl | rfl | rfl)
      · exact h0L
      · exact hbL
      · have : m ∈ ((Frame.cleanLines b κ).erase 0).erase b := by
          rw [hc, Finset.mem_singleton]
        exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase this)
  have hcL : c ∈ Frame.cleanLines b κ := (hmem c).2 (Or.inr (Or.inr rfl))
  have hcne : c ≠ b ∧ c ≠ 0 := by
    have : c ∈ ((Frame.cleanLines b κ).erase 0).erase b := by
      rw [hc, Finset.mem_singleton]
    rw [Finset.mem_erase, Finset.mem_erase] at this
    exact ⟨this.1, this.2.1⟩
  have hcb := F.cleanLines_bounds hcL
  have hlow : Consecutive (Frame.cleanLines b κ) 0 c :=
    ⟨h0L, hcL, by omega, fun m hm => by rcases (hmem m).1 hm with h | h | h <;> omega⟩
  have hhigh : Consecutive (Frame.cleanLines b κ) c b :=
    ⟨hcL, hbL, by omega, fun m hm => by rcases (hmem m).1 hm with h | h | h <;> omega⟩
  set I : Finset (Fin 5) := Finset.univ.filter fun i => ∀ p ∈ t i, p.2 < c with hI
  have hImem : ∀ i, i ∈ I ↔ ∀ p ∈ t i, p.2 < c := by
    intro i
    simp [hI]
  have hIc : ∀ i, i ∈ Iᶜ ↔ ∀ p ∈ t i, c ≤ p.2 := by
    intro i
    rw [Finset.mem_compl, hImem]
    obtain ⟨p, hp⟩ := (ht.tile_isPolyomino hP i).1
    constructor
    · intro h
      rcases F.clean_line hcL i with h' | h'
      · exact absurd h' h
      · exact h'
    · intro h h'
      have h1 := h p hp
      have h2 := h' p hp
      omega
  have hIcard := (F.block hlow I fun i => by
    rw [hImem]
    exact ⟨fun h p hp => ⟨(F.cell_bounds hp).2.1, h p hp⟩, fun h p hp => (h p hp).2⟩).1
  have hIccard := (F.block hhigh Iᶜ fun i => by
    rw [hIc]
    exact ⟨fun h p hp => ⟨h p hp, (F.cell_bounds hp).2.2⟩, fun h p hp => (h p hp).1⟩).1
  have hsum := Finset.card_add_card_compl I
  rw [Fintype.card_fin] at hsum
  have hcase : I.card = 3 ∨ Iᶜ.card = 3 := by omega
  rcases hcase with h3 | h3
  · refine ⟨c, _, ht.lower_part (I.orderEmbOfFin h3) (I.orderEmbOfFin h3).injective
      hcb.1 hcb.2 (fun j => (hImem _).1 (Finset.orderEmbOfFin_mem I h3 j)) ?_⟩
    intro i hi
    rw [← hIc, Finset.mem_compl]
    intro hiI
    have hr : i ∈ Set.range (I.orderEmbOfFin h3) := by
      rw [Finset.range_orderEmbOfFin]
      exact hiI
    obtain ⟨j, hj⟩ := hr
    exact hi j hj
  · refine ⟨b - c, _, ht.upper_part (Iᶜ.orderEmbOfFin h3) (Iᶜ.orderEmbOfFin h3).injective
      hcb.1 hcb.2 (fun j => (hIc _).1 (Finset.orderEmbOfFin_mem Iᶜ h3 j)) ?_⟩
    intro i hi
    rw [← hImem]
    by_contra hiI
    have hr : i ∈ Set.range (Iᶜ.orderEmbOfFin h3) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.2 (Finset.mem_compl.2 hiI)
    obtain ⟨j, hj⟩ := hr
    exact hi j hj

/-- Theorem 6, case (II), for three tiles. Source: `report-4.md`, proof of
Theorem 62 (line 591): "Lemmas 4 and 5 apply with k = 3: 3 >= 2t gives t = 1, the
one block is R, it holds T, at most one down-type horizontal tile, with spine row
b - 1, and at least one vertical tile." -/
theorem theorem6_three (P : Finset Cell) (hP : IsPolyomino P) (hnr : ¬ IsRectangular P)
    (a b : ℤ) (t : Fin 3 → Finset Cell) (ht : IsTiling P a b t) (i₀ : Fin 3)
    (hrow : ∀ x : ℤ, 0 ≤ x → x < a → (x, 0) ∈ t i₀) :
    (∃ (d : ℤ) (κ : Fin 3 → GridIso), TypeH1 a b d t i₀ κ) ∨
      (∃ (d : ℤ) (κ : Fin 3 → GridIso) (i₁ : Fin 3), TypeH2 a b d t i₀ i₁ κ) := by
  obtain ⟨d, κ, F⟩ := Frame.exists_of_row hP hnr ht hrow
  have hblocks := F.two_mul_blocks_le
  rcases F.one_block (by omega) with h | ⟨i₁, h⟩
  · exact Or.inl ⟨d, κ, h⟩
  · exact Or.inr ⟨d, κ, i₁, h⟩

end PolyominoOddOrder
