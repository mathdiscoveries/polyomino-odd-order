module

public import PolyominoOddOrder.H1

/-!
# Type H1: the top row and the bottom (`H1Top.lean`)

Blueprint unit HB. Type H1 for a general number of tiles, second part: Lemma 25,
Corollary 26, Propositions 27 and 28, Corollary 29 (`report-4.md` section 4) and
Lemma 30 (section 5). Proposition 27 (no 3-copy tiling of type H1) is what the
three-copy theorem needs from here.

Notation as in `H1.lean`. Commit `e5ca51d`.
-/

@[expose] public section

namespace PolyominoOddOrder

/-! ## Working lemmas of this file -/

/-- A row without cells of `S` counts 0. -/
private theorem rowCount_of_empty {S : Finset Cell} {y : ℤ} (h : ∀ x : ℤ, (x, y) ∉ S) :
    rowCount S y = 0 := by
  unfold rowCount
  rw [Finset.filter_eq_empty_iff.2, Finset.card_empty, Nat.cast_zero]
  rintro ⟨x, y'⟩ hc rfl
  exact h x hc

/-- A column met in the rows `[0, s)` exactly counts `s`. -/
private theorem colCount_of_interval {S : Finset Cell} {x s : ℤ} (hs : 0 ≤ s)
    (h : ∀ y : ℤ, (x, y) ∈ S ↔ 0 ≤ y ∧ y < s) : colCount S x = s := by
  have hcol : (S.filter fun c => c.1 = x) = ({x} : Finset ℤ) ×ˢ Finset.Ico 0 s := by
    ext ⟨x', y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, rfl⟩
      exact ⟨rfl, (h y).1 hc⟩
    · rintro ⟨rfl, hy⟩
      exact ⟨(h y).2 hy, rfl⟩
  unfold colCount
  rw [hcol, Finset.card_product, Finset.card_singleton, one_mul, Int.card_Ico]
  omega

/-- Two blocks that share a column are the same block. -/
private theorem consecutive_unique {E : Finset ℤ} {e e' f f' x : ℤ} (h : Consecutive E e e')
    (h' : Consecutive E f f') (hex : e ≤ x) (hxe : x < e') (hfx : f ≤ x) (hxf : x < f') :
    e = f ∧ e' = f' := by
  have h1 := h.2.2.2 f h'.1
  have h2 := h.2.2.2 f' h'.2.1
  have h3 := h'.2.2.2 e h.1
  have h4 := h'.2.2.2 e' h.2.1
  omega

/-- A number of `E` below another one is followed by a neighbour. -/
private theorem exists_consecutive_right {E : Finset ℤ} {e m : ℤ} (he : e ∈ E) (hm : m ∈ E)
    (hlt : e < m) : ∃ e', Consecutive E e e' := by
  have hne : m ∈ E.filter fun n => e < n := Finset.mem_filter.2 ⟨hm, hlt⟩
  refine ⟨(E.filter fun n => e < n).min' ⟨m, hne⟩, he, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.1 (Finset.min'_mem _ ⟨m, hne⟩)).1
  · exact (Finset.mem_filter.1 (Finset.min'_mem _ ⟨m, hne⟩)).2
  · intro n hn
    by_cases h : n ≤ e
    · exact Or.inl h
    · exact Or.inr (Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hn, by omega⟩))

/-- A number of `E` above another one follows a neighbour. -/
private theorem exists_consecutive_left {E : Finset ℤ} {e m : ℤ} (he : e ∈ E) (hm : m ∈ E)
    (hlt : m < e) : ∃ e', Consecutive E e' e := by
  have hne : m ∈ E.filter fun n => n < e := Finset.mem_filter.2 ⟨hm, hlt⟩
  refine ⟨(E.filter fun n => n < e).max' ⟨m, hne⟩, ?_, he, ?_, ?_⟩
  · exact (Finset.mem_filter.1 (Finset.max'_mem _ ⟨m, hne⟩)).1
  · exact (Finset.mem_filter.1 (Finset.max'_mem _ ⟨m, hne⟩)).2
  · intro n hn
    by_cases h : e ≤ n
    · exact Or.inr h
    · exact Or.inl (Finset.le_max' _ _ (Finset.mem_filter.2 ⟨hn, by omega⟩))

private theorem mem_colMarks {a : ℤ} {k : ℕ} {κ : Fin k → GridIso} {J : Finset (Fin k)}
    {e : ℤ} : e ∈ colMarks a κ J ↔ e = 0 ∨ e = a ∨
      ∃ i ∈ J, (if (κ i).negX then (κ i).shift.1 + 1 else (κ i).shift.1) = e := by
  simp [colMarks]

namespace Frame

variable {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell} {i₀ : Fin k} {κ : Fin k → GridIso}

/-- Coordinates of a cell of a tile. -/
private theorem cell_in_R (F : Frame a b d t i₀ κ) {i : Fin k} {x y : ℤ} (hc : (x, y) ∈ t i) :
    (0 ≤ x ∧ x < a) ∧ 0 ≤ y ∧ y < b :=
  mem_R.1 (F.isTiling.subset_R i hc)

/-- The cells of `T` lie in the rows `[0, d)`. -/
private theorem cell_low (F : Frame a b d t i₀ κ) {x y : ℤ} (hc : (x, y) ∈ t i₀) :
    0 ≤ y ∧ y < d := by
  have h : y ∈ ySpan (t i₀) := mem_ySpan.2 ⟨_, hc, _, hc, le_rfl, le_rfl⟩
  rwa [F.rows, Finset.mem_Ico] at h

/-- A vertical tile lies in its box. -/
private theorem cell_in_box (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true)
    {x y : ℤ} (hc : (x, y) ∈ t i) :
    ((κ i).boxX d ≤ x ∧ x < (κ i).boxX d + d) ∧
      (κ i).boxY a ≤ y ∧ y < (κ i).boxY a + a := by
  obtain ⟨-, hx, hy, -, -⟩ := F.vertical_spine hi
  have h1 : x ∈ xSpan (t i) := mem_xSpan.2 ⟨_, hc, _, hc, le_rfl, le_rfl⟩
  have h2 : y ∈ ySpan (t i) := mem_ySpan.2 ⟨_, hc, _, hc, le_rfl, le_rfl⟩
  rw [hx, Finset.mem_Ico] at h1
  rw [hy, Finset.mem_Ico] at h2
  exact ⟨h1, h2⟩

/-- Two tiles that share a cell are the same tile. -/
private theorem same_tile (F : Frame a b d t i₀ κ) {i j : Fin k} {c : Cell} (hi : c ∈ t i)
    (hj : c ∈ t j) : i = j :=
  F.isTiling.tile_unique hi hj

/-- Every cell of `R a b` is in a tile. -/
private theorem exists_tile_at (F : Frame a b d t i₀ κ) {x y : ℤ} (hx0 : 0 ≤ x) (hxa : x < a)
    (hy0 : 0 ≤ y) (hyb : y < b) : ∃ i, (x, y) ∈ t i :=
  F.isTiling.exists_tile (mem_R.2 ⟨⟨hx0, hxa⟩, hy0, hyb⟩)

/-- The marks of a family of vertical tiles lie in `[0, a]`. -/
private theorem colMarks_range (F : Frame a b d t i₀ κ) {J : Finset (Fin k)}
    (hJ : ∀ i ∈ J, (κ i).swap = true) {e : ℤ} (he : e ∈ colMarks a κ J) : 0 ≤ e ∧ e ≤ a := by
  have ha := F.two_le
  have hd := F.two_le_d
  rcases mem_colMarks.1 he with rfl | rfl | ⟨i, hi, rfl⟩
  · omega
  · omega
  · have hx := (F.vertical_spine (hJ i hi)).2.2.2.1
    unfold GridIso.boxX at hx
    cases hn : (κ i).negX <;>
      simp only [hn, Bool.false_eq_true, ite_true, ite_false] at hx ⊢ <;> omega

/-- The row of a vertical tile that is the image of column `x` of `T`, counted from
the first row of the box. -/
private theorem image_row (x : ℤ) (g : GridIso) (a : ℤ) :
    (if g.negY then -x else x) + g.shift.2 =
      g.boxY a + (if g.negY then a - 1 - x else x) := by
  unfold GridIso.boxY
  cases g.negY <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega

/-- If the row of a vertical tile that is the image of column `x` of `T` is full in
the box, then so is column `x` of `box(T)`. -/
private theorem column_of_row (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true)
    {x : ℤ} (h : ∀ z : ℤ, (κ i).boxX d ≤ z → z < (κ i).boxX d + d →
      (z, (κ i).boxY a + (if (κ i).negY then a - 1 - x else x)) ∈ t i)
    {j : ℤ} (hj0 : 0 ≤ j) (hjd : j < d) : (x, j) ∈ t i₀ := by
  rw [← F.vertical_mem hi x j, image_row x (κ i) a]
  apply h <;> unfold GridIso.boxX <;> cases (κ i).negX <;>
    simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega

/-- A vertical tile has at most `d` cells in a row. -/
private theorem vertical_rowCount_le (F : Frame a b d t i₀ κ) {i : Fin k}
    (hi : (κ i).swap = true) (y : ℤ) : rowCount (t i) y ≤ d := by
  have h : ((t i).filter fun c => c.2 = y).card ≤
      (Finset.Ico ((κ i).boxX d) ((κ i).boxX d + d)).card := by
    refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
    · rintro ⟨x, y'⟩ hc
      have hc' := Finset.mem_filter.1 (Finset.mem_coe.1 hc)
      exact Finset.mem_coe.2 (Finset.mem_Ico.2 (F.cell_in_box hi hc'.1).1)
    · rintro ⟨x, y₁⟩ h1 ⟨x', y₂⟩ h2 hx
      have h1' := (Finset.mem_filter.1 (Finset.mem_coe.1 h1)).2
      have h2' := (Finset.mem_filter.1 (Finset.mem_coe.1 h2)).2
      dsimp only at hx h1' h2'
      rw [hx, h1', h2']
  rw [Int.card_Ico] at h
  have hd := F.two_le_d
  unfold rowCount
  omega

/-- If only the vertical tiles of `S` have cells in a row, then `a <= |S| d`. -/
private theorem row_bound (F : Frame a b d t i₀ κ) (S : Finset (Fin k))
    (hS : ∀ i ∈ S, (κ i).swap = true) {y : ℤ} (hy0 : 0 ≤ y) (hyb : y < b)
    (h : ∀ i x, (x, y) ∈ t i → i ∈ S) : a ≤ S.card * d := by
  have hsum := sum_rowCount_of_cover t F.disjoint F.cover
    (by have := F.two_le; omega) hy0 hyb
  have h1 : ∑ i ∈ S, rowCount (t i) y = ∑ i, rowCount (t i) y :=
    Finset.sum_subset (Finset.subset_univ S)
      fun i _ hi => rowCount_of_empty fun x hx => hi (h i x hx)
  have h2 : ∑ i ∈ S, rowCount (t i) y ≤ S.card • d :=
    Finset.sum_le_card_nsmul _ _ _ fun i hi => F.vertical_rowCount_le (hS i hi) y
  rw [nsmul_eq_mul] at h2
  linarith

end Frame

namespace TypeH1

variable {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell} {i₀ : Fin k} {κ : Fin k → GridIso}

/-! ## Lemma 25: the top row -/

open Classical in
/-- The top tiles: the vertical tiles with a cell in row `b - 1`. Source:
`report-4.md`, section 4 (line 106). -/
noncomputable def topTiles (b : ℤ) {k : ℕ} (t : Fin k → Finset Cell) (i₀ : Fin k) :
    Finset (Fin k) :=
  Finset.univ.filter fun i => i ≠ i₀ ∧ ∃ x : ℤ, (x, b - 1) ∈ t i

private theorem mem_topTiles {i : Fin k} :
    i ∈ topTiles b t i₀ ↔ i ≠ i₀ ∧ ∃ x : ℤ, (x, b - 1) ∈ t i := by
  simp [topTiles]

/-- A top tile is vertical. -/
private theorem top_vert (H : TypeH1 a b d t i₀ κ) :
    ∀ i ∈ topTiles b t i₀, (κ i).swap = true :=
  fun i hi => H.vert i (mem_topTiles.1 hi).1

/-- A top tile has the rows `[b - a, b)`. -/
private theorem top_boxY (H : TypeH1 a b d t i₀ κ) {i : Fin k} (hi : i ∈ topTiles b t i₀) :
    (κ i).boxY a = b - a := by
  obtain ⟨hne, x, hx⟩ := mem_topTiles.1 hi
  have h1 := H.frame.cell_in_box (H.vert i hne) hx
  obtain ⟨-, -, -, -, -, h2⟩ := H.frame.vertical_spine (H.vert i hne)
  omega

/-- Lemma 25 (a). Source: `report-4.md`, Lemma 25 (a) (line 110): "Row b - 1 is
covered by top tiles. Distinct top tiles have distinct spine columns, and a top
tile lies entirely left or entirely right of the spine column of any other." A
top tile has the rows `[b - a, b)`. -/
theorem lemma25a (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) :
    (∀ x : ℤ, 0 ≤ x → x < a → ∃ i ∈ topTiles b t i₀, (x, b - 1) ∈ t i) ∧
      (∀ i ∈ topTiles b t i₀, (κ i).boxY a = b - a) ∧
      ∀ i ∈ topTiles b t i₀, ∀ j ∈ topTiles b t i₀, i ≠ j →
        (∀ c ∈ t j, c.1 < (κ i).shift.1) ∨ (∀ c ∈ t j, (κ i).shift.1 < c.1) := by
  have hb := H.bounds hk
  have F := H.frame
  refine ⟨?_, fun i hi => top_boxY H hi, ?_⟩
  · intro x hx0 hxa
    obtain ⟨i, hi⟩ := F.exists_tile_at hx0 hxa (y := b - 1) (by omega) (by omega)
    refine ⟨i, mem_topTiles.2 ⟨?_, x, hi⟩, hi⟩
    rintro rfl
    have := F.cell_low hi
    omega
  · intro i hi j hj hij
    have hyi := top_boxY H hi
    have hyj := top_boxY H hj
    have hno : ∀ y : ℤ, ((κ i).shift.1, y) ∉ t j := by
      intro y hy
      have h1 := F.cell_in_box (top_vert H j hj) hy
      exact hij (F.same_tile
        ((F.vertical_spine (top_vert H i hi)).1 y (by omega) (by omega)) hy)
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨c, hc, h1⟩, e, he, h2⟩ := hcon
    obtain ⟨y, hy⟩ := (F.isTiling.tile_isPolyomino F.poly j).2.exists_in_col he hc h2 h1
    exact hno y hy

/-- The marks of the top tiles lie in `[0, a]`. -/
private theorem top_marks (H : TypeH1 a b d t i₀ κ) {e : ℤ}
    (he : e ∈ colMarks a κ (topTiles b t i₀)) : 0 ≤ e ∧ e ≤ a :=
  H.frame.colMarks_range (top_vert H) he

/-- A top tile with a cell in a block lies in the block, with its spine in the first
column (right-type) or the last (left-type). -/
private theorem top_block (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) {e e' : ℤ}
    (hee' : Consecutive (colMarks a κ (topTiles b t i₀)) e e') {i : Fin k}
    (hi : i ∈ topTiles b t i₀) {x y : ℤ} (hc : (x, y) ∈ t i) (hex : e ≤ x) (hxe : x < e') :
    (e ≤ (κ i).boxX d ∧ (κ i).boxX d + d ≤ e') ∧ ((κ i).negX = false → (κ i).shift.1 = e) ∧
      ((κ i).negX = true → (κ i).shift.1 = e' - 1) := by
  obtain ⟨f, f', hff', h1, h2, h3⟩ := H.frame.column_blocks (topTiles b t i₀) (top_vert H)
    (H.lemma25a hk).2.2 i hi
  have hbox := (H.frame.cell_in_box (top_vert H i hi) hc).1
  obtain ⟨rfl, rfl⟩ := consecutive_unique hee' hff' hex hxe (by omega) (by omega)
  exact ⟨⟨h1, h2⟩, h3⟩

/-- The spine of a top tile whose box lies in a block. -/
private theorem top_block_spine (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) {e e' : ℤ}
    (hee' : Consecutive (colMarks a κ (topTiles b t i₀)) e e') {i : Fin k}
    (hi : i ∈ topTiles b t i₀) (hie : e ≤ (κ i).boxX d ∧ (κ i).boxX d + d ≤ e') :
    ((κ i).negX = false → (κ i).shift.1 = e) ∧ ((κ i).negX = true → (κ i).shift.1 = e' - 1) := by
  have ha := H.frame.two_le
  have hc := (H.frame.vertical_spine (top_vert H i hi)).1 ((κ i).boxY a) le_rfl (by omega)
  have hbox := (H.frame.cell_in_box (top_vert H i hi) hc).1
  exact (top_block H hk hee' hi hc (by omega) (by omega)).2

/-- Lemma 25 (b), last sentence: every block of the top tiles holds a top tile and
has at least `d` columns. Source: `report-4.md`, Lemma 25 (b) (line 111). The first
sentences of (b) are `Frame.column_blocks` with `J = topTiles`. -/
theorem lemma25b (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) {e e' : ℤ}
    (hee' : Consecutive (colMarks a κ (topTiles b t i₀)) e e') :
    d ≤ e' - e ∧ ∃ i ∈ topTiles b t i₀, e ≤ (κ i).boxX d ∧ (κ i).boxX d + d ≤ e' := by
  have h := top_marks H hee'.1
  have h' := top_marks H hee'.2.1
  have hlt := hee'.2.2.1
  obtain ⟨i, hi, hc⟩ := (H.lemma25a hk).1 e (by omega) (by omega)
  have hB := (top_block H hk hee' hi hc le_rfl hlt).1
  exact ⟨by omega, i, hi, hB⟩

/-- Lemma 25 (c). Source: `report-4.md`, Lemma 25 (c) (line 112): "A block with one
top tile W has exactly d columns, W contains the top row of the block, and T
contains a full vertical side of box(T)". -/
theorem lemma25c (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) {e e' : ℤ}
    (hee' : Consecutive (colMarks a κ (topTiles b t i₀)) e e') {w : Fin k}
    (hw : w ∈ topTiles b t i₀)
    (hone : ∀ i ∈ topTiles b t i₀, e ≤ (κ i).boxX d ∧ (κ i).boxX d + d ≤ e' → i = w) :
    e' - e = d ∧ (∀ x : ℤ, e ≤ x → x < e' → (x, b - 1) ∈ t w) ∧
      ((∀ y : ℤ, 0 ≤ y → y < d → (0, y) ∈ t i₀) ∨
        (∀ y : ℤ, 0 ≤ y → y < d → (a - 1, y) ∈ t i₀)) := by
  have hb := H.bounds hk
  have F := H.frame
  have h := top_marks H hee'.1
  have h' := top_marks H hee'.2.1
  have hlt := hee'.2.2.1
  obtain ⟨hd, w', hw', hwe⟩ := H.lemma25b hk hee'
  obtain rfl : w' = w := hone w' hw' hwe
  have htop : ∀ x : ℤ, e ≤ x → x < e' → (x, b - 1) ∈ t w' := by
    intro x h1 h2
    obtain ⟨i, hi, hc⟩ := (H.lemma25a hk).1 x (by omega) (by omega)
    rwa [hone i hi (top_block H hk hee' hi hc h1 h2).1] at hc
  have hwid : e' - e = d := by
    have h2 := F.cell_in_box (top_vert H w' hw) (htop e le_rfl hlt)
    have h3 := F.cell_in_box (top_vert H w' hw) (htop (e' - 1) (by omega) (by omega))
    omega
  refine ⟨hwid, htop, ?_⟩
  have hy := top_boxY H hw
  cases hn : (κ w').negY
  · refine Or.inr fun y hy0 hyd => F.column_of_row (top_vert H w' hw) ?_ hy0 hyd
    intro z hz1 hz2
    rw [hn, hy, ite_eq_right Bool.false_ne_true, show b - a + (a - 1) = b - 1 by ring]
    exact htop z (by omega) (by omega)
  · refine Or.inl fun y hy0 hyd => F.column_of_row (top_vert H w' hw) ?_ hy0 hyd
    intro z hz1 hz2
    rw [hn, hy, ite_eq_left rfl, show b - a + (a - 1 - 0) = b - 1 by ring]
    exact htop z (by omega) (by omega)

/-- Lemma 25 (d). Source: `report-4.md`, Lemma 25 (d) (line 113): "A block with two
top tiles has w columns with d + 1 <= w <= 2d." -/
theorem lemma25d (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) {e e' : ℤ}
    (hee' : Consecutive (colMarks a κ (topTiles b t i₀)) e e') {w w' : Fin k}
    (hw : w ∈ topTiles b t i₀) (hw' : w' ∈ topTiles b t i₀) (hww' : w ≠ w')
    (hwe : e ≤ (κ w).boxX d ∧ (κ w).boxX d + d ≤ e')
    (hw'e : e ≤ (κ w').boxX d ∧ (κ w').boxX d + d ≤ e') :
    d + 1 ≤ e' - e ∧ e' - e ≤ 2 * d := by
  have hb := H.bounds hk
  have F := H.frame
  have hJ := top_vert H
  have hsep := (H.lemma25a hk).2.2
  wlog hn : (κ w).negX = false generalizing w w'
  · have hn' : (κ w').negX = false := by
      by_contra h
      refine hww' (F.column_blocks_unique _ hJ hsep hee' hw hw' hwe hw'e ?_)
      rw [Bool.not_eq_false] at hn h
      rw [hn, h]
    exact this hw' hw hww'.symm hw'e hwe hn'
  have hn' : (κ w').negX = true := by
    by_contra h
    refine hww' (F.column_blocks_unique _ hJ hsep hee' hw hw' hwe hw'e ?_)
    rw [Bool.not_eq_true] at h
    rw [hn, h]
  have hsw := (top_block_spine H hk hee' hw hwe).1 hn
  have hsw' := (top_block_spine H hk hee' hw' hw'e).2 hn'
  have hm := top_marks H hee'.1
  have hm' := top_marks H hee'.2.1
  constructor
  · by_contra hlt
    have hbx : (κ w').boxX d = e := by omega
    have hmem : e ∈ xSpan (t w') := by
      rw [(F.vertical_spine (hJ w' hw')).2.1, Finset.mem_Ico]
      omega
    obtain ⟨p, hp, q, hq, h1, h2⟩ := mem_xSpan.1 hmem
    rcases hsep w hw w' hw' hww' with h | h
    · have := h q hq
      omega
    · have := h p hp
      omega
  · by_contra hlt
    obtain ⟨i, hi, hc⟩ := (H.lemma25a hk).1 (e + d) (by omega) (by omega)
    have hB := top_block H hk hee' hi hc (by omega) (by omega)
    have hbox := (F.cell_in_box (hJ i hi) hc).1
    cases hni : (κ i).negX
    · have h := hB.2.1 hni
      unfold GridIso.boxX at hbox
      simp only [hni, Bool.false_eq_true, ite_false] at hbox
      omega
    · have h := hB.2.2 hni
      unfold GridIso.boxX at hbox
      simp only [hni, ite_true] at hbox
      omega

/-! ## Proposition 28 and its case `k = 3`, Proposition 27 -/

/-- If every vertical tile is a top tile, `T` contains the rows below `b - a`. Source:
`report-4.md`, Proposition 28 (0) (line 135): "No vertical tile has a cell in rows
0, ..., h - 1, so T contains them." -/
private theorem low_mem (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k)
    (hall : ∀ i, i ≠ i₀ → i ∈ topTiles b t i₀) {x y : ℤ} (hx0 : 0 ≤ x) (hxa : x < a)
    (hy0 : 0 ≤ y) (hyh : y < b - a) : (x, y) ∈ t i₀ := by
  have hb := H.bounds hk
  obtain ⟨i, hi⟩ := H.frame.exists_tile_at hx0 hxa hy0 (by omega)
  by_cases hne : i = i₀
  · rwa [hne] at hi
  · have h1 := top_boxY H (hall i hne)
    have h2 := H.frame.cell_in_box (H.vert i hne) hi
    omega

/-- If every vertical tile is a top tile, `b - a < d`. Source: `report-4.md`,
Proposition 28 (0): "T lies in rows < d and is not its box, so h < d." -/
private theorem low_lt (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k)
    (hall : ∀ i, i ≠ i₀ → i ∈ topTiles b t i₀) : b - a < d := by
  by_contra hlt
  apply H.frame.nonrect
  refine Finset.Subset.antisymm (subset_boundingBox _) ?_
  rintro ⟨x, y⟩ hc
  rw [mem_boundingBox, H.frame.cols, H.frame.rows, Finset.mem_Ico, Finset.mem_Ico] at hc
  dsimp only at hc
  exact low_mem H hk hall hc.1.1 hc.1.2 hc.2.1 (by omega)

/-- Proposition 28, step (1). Source: `report-4.md`, Proposition 28 (line 135): if
every vertical tile is a top tile and `d < a`, no block of the top tiles holds
exactly one top tile (the spine collision). -/
theorem proposition28_step1 (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) (hda : d < a)
    (hall : ∀ i, i ≠ i₀ → i ∈ topTiles b t i₀) {e e' : ℤ}
    (hee' : Consecutive (colMarks a κ (topTiles b t i₀)) e e') {w : Fin k}
    (hw : w ∈ topTiles b t i₀)
    (hone : ∀ i ∈ topTiles b t i₀, e ≤ (κ i).boxX d ∧ (κ i).boxX d + d ≤ e' → i = w) :
    False := by
  have hb := H.bounds hk
  have F := H.frame
  have hJ := top_vert H
  have hr := top_marks H hee'.1
  have hr' := top_marks H hee'.2.1
  have hhd := low_lt H hk hall
  have hwid := (H.lemma25c hk hee' hw hone).1
  obtain ⟨-, w', hw', hwe⟩ := H.lemma25b hk hee'
  obtain rfl : w' = w := hone w' hw' hwe
  have hy := top_boxY H hw
  -- the rows from `d` up are full rows of the one tile of the block
  have hfull : ∀ x y : ℤ, e ≤ x → x < e' → d ≤ y → y < b → (x, y) ∈ t w' := by
    intro x y h1 h2 h3 h4
    obtain ⟨i, hi⟩ := F.exists_tile_at (x := x) (y := y) (by omega) (by omega) (by omega) h4
    have hne : i ≠ i₀ := by
      rintro rfl
      have := F.cell_low hi
      omega
    rwa [hone i (hall i hne) (top_block H hk hee' (hall i hne) hi h1 h2).1] at hi
  -- no spine column is a column of `T` with a cell in row `b - a`
  have hno : ∀ i ∈ topTiles b t i₀, ((κ i).shift.1, b - a) ∉ t i₀ := by
    intro i hi hc
    have h1 := top_boxY H hi
    have h2 := (F.vertical_spine (hJ i hi)).1 (b - a) (by omega) (by omega)
    exact (mem_topTiles.1 hi).1 (F.same_tile h2 hc)
  have h0 : (0 : ℤ) ∈ colMarks a κ (topTiles b t i₀) := mem_colMarks.2 (Or.inl rfl)
  have ha : a ∈ colMarks a κ (topTiles b t i₀) := mem_colMarks.2 (Or.inr (Or.inl rfl))
  cases hn : (κ w').negY
  · -- `T` contains the columns `[d - h, a)`, against the last block
    have hcol : ∀ x : ℤ, d - (b - a) ≤ x → x < a → (x, b - a) ∈ t i₀ := by
      intro x h1 h2
      refine F.column_of_row (hJ w' hw) ?_ (by omega) hhd
      intro z hz1 hz2
      rw [hn, hy, ite_eq_right Bool.false_ne_true]
      exact hfull z _ (by omega) (by omega) (by omega) (by omega)
    obtain ⟨f, hf⟩ := exists_consecutive_left ha h0 (by omega)
    obtain ⟨-, i, hi, hie⟩ := H.lemma25b hk hf
    have hspine := top_block_spine H hk hf hi hie
    have hlow : (κ i).shift.1 < d - (b - a) := by
      have hc := (F.vertical_spine (hJ i hi)).1 ((κ i).boxY a) le_rfl (by omega)
      have hc' := F.cell_in_R hc
      by_contra hlt
      exact hno i hi (hcol _ (by omega) (by omega))
    have hfr := top_marks H hf.1
    cases hni : (κ i).negX
    · have hs := hspine.1 hni
      by_cases hf0 : f = 0
      · have := consecutive_unique hee' hf le_rfl hee'.2.2.1 (by omega) (by omega)
        omega
      · obtain ⟨f₀, hf₀⟩ := exists_consecutive_left hf.1 h0 (by omega)
        have h1 := (H.lemma25b hk hf₀).1
        have h2 := top_marks H hf₀.1
        omega
    · have hs := hspine.2 hni
      omega
  · -- `T` contains the columns `[0, a + h - d)`, against the first block
    have hcol : ∀ x : ℤ, 0 ≤ x → x < a + (b - a) - d → (x, b - a) ∈ t i₀ := by
      intro x h1 h2
      refine F.column_of_row (hJ w' hw) ?_ (by omega) hhd
      intro z hz1 hz2
      rw [hn, hy, ite_eq_left rfl]
      exact hfull z _ (by omega) (by omega) (by omega) (by omega)
    obtain ⟨f, hf⟩ := exists_consecutive_right h0 ha (by omega)
    obtain ⟨-, i, hi, hie⟩ := H.lemma25b hk hf
    have hspine := top_block_spine H hk hf hi hie
    have hhigh : a + (b - a) - d ≤ (κ i).shift.1 := by
      have hc := (F.vertical_spine (hJ i hi)).1 ((κ i).boxY a) le_rfl (by omega)
      have hc' := F.cell_in_R hc
      by_contra hlt
      exact hno i hi (hcol _ (by omega) (by omega))
    have hfr := top_marks H hf.2.1
    cases hni : (κ i).negX
    · have hs := hspine.1 hni
      omega
    · have hs := hspine.2 hni
      by_cases hfa : f = a
      · have := consecutive_unique hee' hf le_rfl hee'.2.2.1 (by omega) (by omega)
        omega
      · obtain ⟨f₀, hf₀⟩ := exists_consecutive_right hf.2.1 ha (by omega)
        have h1 := (H.lemma25b hk hf₀).1
        have h2 := top_marks H hf₀.2.1
        omega

/-- If every vertical tile is a top tile, a block holds a right-type and a left-type
top tile. Source: `report-4.md`, Proposition 28 (2) (line 135): "So every block holds
two top tiles." -/
private theorem block_both (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) (hda : d < a)
    (hall : ∀ i, i ≠ i₀ → i ∈ topTiles b t i₀) {e e' : ℤ}
    (hee' : Consecutive (colMarks a κ (topTiles b t i₀)) e e') (n : Bool) :
    ∃ i ∈ topTiles b t i₀, (e ≤ (κ i).boxX d ∧ (κ i).boxX d + d ≤ e') ∧ (κ i).negX = n := by
  obtain ⟨-, w, hw, hwe⟩ := H.lemma25b hk hee'
  by_cases hn : (κ w).negX = n
  · exact ⟨w, hw, hwe, hn⟩
  · by_contra hcon
    push Not at hcon
    refine H.proposition28_step1 hk hda hall hee' hw fun i hi hie => ?_
    refine H.frame.column_blocks_unique _ (top_vert H) (H.lemma25a hk).2.2 hee' hi hw hie hwe ?_
    have h := hcon i hi hie
    revert hn h
    cases (κ w).negX <;> cases (κ i).negX <;> cases n <;> simp

/-- Proposition 28. Source: `report-4.md`, section 4, Proposition 28 (line 133):
"In the setting of section 1 with d < a, not every vertical tile is a top tile."
Proof idea, step (2): with two top tiles in every block, columns 0 and `a - 1`
are spines above the `h = b - a` full bottom rows, so `a = (k - 1) h` and `T` is
the rectangle of its bottom `h` rows. -/
theorem proposition28 (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) (hda : d < a) :
    ∃ i, i ≠ i₀ ∧ i ∉ topTiles b t i₀ := by
  by_contra hcon
  push Not at hcon
  have hb := H.bounds hk
  have F := H.frame
  have hJ := top_vert H
  have hhd := low_lt H hk hcon
  -- a column of `T` under a spine
  have hcol : ∀ i ∈ topTiles b t i₀, colCount (t i₀) (κ i).shift.1 = b - a := by
    intro i hi
    have h1 := top_boxY H hi
    have h2 := (F.vertical_spine (hJ i hi)).1
    have h3 := F.cell_in_R (h2 (b - a) (by omega) (by omega))
    refine colCount_of_interval (by omega) fun y => ⟨fun hc => ?_, fun hy => ?_⟩
    · have h4 := F.cell_low hc
      refine ⟨h4.1, ?_⟩
      by_contra hlt
      exact (mem_topTiles.1 hi).1 (F.same_tile (h2 y (by omega) (by omega)) hc)
    · exact low_mem H hk hcon h3.1.1 h3.1.2 hy.1 hy.2
  have h0 : (0 : ℤ) ∈ colMarks a κ (topTiles b t i₀) := mem_colMarks.2 (Or.inl rfl)
  have ha : a ∈ colMarks a κ (topTiles b t i₀) := mem_colMarks.2 (Or.inr (Or.inl rfl))
  have hu0 : colCount (t i₀) 0 = b - a := by
    obtain ⟨f, hf⟩ := exists_consecutive_right h0 ha (by omega)
    obtain ⟨i, hi, hie, hn⟩ := block_both H hk hda hcon hf false
    rw [← (top_block_spine H hk hf hi hie).1 hn]
    exact hcol i hi
  have hu1 : colCount (t i₀) (a - 1) = b - a := by
    obtain ⟨f, hf⟩ := exists_consecutive_left ha h0 (by omega)
    obtain ⟨i, hi, hie, hn⟩ := block_both H hk hda hcon hf true
    rw [← (top_block_spine H hk hf hi hie).2 hn]
    exact hcol i hi
  -- every vertical tile has `b - a` cells in row `b - 1`
  have hrow : ∀ i, rowCount (t i) (b - 1) = (b - a) - if i = i₀ then b - a else 0 := by
    intro i
    by_cases hi : i = i₀
    · rw [ite_eq_left hi, sub_self, hi]
      refine rowCount_of_empty fun x hx => ?_
      have := F.cell_low hx
      omega
    · rw [ite_eq_right hi, sub_zero]
      have hy := top_boxY H (hcon i hi)
      have hs := H.vert i hi
      cases hn : (κ i).negY
      · have h := F.vertical_rowCount hs (a - 1)
        rw [Frame.image_row (a - 1) (κ i) a, hn, hy, ite_eq_right Bool.false_ne_true, hu1,
          show b - a + (a - 1) = b - 1 by ring] at h
        exact h
      · have h := F.vertical_rowCount hs 0
        rw [Frame.image_row 0 (κ i) a, hn, hy, ite_eq_left rfl, hu0,
          show b - a + (a - 1 - 0) = b - 1 by ring] at h
        exact h
  have hsum := sum_rowCount_of_cover t F.disjoint F.cover (by omega) (y := b - 1)
    (by omega) (by omega)
  rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ite_eq_left (Finset.mem_univ _)] at hsum
  -- the area
  have hcard : ((t i₀).card : ℤ) = a * (b - a) := by
    have h := F.isTiling.card_mul
    have h' : (k : ℤ) * (t i₀).card = a * b := by
      rw [← Int.toNat_of_nonneg (show 0 ≤ a by omega),
        ← Int.toNat_of_nonneg (show 0 ≤ b by omega)]
      exact_mod_cast h
    have hk0 : (k : ℤ) ≠ 0 := by omega
    apply mul_left_cancel₀ hk0
    rw [h']
    linear_combination (-a) * hsum
  have hsub : (Finset.Ico 0 a ×ˢ Finset.Ico 0 (b - a) : Finset Cell) ⊆ t i₀ := by
    rintro ⟨x, y⟩ hc
    simp only [Finset.mem_product, Finset.mem_Ico] at hc
    exact low_mem H hk hcon hc.1.1 hc.1.2 hc.2.1 hc.2.2
  have hcle : (t i₀).card ≤ (Finset.Ico 0 a ×ˢ Finset.Ico 0 (b - a) : Finset Cell).card := by
    rw [Finset.card_product, Int.card_Ico, Int.card_Ico, sub_zero, sub_zero]
    zify
    rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega), hcard]
  have heq := Finset.eq_of_subset_of_card_le hsub hcle
  obtain ⟨x, hx⟩ := F.exists_in_row (y := b - a) (by omega) hhd
  rw [← heq] at hx
  simp only [Finset.mem_product, Finset.mem_Ico] at hx
  omega

/-- Proposition 27. Source: `report-4.md`, section 4, Proposition 27 (line 127):

> No rectangle has a 3-copy tiling by a non-rectangular polyomino in which a tile
> contains row 0 and the other two tiles are vertical.

Proof (line 137): "For k = 3 both vertical tiles are top tiles (one has at most
d < a cells in row b - 1), and d < a by Corollary 23". -/
theorem proposition27 {a b d : ℤ} {t : Fin 3 → Finset Cell} {i₀ : Fin 3}
    {κ : Fin 3 → GridIso} (H : TypeH1 a b d t i₀ κ) : False := by
  have hb := H.bounds (by omega)
  have F := H.frame
  have hda := (H.corollary23 le_rfl (by decide)).2.1
  obtain ⟨i, hi, hit⟩ := H.proposition28 (by omega) hda
  -- one tile alone covers the top row
  have hbound : a ≤ (((Finset.univ.erase i₀).erase i).card : ℤ) * d := by
    refine F.row_bound _ (fun j hj => H.vert j ?_) (y := b - 1) (by omega) (by omega) ?_
    · exact (Finset.mem_erase.1 (Finset.mem_erase.1 hj).2).1
    · intro j x hx
      have hj : j ≠ i₀ := by
        rintro rfl
        have := F.cell_low hx
        omega
      have hjt := mem_topTiles.2 ⟨hj, x, hx⟩
      refine Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩⟩
      rintro rfl
      exact hit hjt
  rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hbound
  norm_num at hbound
  omega

/-! ## Corollaries 26 and 29 (five tiles) -/

/-- Corollary 26. Source: `report-4.md`, Corollary 26 (line 121): "Let p be the
number of top tiles. Then 2 <= p <= 4 and a <= p d. If b - a > d, then p = 2,
a <= 2d, and the two other vertical tiles both have cells in every row r with
d <= r < b - a." -/
theorem corollary26 {a b d : ℤ} {t : Fin 5 → Finset Cell} {i₀ : Fin 5}
    {κ : Fin 5 → GridIso} (H : TypeH1 a b d t i₀ κ) :
    2 ≤ (topTiles b t i₀).card ∧ (topTiles b t i₀).card ≤ 4 ∧
      a ≤ (topTiles b t i₀).card * d ∧
      (d < b - a → (topTiles b t i₀).card = 2 ∧ a ≤ 2 * d ∧
        ∀ i, i ≠ i₀ → i ∉ topTiles b t i₀ →
          ∀ r : ℤ, d ≤ r → r < b - a → ∃ x : ℤ, (x, r) ∈ t i) := by
  have hb := H.bounds (by omega)
  have F := H.frame
  have hda := (H.corollary23 (by omega) (by decide)).2.1
  have hsub : topTiles b t i₀ ⊆ Finset.univ.erase i₀ := fun i hi =>
    Finset.mem_erase.2 ⟨(mem_topTiles.1 hi).1, Finset.mem_univ _⟩
  have hcard4 : (Finset.univ.erase i₀ : Finset (Fin 5)).card = 4 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have h4 : (topTiles b t i₀).card ≤ 4 := by
    rw [← hcard4]
    exact Finset.card_le_card hsub
  have hpd : a ≤ (topTiles b t i₀).card * d := by
    refine F.row_bound _ (top_vert H) (y := b - 1) (by omega) (by omega) fun j x hx => ?_
    refine mem_topTiles.2 ⟨?_, x, hx⟩
    rintro rfl
    have := F.cell_low hx
    omega
  have hcancel : ∀ m : ℕ, a ≤ m * d → 2 ≤ m := by
    intro m hm
    by_contra hlt
    have h1 : (m : ℤ) * d ≤ 1 * d := mul_le_mul_of_nonneg_right (by omega) (by omega)
    omega
  refine ⟨hcancel _ hpd, h4, hpd, fun hh => ?_⟩
  -- the rows between `T` and the top tiles
  have hmid : ∀ i x r, d ≤ r → r < b - a → (x, r) ∈ t i →
      i ∈ Finset.univ.erase i₀ \ topTiles b t i₀ := by
    intro i x r hr1 hr2 hx
    refine Finset.mem_sdiff.2 ⟨Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩, fun hi => ?_⟩
    · rintro rfl
      have := F.cell_low hx
      omega
    · have h1 := top_boxY H hi
      have h2 := F.cell_in_box (top_vert H i hi) hx
      omega
  have hvert : ∀ i ∈ Finset.univ.erase i₀ \ topTiles b t i₀, (κ i).swap = true :=
    fun i hi => H.vert i (Finset.mem_erase.1 (Finset.mem_sdiff.1 hi).1).1
  have hsd := Finset.card_sdiff_add_card_eq_card hsub
  rw [hcard4] at hsd
  have h2 := hcancel _ (F.row_bound _ hvert (y := d) (by omega) (by omega)
    fun i x hx => hmid i x d le_rfl hh hx)
  have hp := hcancel _ hpd
  have hp2 : (topTiles b t i₀).card = 2 := by omega
  refine ⟨hp2, by rw [hp2] at hpd; exact hpd, fun i hi hit r hr1 hr2 => ?_⟩
  by_contra hno
  push Not at hno
  have h3 := hcancel _ (F.row_bound ((Finset.univ.erase i₀ \ topTiles b t i₀).erase i)
    (fun j hj => hvert j (Finset.mem_erase.1 hj).2) (y := r) (by omega) (by omega)
    fun j x hx => Finset.mem_erase.2
      ⟨by rintro rfl; exact hno x hx, hmid j x r hr1 hr2 hx⟩)
  rw [Finset.card_erase_of_mem (Finset.mem_sdiff.2
    ⟨Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩, hit⟩)] at h3
  omega

/-- Corollary 29. Source: `report-4.md`, Corollary 29 (line 141): "The number p of
top tiles is 2 or 3". -/
theorem corollary29 {a b d : ℤ} {t : Fin 5 → Finset Cell} {i₀ : Fin 5}
    {κ : Fin 5 → GridIso} (H : TypeH1 a b d t i₀ κ) :
    (topTiles b t i₀).card = 2 ∨ (topTiles b t i₀).card = 3 := by
  have hda := (H.corollary23 (by omega) (by decide)).2.1
  obtain ⟨h2, h4, -, -⟩ := H.corollary26
  obtain ⟨i, hi, hit⟩ := H.proposition28 (by omega) hda
  have hsub : topTiles b t i₀ ⊆ (Finset.univ.erase i₀).erase i := by
    intro j hj
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2
      ⟨(mem_topTiles.1 hj).1, Finset.mem_univ _⟩⟩
    rintro rfl
    exact hit hj
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h3
  omega

/-! ## Lemma 30: the bottom of type H1 -/

end TypeH1

/-- `s` is the number of full rows at the bottom of `T`: rows `0, ..., s - 1` lie in
`T` and row `s` does not. Source: `report-4.md`, Lemma 30 (line 151). The number `s` is
a count, so `0 ≤ s` is part of the definition; without it every `s < 0` would qualify. -/
def FullRows (T : Finset Cell) (a s : ℤ) : Prop :=
  0 ≤ s ∧ (∀ x y : ℤ, 0 ≤ x → x < a → 0 ≤ y → y < s → (x, y) ∈ T) ∧
    ∃ x : ℤ, 0 ≤ x ∧ x < a ∧ (x, s) ∉ T

namespace Frame

variable {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell} {i₀ : Fin k} {κ : Fin k → GridIso}

/-- Lemma 30, first sentence: `1 <= s <= d - 1` exists. Source: `report-4.md`,
Lemma 30 (line 151). Stated for a frame, since section 5e uses the same `s` in
type H2. -/
theorem exists_fullRows (F : Frame a b d t i₀ κ) :
    ∃ s : ℤ, 1 ≤ s ∧ s ≤ d - 1 ∧ FullRows (t i₀) a s := by
  have hd := F.two_le_d
  obtain ⟨⟨x, y⟩, hbox, hnot⟩ := exists_hole_of_not_isRectangular F.nonrect
  rw [mem_boundingBox, F.cols, F.rows, Finset.mem_Ico, Finset.mem_Ico] at hbox
  dsimp only at hbox
  obtain ⟨s, ⟨hs0, z, hz0, hza, hz⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun s : ℤ => 0 ≤ s ∧ ∃ z : ℤ, 0 ≤ z ∧ z < a ∧ (z, s) ∉ t i₀)
    ⟨0, fun _ h => h.1⟩ ⟨y, hbox.2.1, x, hbox.1.1, hbox.1.2, hnot⟩
  refine ⟨s, ?_, ?_, hs0, fun x' y' hx0 hxa hy0 hys => ?_, z, hz0, hza, hz⟩
  · by_contra hlt
    obtain rfl : s = 0 := by omega
    exact hz (F.row0 z hz0 hza)
  · have := hmin y ⟨hbox.2.1, x, hbox.1.1, hbox.1.2, hnot⟩
    omega
  · by_contra hc
    have := hmin y' ⟨hy0, x', hx0, hxa, hc⟩
    omega

/-- Lemma 30 (b), the thick spine. Source: `report-4.md`, Lemma 30 (b) (line 153):
"every vertical tile contains in full the s columns of its box nearest its spine,
the spine included". Stated for a frame (used in types H1 and H2). -/
theorem thick_spine (F : Frame a b d t i₀ κ) {s : ℤ} (hs : FullRows (t i₀) a s) {i : Fin k}
    (hi : (κ i).swap = true) (j y : ℤ) (hj0 : 0 ≤ j) (hjs : j < s)
    (hy0 : (κ i).boxY a ≤ y) (hya : y < (κ i).boxY a + a) :
    ((if (κ i).negX then -j else j) + (κ i).shift.1, y) ∈ t i := by
  have key : ∀ x : ℤ, 0 ≤ x → x < a → (if (κ i).negY then -x else x) + (κ i).shift.2 = y →
      ((if (κ i).negX then -j else j) + (κ i).shift.1, y) ∈ t i := by
    intro x h0 h1 hxy
    have h := (F.vertical_mem hi x j).2 (hs.2.1 x j h0 h1 hj0 hjs)
    rwa [hxy] at h
  unfold GridIso.boxY at hy0 hya
  cases hn : (κ i).negY <;>
    simp only [hn, Bool.false_eq_true, ite_true, ite_false] at hy0 hya key
  · exact key (y - (κ i).shift.2) (by omega) (by omega) (by omega)
  · exact key ((κ i).shift.2 - y) (by omega) (by omega) (by omega)

end Frame

namespace TypeH1

variable {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell} {i₀ : Fin k} {κ : Fin k → GridIso}

/-- Lemma 30 (a). Source: `report-4.md`, Lemma 30 (a) (line 152): "every vertical
tile has y_i >= s, and the vertical tiles with a cell in row s are exactly those
with y_i = s (bottom tiles); there is at least one". -/
theorem lemma30a (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) {s : ℤ} (hs : FullRows (t i₀) a s) :
    (∀ i, i ≠ i₀ → s ≤ (κ i).boxY a) ∧
      (∀ i, i ≠ i₀ → ((∃ x : ℤ, (x, s) ∈ t i) ↔ (κ i).boxY a = s)) ∧
      ∃ i, i ≠ i₀ ∧ (κ i).boxY a = s := by
  have hb := H.bounds hk
  have F := H.frame
  have hs0 := hs.1
  have hspine : ∀ i, i ≠ i₀ → ((κ i).shift.1, (κ i).boxY a) ∈ t i := fun i hi =>
    (F.vertical_spine (H.vert i hi)).1 _ le_rfl (by omega)
  have h1 : ∀ i, i ≠ i₀ → s ≤ (κ i).boxY a := by
    intro i hi
    have hc := F.cell_in_R (hspine i hi)
    by_contra hlt
    exact hi (F.same_tile (hspine i hi) (hs.2.1 _ _ hc.1.1 hc.1.2 hc.2.1 (by omega)))
  have h2 : ∀ i, i ≠ i₀ → ((∃ x : ℤ, (x, s) ∈ t i) ↔ (κ i).boxY a = s) := by
    intro i hi
    constructor
    · rintro ⟨x, hx⟩
      have h3 := F.cell_in_box (H.vert i hi) hx
      have h4 := h1 i hi
      omega
    · intro h
      have hc := hspine i hi
      rw [h] at hc
      exact ⟨_, hc⟩
  refine ⟨h1, h2, ?_⟩
  obtain ⟨x, hx0, hxa, hx⟩ := hs.2.2
  have hsd : s < d := by
    by_contra hlt
    obtain ⟨s', hs', hs'd, -, -, z, hz0, hza, hz⟩ := F.exists_fullRows
    exact hz (hs.2.1 z s' hz0 hza (by omega) (by omega))
  obtain ⟨i, hi⟩ := F.exists_tile_at hx0 hxa hs0 (by omega)
  have hne : i ≠ i₀ := by
    rintro rfl
    exact hx hi
  exact ⟨i, hne, (h2 i hne).1 ⟨x, hi⟩⟩

/-- Lemma 30 (c), (d). Source: `report-4.md`, Lemma 30 (c), (d) (lines 154-155): if
`c` is a thick-spine column of a bottom tile, `T` meets column `c` in the rows
`0, ..., s - 1` only, and every vertical tile has exactly `s` cells in the row that
is the image of column `c`. -/
theorem lemma30cd (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) {s : ℤ} (hs : FullRows (t i₀) a s)
    {i : Fin k} (hi : i ≠ i₀) (hbot : (κ i).boxY a = s) (j : ℤ) (hj0 : 0 ≤ j) (hjs : j < s) :
    (∀ y : ℤ, ((if (κ i).negX then -j else j) + (κ i).shift.1, y) ∈ t i₀ ↔ 0 ≤ y ∧ y < s) ∧
      ∀ i', i' ≠ i₀ →
        rowCount (t i')
          ((if (κ i').negY then -((if (κ i).negX then -j else j) + (κ i).shift.1)
            else (if (κ i).negX then -j else j) + (κ i).shift.1) + (κ i').shift.2) = s := by
  have hb := H.bounds hk
  have F := H.frame
  have hthick : ∀ y : ℤ, s ≤ y → y < s + a →
      ((if (κ i).negX then -j else j) + (κ i).shift.1, y) ∈ t i := fun y h1 h2 =>
    F.thick_spine hs (H.vert i hi) j y hj0 hjs (by omega) (by omega)
  have hcol := F.cell_in_R (hthick s le_rfl (by omega))
  have hiff : ∀ y : ℤ, ((if (κ i).negX then -j else j) + (κ i).shift.1, y) ∈ t i₀ ↔
      0 ≤ y ∧ y < s := by
    intro y
    constructor
    · intro hc
      have h1 := F.cell_low hc
      refine ⟨h1.1, ?_⟩
      by_contra hlt
      exact hi (F.same_tile (hthick y (by omega) (by omega)) hc)
    · intro hy
      exact hs.2.1 _ y hcol.1.1 hcol.1.2 hy.1 hy.2
  refine ⟨hiff, fun i' hi' => ?_⟩
  rw [F.vertical_rowCount (H.vert i' hi')]
  exact colCount_of_interval (by omega) hiff

end TypeH1

end PolyominoOddOrder
