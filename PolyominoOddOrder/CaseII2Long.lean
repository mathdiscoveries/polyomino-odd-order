module

public import PolyominoOddOrder.ThreeCopy

/-!
# Case (II.2) with `b - a > d` does not occur (`CaseII2Long.lean`)

Blueprint unit II2a. Type H1 with five tiles, the layout with two top tiles and
`b - a > d`: `report-4.md`, sections 5, 5a, 5b (Proposition 31, Lemmas 32 and 32a,
Propositions 33 and 34, Corollary 35). The other half (`b - a <= d`) is
`CaseII2.lean`.

The binding statements of this file are `proposition34` and `corollary35`.
Everything else here is marked PROVISIONAL: it is the reports' intermediate
lemma in the coordinates of `Spine.lean`, stated in the parts that later steps
use, and the owner of the file may restate it.

Notation: `h = b - a`; `u_0 = colCount (t i₀) 0`, `u_1 = colCount (t i₀) (a - 1)`,
`t = rowCount (t i₀) (d - 1)` (the size of the top row of `T`). A tile at the left
wall (`boxX = 0`) is *outer* when `negX = false` (spine column 0) and *inner*
when `negX = true` (spine column `d - 1`); at the right wall (`boxX = a - d`) it
is outer when `negX = true` and inner when `negX = false`.

Commit `e5ca51d`.
-/

@[expose] public section

namespace PolyominoOddOrder

open TypeH1

/-! ## Working lemmas

Coordinates used in this file. A cell `(X, Y)` of a vertical tile `t i` is the image
of the cell `(ord (κ i) a Y, j)` of `T`, where `j` is the distance of column `X` from
the spine; `place` is the inverse of `ord`. -/

namespace Layout31

/-- The rows of the cells of `S` in column `x`. -/
def colSet (S : Finset Cell) (x : ℤ) : Finset ℤ :=
  (S.filter fun c => c.1 = x).image Prod.snd

theorem mem_colSet {S : Finset Cell} {x y : ℤ} : y ∈ colSet S x ↔ (x, y) ∈ S := by
  unfold colSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨u, v⟩, hc, rfl⟩
    obtain ⟨h1, rfl⟩ := Finset.mem_filter.1 hc
    exact h1
  · intro h
    exact ⟨(x, y), Finset.mem_filter.2 ⟨h, rfl⟩, rfl⟩

theorem card_colSet (S : Finset Cell) (x : ℤ) : ((colSet S x).card : ℤ) = colCount S x := by
  unfold colSet colCount
  rw [Finset.card_image_of_injOn]
  intro c hc c' hc' h
  have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
  have h2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hc')).2
  exact Prod.ext (h1.trans h2.symm) h

/-- The columns of the cells of `S` in row `y`. -/
def rowSet (S : Finset Cell) (y : ℤ) : Finset ℤ :=
  (S.filter fun c => c.2 = y).image Prod.fst

theorem mem_rowSet {S : Finset Cell} {x y : ℤ} : x ∈ rowSet S y ↔ (x, y) ∈ S := by
  unfold rowSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨u, v⟩, hc, rfl⟩
    obtain ⟨h1, rfl⟩ := Finset.mem_filter.1 hc
    exact h1
  · intro h
    exact ⟨(x, y), Finset.mem_filter.2 ⟨h, rfl⟩, rfl⟩

theorem card_rowSet (S : Finset Cell) (y : ℤ) : ((rowSet S y).card : ℤ) = rowCount S y := by
  unfold rowSet rowCount
  rw [Finset.card_image_of_injOn]
  intro c hc c' hc' h
  have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
  have h2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hc')).2
  exact Prod.ext h (h1.trans h2.symm)

/-- A finite set of integers with least value `lo` and no gaps. -/
theorem mem_iff_of_initial {A : Finset ℤ} {lo : ℤ} (hlo : ∀ y ∈ A, lo ≤ y)
    (hdown : ∀ y ∈ A, ∀ z, lo ≤ z → z ≤ y → z ∈ A) (y : ℤ) :
    y ∈ A ↔ lo ≤ y ∧ y < lo + A.card := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.notMem_empty, Finset.card_empty, Nat.cast_zero, false_iff]
    omega
  · obtain ⟨M, hM, hmax⟩ := A.exists_max_image id hne
    have hA : A = Finset.Icc lo M := by
      ext z
      rw [Finset.mem_Icc]
      exact ⟨fun h => ⟨hlo z h, hmax z h⟩, fun h => hdown M hM z h.1 h.2⟩
    have hc : (A.card : ℤ) = M + 1 - lo := by
      have := hlo M hM
      rw [hA, Int.card_Icc]
      omega
    rw [hc, hA, Finset.mem_Icc]
    omega

theorem colCount_of_interval {S : Finset Cell} {x lo hi : ℤ} (hle : lo ≤ hi)
    (h : ∀ y, (x, y) ∈ S ↔ lo ≤ y ∧ y < hi) : colCount S x = hi - lo := by
  have e : colSet S x = Finset.Ico lo hi := by
    ext y
    rw [mem_colSet, h, Finset.mem_Ico]
  rw [← card_colSet, e, Int.card_Ico]
  omega

theorem rowCount_of_interval {S : Finset Cell} {y lo hi : ℤ} (hle : lo ≤ hi)
    (h : ∀ x, (x, y) ∈ S ↔ lo ≤ x ∧ x < hi) : rowCount S y = hi - lo := by
  have e : rowSet S y = Finset.Ico lo hi := by
    ext x
    rw [mem_rowSet, h, Finset.mem_Ico]
  rw [← card_rowSet, e, Int.card_Ico]
  omega

theorem le_colCount {S : Finset Cell} {x lo hi : ℤ}
    (h : ∀ y, lo ≤ y → y < hi → (x, y) ∈ S) : hi - lo ≤ colCount S x := by
  have e : Finset.Ico lo hi ⊆ colSet S x := by
    intro y hy
    rw [Finset.mem_Ico] at hy
    exact mem_colSet.2 (h y hy.1 hy.2)
  have := Finset.card_le_card e
  rw [Int.card_Ico] at this
  rw [← card_colSet]
  omega

/-- Two disjoint sets that fill the rows `[lo, hi)` of column `x`. -/
theorem colCount_add {S S' : Finset Cell} {x lo hi : ℤ} (hle : lo ≤ hi)
    (h : ∀ y, ((x, y) ∈ S ∨ (x, y) ∈ S') ↔ lo ≤ y ∧ y < hi)
    (hd : ∀ y, (x, y) ∈ S → (x, y) ∈ S' → False) :
    colCount S x + colCount S' x = hi - lo := by
  have e : colSet S x ∪ colSet S' x = Finset.Ico lo hi := by
    ext y
    rw [Finset.mem_union, mem_colSet, mem_colSet, h, Finset.mem_Ico]
  have hdis : Disjoint (colSet S x) (colSet S' x) := by
    rw [Finset.disjoint_left]
    intro y h1 h2
    exact hd y (mem_colSet.1 h1) (mem_colSet.1 h2)
  have hc := Finset.card_union_of_disjoint hdis
  rw [e, Int.card_Ico] at hc
  rw [← card_colSet, ← card_colSet]
  omega

/-- Two descriptions of one non-empty interval agree. -/
theorem interval_eq {lo hi lo' hi' : ℤ}
    (h : ∀ y, (lo ≤ y ∧ y < hi) ↔ (lo' ≤ y ∧ y < hi')) (hne : lo < hi) :
    lo = lo' ∧ hi = hi' := by
  have h1 := h lo
  have h2 := h (hi - 1)
  have h3 := h lo'
  have h4 := h (hi' - 1)
  omega

/-- The column of `T` that goes to row `Y` of a vertical tile. -/
def ord (g : GridIso) (a Y : ℤ) : ℤ :=
  if g.negY then g.boxY a + a - 1 - Y else Y - g.boxY a

/-- The row of a vertical tile to which column `x` of `T` goes. -/
def place (g : GridIso) (a x : ℤ) : ℤ :=
  if g.negY then g.boxY a + a - 1 - x else g.boxY a + x

theorem ord_place (g : GridIso) (a x : ℤ) : ord g a (place g a x) = x := by
  unfold ord place
  split <;> omega

theorem ord_range {g : GridIso} {a Y : ℤ} :
    (0 ≤ ord g a Y ∧ ord g a Y < a) ↔ g.boxY a ≤ Y ∧ Y < g.boxY a + a := by
  unfold ord
  split <;> omega

theorem place_range {g : GridIso} {a x : ℤ} :
    (g.boxY a ≤ place g a x ∧ place g a x < g.boxY a + a) ↔ 0 ≤ x ∧ x < a := by
  unfold place
  split <;> omega

theorem ord_keep {g : GridIso} (h : g.negY = false) (a Y : ℤ) : ord g a Y = Y - g.boxY a := by
  simp [ord, h]

theorem ord_rev {g : GridIso} (h : g.negY = true) (a Y : ℤ) :
    ord g a Y = g.boxY a + a - 1 - Y := by
  simp [ord, h]

theorem place_keep {g : GridIso} (h : g.negY = false) (a x : ℤ) :
    place g a x = g.boxY a + x := by
  simp [place, h]

theorem place_rev {g : GridIso} (h : g.negY = true) (a x : ℤ) :
    place g a x = g.boxY a + a - 1 - x := by
  simp [place, h]

theorem place_eq (g : GridIso) (a x : ℤ) :
    place g a x = (if g.negY then -x else x) + g.shift.2 := by
  unfold place GridIso.boxY
  split <;> omega

section Frames

variable {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell} {i₀ : Fin k} {κ : Fin k → GridIso}

theorem vert_mem_right (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true)
    (hn : (κ i).negX = false) (X Y : ℤ) :
    (X, Y) ∈ t i ↔ (ord (κ i) a Y, X - (κ i).boxX d) ∈ t i₀ := by
  rw [← F.vertical_mem hi]
  have e1 : (if (κ i).negX then -(X - (κ i).boxX d) else X - (κ i).boxX d) + (κ i).shift.1 = X := by
    simp [GridIso.boxX, hn]
  have e2 : (if (κ i).negY then -(ord (κ i) a Y) else ord (κ i) a Y) + (κ i).shift.2 = Y := by
    rw [← place_eq _ a]
    unfold place ord
    split <;> omega
  rw [e1, e2]

theorem vert_mem_left (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true)
    (hn : (κ i).negX = true) (X Y : ℤ) :
    (X, Y) ∈ t i ↔ (ord (κ i) a Y, (κ i).boxX d + d - 1 - X) ∈ t i₀ := by
  rw [← F.vertical_mem hi]
  have e1 : (if (κ i).negX then -((κ i).boxX d + d - 1 - X) else (κ i).boxX d + d - 1 - X) +
      (κ i).shift.1 = X := by
    simp only [GridIso.boxX, hn, ite_true]
    omega
  have e2 : (if (κ i).negY then -(ord (κ i) a Y) else ord (κ i) a Y) + (κ i).shift.2 = Y := by
    rw [← place_eq _ a]
    unfold place ord
    split <;> omega
  rw [e1, e2]

theorem colCount_right (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true)
    (hn : (κ i).negX = false) (X : ℤ) :
    colCount (t i) X = rowCount (t i₀) (X - (κ i).boxX d) := by
  rw [← F.vertical_colCount hi]
  simp [GridIso.boxX, hn]

theorem colCount_left (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true)
    (hn : (κ i).negX = true) (X : ℤ) :
    colCount (t i) X = rowCount (t i₀) ((κ i).boxX d + d - 1 - X) := by
  rw [← F.vertical_colCount hi]
  congr 1
  simp only [GridIso.boxX, hn, ite_true]
  omega

theorem vert_bounds (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true) {X Y : ℤ}
    (h : (X, Y) ∈ t i) :
    (κ i).boxX d ≤ X ∧ X < (κ i).boxX d + d ∧ (κ i).boxY a ≤ Y ∧ Y < (κ i).boxY a + a := by
  obtain ⟨-, hx, hy, -, -⟩ := F.vertical_spine hi
  have h1 : X ∈ xSpan (t i) := mem_xSpan.2 ⟨_, h, _, h, le_rfl, le_rfl⟩
  have h2 : Y ∈ ySpan (t i) := mem_ySpan.2 ⟨_, h, _, h, le_rfl, le_rfl⟩
  rw [hx, Finset.mem_Ico] at h1
  rw [hy, Finset.mem_Ico] at h2
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

theorem base_bounds (F : Frame a b d t i₀ κ) {x y : ℤ} (h : (x, y) ∈ t i₀) :
    0 ≤ x ∧ x < a ∧ 0 ≤ y ∧ y < d := by
  have h1 : x ∈ xSpan (t i₀) := mem_xSpan.2 ⟨_, h, _, h, le_rfl, le_rfl⟩
  have h2 : y ∈ ySpan (t i₀) := mem_ySpan.2 ⟨_, h, _, h, le_rfl, le_rfl⟩
  rw [F.cols, Finset.mem_Ico] at h1
  rw [F.rows, Finset.mem_Ico] at h2
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

/-- A vertical tile meets every column of its box. -/
theorem vert_exists_col (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true) {X : ℤ}
    (h1 : (κ i).boxX d ≤ X) (h2 : X < (κ i).boxX d + d) : ∃ Y, (X, Y) ∈ t i := by
  have h : X ∈ xSpan (t i) := by
    rw [(F.vertical_spine hi).2.1, Finset.mem_Ico]
    exact ⟨h1, h2⟩
  obtain ⟨c, hc, e, he, h3, h4⟩ := mem_xSpan.1 h
  exact (F.isTiling.tile_isPolyomino F.poly i).2.exists_in_col hc he h3 h4

theorem spine_right (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true)
    (hn : (κ i).negX = false) {Y : ℤ} (h1 : (κ i).boxY a ≤ Y) (h2 : Y < (κ i).boxY a + a) :
    ((κ i).boxX d, Y) ∈ t i := by
  rw [vert_mem_right F hi hn, sub_self]
  have := ord_range.2 ⟨h1, h2⟩
  exact F.row0 _ this.1 this.2

theorem spine_left (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true)
    (hn : (κ i).negX = true) {Y : ℤ} (h1 : (κ i).boxY a ≤ Y) (h2 : Y < (κ i).boxY a + a) :
    ((κ i).boxX d + d - 1, Y) ∈ t i := by
  rw [vert_mem_left F hi hn, sub_self]
  have := ord_range.2 ⟨h1, h2⟩
  exact F.row0 _ this.1 this.2

/-- `T` is not its box. -/
theorem base_not_full (F : Frame a b d t i₀ κ)
    (h : ∀ x y : ℤ, 0 ≤ x → x < a → 0 ≤ y → y < d → (x, y) ∈ t i₀) : False := by
  refine F.nonrect (Finset.Subset.antisymm (subset_boundingBox _) ?_)
  rintro ⟨x, y⟩ hc
  rw [mem_boundingBox, F.cols, F.rows, Finset.mem_Ico, Finset.mem_Ico] at hc
  exact h x y hc.1.1 hc.1.2 hc.2.1 hc.2.2

end Frames

/-- Proposition 31 (i), `a + h <= 5d - 1`: `n <= a d - 1` and `5 n = a (a + h)`. -/
theorem height_bound {a b d : ℤ} {t : Fin 5 → Finset Cell} {i₀ : Fin 5}
    {κ : Fin 5 → GridIso} (F : Frame a b d t i₀ κ) : b ≤ 5 * d - 1 := by
  have h2 := F.two_le
  have hd := F.two_le_d
  have hbox : boundingBox (t i₀) = Finset.Ico 0 a ×ˢ Finset.Ico 0 d := by
    unfold boundingBox
    rw [F.cols, F.rows]
  have hlt : (t i₀).card < (boundingBox (t i₀)).card :=
    Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.2 ⟨subset_boundingBox _, fun h => F.nonrect h⟩)
  rw [hbox, Finset.card_product, Int.card_Ico, Int.card_Ico, sub_zero, sub_zero] at hlt
  have hm := F.isTiling.card_mul
  have ha : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg (by omega)
  have hb : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg (by omega)
  have hd' : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg (by omega)
  have hlt' : ((t i₀).card : ℤ) < a * d := by
    have : (((t i₀).card : ℕ) : ℤ) < ((a.toNat * d.toNat : ℕ) : ℤ) := by exact_mod_cast hlt
    rwa [Nat.cast_mul, ha, hd'] at this
  have hm' : 5 * ((t i₀).card : ℤ) = a * b := by
    have : ((5 * (t i₀).card : ℕ) : ℤ) = ((a.toNat * b.toNat : ℕ) : ℤ) := by exact_mod_cast hm
    rw [Nat.cast_mul, Nat.cast_mul, ha, hb] at this
    exact_mod_cast this
  by_contra hcon
  have h5 : 5 * d ≤ b := by omega
  have := mul_le_mul_of_nonneg_left h5 (by omega : (0 : ℤ) ≤ a)
  linarith [this, hm', hlt', mul_comm a d, mul_left_comm a 5 d]

/-! ### The mirror image -/

theorem mem_flip {S : Finset Cell} {a x y : ℤ} :
    (x, y) ∈ S.image (GridIso.flipX a).apply ↔ (a - 1 - x, y) ∈ S := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨u, v⟩, hc, h⟩
    rw [GridIso.flipX_apply, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have e : ((a - 1 - x, y) : Cell) = (u, v) := Prod.ext (by dsimp only at h1 ⊢; omega) h2.symm
    rw [e]
    exact hc
  · intro h
    refine ⟨_, h, ?_⟩
    rw [GridIso.flipX_apply]
    exact Prod.ext (by dsimp only; omega) rfl

/-- The isometry of a tile in the mirror image. -/
abbrev mir (a : ℤ) (g : GridIso) : GridIso :=
  (GridIso.flipX a).comp (g.comp (GridIso.flipX a))

theorem mir_negX {g : GridIso} (hs : g.swap = true) (a : ℤ) : (mir a g).negX = !g.negX := by
  simp [mir, GridIso.comp, GridIso.flipX, hs]

theorem mir_negY {g : GridIso} (hs : g.swap = true) (a : ℤ) : (mir a g).negY = !g.negY := by
  simp [mir, GridIso.comp, GridIso.flipX, hs]

theorem mir_boxX {g : GridIso} (hs : g.swap = true) (a d : ℤ) :
    (mir a g).boxX d = a - d - g.boxX d := by
  unfold GridIso.boxX
  rw [mir_negX hs]
  cases hn : g.negX <;>
    simp [mir, GridIso.comp, GridIso.flipX, GridIso.apply, hs, hn] <;> ring

theorem mir_boxY {g : GridIso} (hs : g.swap = true) (a : ℤ) :
    (mir a g).boxY a = g.boxY a := by
  unfold GridIso.boxY
  rw [mir_negY hs]
  cases hn : g.negY <;>
    simp [mir, GridIso.comp, GridIso.flipX, GridIso.apply, hs, hn]
  ring

end Layout31

/-! ## Section 5: the layout with two top tiles and `b - a > d` -/

/-- The layout of Proposition 31 (ii). Source: `report-4.md`, Proposition 31
(line 163):

> (ii) box(Z_1) = [0, d) x [y_1, y_1 + a), box(Z_2) = [a - d, a) x [y_2, y_2 + a) after
> renaming, with max(1, h - a) <= y_i <= d; box(W_1) = [0, d) x [h, b),
> box(W_2) = [a - d, a) x [h, b);

`w₁`, `w₂` are the top tiles, `z₁`, `z₂` the other two vertical tiles. -/
structure Layout31 (a b d : ℤ) (t : Fin 5 → Finset Cell) (i₀ : Fin 5)
    (κ : Fin 5 → GridIso) (w₁ w₂ z₁ z₂ : Fin 5) : Prop where
  /-- The tiling is of type H1. -/
  h1 : TypeH1 a b d t i₀ κ
  /-- `b - a > d`. -/
  long : d < b - a
  /-- The five tiles are `T`, `W_1`, `W_2`, `Z_1`, `Z_2`. -/
  nodup : [i₀, w₁, w₂, z₁, z₂].Nodup
  /-- `box(W_1) = [0, d) x [h, b)`. -/
  w₁box : (κ w₁).boxX d = 0 ∧ (κ w₁).boxY a = b - a
  /-- `box(W_2) = [a - d, a) x [h, b)`. -/
  w₂box : (κ w₂).boxX d = a - d ∧ (κ w₂).boxY a = b - a
  /-- `box(Z_1) = [0, d) x [y_1, y_1 + a)` with `max(1, h - a) <= y_1 <= d`. -/
  z₁box : (κ z₁).boxX d = 0 ∧ 1 ≤ (κ z₁).boxY a ∧ b - a - a ≤ (κ z₁).boxY a ∧
    (κ z₁).boxY a ≤ d
  /-- `box(Z_2) = [a - d, a) x [y_2, y_2 + a)` with `max(1, h - a) <= y_2 <= d`. -/
  z₂box : (κ z₂).boxX d = a - d ∧ 1 ≤ (κ z₂).boxY a ∧ b - a - a ≤ (κ z₂).boxY a ∧
    (κ z₂).boxY a ≤ d

/-- Proposition 31 (i), (ii). Source: `report-4.md`, Proposition 31 (lines 161-163):
in type H1 with five tiles and `h = b - a > d` the layout exists, `d < a <= 2d` and
`a + h <= 5d - 1`. Proof idea: Corollary 26; the two non-top tiles alone cover each
row `d <= r < h`. -/
theorem proposition31 {a b d : ℤ} {t : Fin 5 → Finset Cell} {i₀ : Fin 5}
    {κ : Fin 5 → GridIso} (H : TypeH1 a b d t i₀ κ) (hlong : d < b - a) :
    (d < a ∧ a ≤ 2 * d ∧ b ≤ 5 * d - 1) ∧
      ∃ w₁ w₂ z₁ z₂ : Fin 5, Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂ := by
  have F := H.frame
  have h23 := H.corollary23 (by norm_num) (by decide)
  obtain ⟨-, -, -, h26⟩ := corollary26 H
  obtain ⟨-, ha2, hZ⟩ := h26 hlong
  obtain ⟨hrow, hboxY, -⟩ := H.lemma25a (by norm_num)
  refine ⟨⟨h23.2.1, ha2, Layout31.height_bound F⟩, ?_⟩
  -- top tiles
  have htop : ∀ i ∈ topTiles b t i₀, i ≠ i₀ := by
    intro i hi
    simp only [topTiles, Finset.mem_filter] at hi
    exact hi.2.1
  obtain ⟨w₁, hw₁, hw₁c⟩ := hrow 0 le_rfl (by omega)
  obtain ⟨w₂, hw₂, hw₂c⟩ := hrow (a - 1) (by omega) (by omega)
  have vw₁ := H.vert w₁ (htop w₁ hw₁)
  have vw₂ := H.vert w₂ (htop w₂ hw₂)
  have bw₁ := Layout31.vert_bounds F vw₁ hw₁c
  have bw₂ := Layout31.vert_bounds F vw₂ hw₂c
  have sw₁ := (F.vertical_spine vw₁).2.2.2.1
  have sw₂ := (F.vertical_spine vw₂).2.2.2.1
  have yw₁ := hboxY w₁ hw₁
  have yw₂ := hboxY w₂ hw₂
  -- the other two
  have hcell : ∀ x : ℤ, 0 ≤ x → x < a → ∃ i, i ≠ i₀ ∧ i ∉ topTiles b t i₀ ∧ (x, d) ∈ t i := by
    intro x hx0 hxa
    obtain ⟨i, hi⟩ := F.isTiling.exists_tile (c := (x, d))
      (mem_R.2 ⟨⟨hx0, hxa⟩, by dsimp only; omega, by dsimp only; omega⟩)
    have hne : i ≠ i₀ := by
      rintro rfl
      have := Layout31.base_bounds F hi
      omega
    refine ⟨i, hne, fun hmem => ?_, hi⟩
    have h1 := Layout31.vert_bounds F (H.vert i hne) hi
    have h2 := hboxY i hmem
    omega
  have hbot : ∀ i, i ≠ i₀ → i ∉ topTiles b t i₀ → 1 ≤ (κ i).boxY a ∧
      b - a - a ≤ (κ i).boxY a ∧ (κ i).boxY a ≤ d := by
    intro i hne hnt
    obtain ⟨x, hx⟩ := hZ i hne hnt d le_rfl hlong
    obtain ⟨x', hx'⟩ := hZ i hne hnt (b - a - 1) (by omega) (by omega)
    have h1 := Layout31.vert_bounds F (H.vert i hne) hx
    have h2 := Layout31.vert_bounds F (H.vert i hne) hx'
    have h3 := (F.vertical_spine (H.vert i hne)).2.2.2.2
    omega
  obtain ⟨z₁, hz₁, nz₁, hz₁c⟩ := hcell 0 le_rfl (by omega)
  obtain ⟨z₂, hz₂, nz₂, hz₂c⟩ := hcell (a - 1) (by omega) (by omega)
  have bz₁ := Layout31.vert_bounds F (H.vert z₁ hz₁) hz₁c
  have bz₂ := Layout31.vert_bounds F (H.vert z₂ hz₂) hz₂c
  have sz₁ := (F.vertical_spine (H.vert z₁ hz₁)).2.2.2.1
  have sz₂ := (F.vertical_spine (H.vert z₂ hz₂)).2.2.2.1
  have hwne : w₁ ≠ w₂ := by
    rintro rfl
    omega
  have hzne : z₁ ≠ z₂ := by
    rintro rfl
    omega
  have hwz : ∀ i ∈ topTiles b t i₀, ∀ j, j ∉ topTiles b t i₀ → i ≠ j := by
    rintro i hi j hj rfl
    exact hj hi
  refine ⟨w₁, w₂, z₁, z₂, H, hlong, ?_, ⟨by omega, yw₁⟩, ⟨by omega, yw₂⟩,
    ⟨by omega, hbot z₁ hz₁ nz₁⟩, ⟨by omega, hbot z₂ hz₂ nz₂⟩⟩
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil,
    not_false_eq_true, and_true]
  exact ⟨⟨(htop w₁ hw₁).symm, (htop w₂ hw₂).symm, hz₁.symm, hz₂.symm⟩,
    ⟨hwne, hwz w₁ hw₁ z₁ nz₁, hwz w₁ hw₁ z₂ nz₂⟩,
    ⟨hwz w₂ hw₂ z₁ nz₁, hwz w₂ hw₂ z₂ nz₂⟩, hzne⟩

namespace Layout31

variable {a b d : ℤ} {t : Fin 5 → Finset Cell} {i₀ : Fin 5} {κ : Fin 5 → GridIso}
  {w₁ w₂ z₁ z₂ : Fin 5}

/-! ### Working lemmas on a layout -/

/-- Proposition 31 (i) with `2 <= d`. -/
theorem nums (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) :
    2 ≤ d ∧ d < a ∧ a ≤ 2 * d ∧ b ≤ 5 * d - 1 ∧ d < b - a := by
  have h1 := (proposition31 L.h1 L.long).1
  have h2 := L.h1.frame.two_le_d
  have h3 := L.long
  omega

theorem ne (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) :
    (i₀ ≠ w₁ ∧ i₀ ≠ w₂ ∧ i₀ ≠ z₁ ∧ i₀ ≠ z₂) ∧ (w₁ ≠ w₂ ∧ w₁ ≠ z₁ ∧ w₁ ≠ z₂) ∧
      (w₂ ≠ z₁ ∧ w₂ ≠ z₂) ∧ z₁ ≠ z₂ := by
  have h := L.nodup
  simpa only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil,
    not_false_eq_true, and_true] using h

theorem univ_eq (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) :
    [i₀, w₁, w₂, z₁, z₂].toFinset = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [List.toFinset_card_of_nodup L.nodup]
  rfl

theorem index_cases (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (i : Fin 5) :
    i = i₀ ∨ i = w₁ ∨ i = w₂ ∨ i = z₁ ∨ i = z₂ := by
  have h : i ∈ [i₀, w₁, w₂, z₁, z₂].toFinset := by
    rw [L.univ_eq]
    exact Finset.mem_univ i
  simpa using h

theorem sum_eq (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (f : Fin 5 → ℤ) :
    ∑ i, f i = f i₀ + f w₁ + f w₂ + f z₁ + f z₂ := by
  rw [← L.univ_eq, List.sum_toFinset f L.nodup]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

theorem vw₁ (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) : (κ w₁).swap = true :=
  L.h1.vert _ L.ne.1.1.symm

theorem vw₂ (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) : (κ w₂).swap = true :=
  L.h1.vert _ L.ne.1.2.1.symm

theorem vz₁ (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) : (κ z₁).swap = true :=
  L.h1.vert _ L.ne.1.2.2.1.symm

theorem vz₂ (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) : (κ z₂).swap = true :=
  L.h1.vert _ L.ne.1.2.2.2.symm

theorem bT (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) {X Y : ℤ} (h : (X, Y) ∈ t i₀) :
    0 ≤ X ∧ X < a ∧ 0 ≤ Y ∧ Y < d :=
  base_bounds L.h1.frame h

theorem bw₁ (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) {X Y : ℤ} (h : (X, Y) ∈ t w₁) :
    0 ≤ X ∧ X < d ∧ b - a ≤ Y ∧ Y < b := by
  have h1 := vert_bounds L.h1.frame L.vw₁ h
  have h2 := L.w₁box
  omega

theorem bw₂ (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) {X Y : ℤ} (h : (X, Y) ∈ t w₂) :
    a - d ≤ X ∧ X < a ∧ b - a ≤ Y ∧ Y < b := by
  have h1 := vert_bounds L.h1.frame L.vw₂ h
  have h2 := L.w₂box
  omega

theorem bz₁ (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) {X Y : ℤ} (h : (X, Y) ∈ t z₁) :
    0 ≤ X ∧ X < d ∧ (κ z₁).boxY a ≤ Y ∧ Y < (κ z₁).boxY a + a := by
  have h1 := vert_bounds L.h1.frame L.vz₁ h
  have h2 := L.z₁box
  omega

theorem bz₂ (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) {X Y : ℤ} (h : (X, Y) ∈ t z₂) :
    a - d ≤ X ∧ X < a ∧ (κ z₂).boxY a ≤ Y ∧ Y < (κ z₂).boxY a + a := by
  have h1 := vert_bounds L.h1.frame L.vz₂ h
  have h2 := L.z₂box
  omega

theorem uniq (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) {i j : Fin 5} {c : Cell} (hi : c ∈ t i)
    (hj : c ∈ t j) (hij : i ≠ j) : False :=
  hij (L.h1.frame.isTiling.tile_unique hi hj)

theorem tile_at (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) {X Y : ℤ} (hX0 : 0 ≤ X) (hXa : X < a)
    (hY0 : 0 ≤ Y) (hYb : Y < b) :
    (X, Y) ∈ t i₀ ∨ (X, Y) ∈ t w₁ ∨ (X, Y) ∈ t w₂ ∨ (X, Y) ∈ t z₁ ∨ (X, Y) ∈ t z₂ := by
  obtain ⟨i, hi⟩ := L.h1.frame.isTiling.exists_tile (c := (X, Y))
    (mem_R.2 ⟨⟨hX0, hXa⟩, hY0, hYb⟩)
  rcases L.index_cases i with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr (Or.inl hi))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hi)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hi)))

/-! Cells of the tiles at the left wall (`outer`: spine column 0) and at the right
wall (`outer`: spine column `a - 1`). -/

theorem w₁_outer (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hn : (κ w₁).negX = false) (X Y : ℤ) :
    (X, Y) ∈ t w₁ ↔ (ord (κ w₁) a Y, X) ∈ t i₀ := by
  rw [vert_mem_right L.h1.frame L.vw₁ hn, L.w₁box.1, sub_zero]

theorem w₁_inner (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hn : (κ w₁).negX = true) (X Y : ℤ) :
    (X, Y) ∈ t w₁ ↔ (ord (κ w₁) a Y, d - 1 - X) ∈ t i₀ := by
  rw [vert_mem_left L.h1.frame L.vw₁ hn, L.w₁box.1, zero_add]

theorem z₁_outer (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hn : (κ z₁).negX = false) (X Y : ℤ) :
    (X, Y) ∈ t z₁ ↔ (ord (κ z₁) a Y, X) ∈ t i₀ := by
  rw [vert_mem_right L.h1.frame L.vz₁ hn, L.z₁box.1, sub_zero]

theorem z₁_inner (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hn : (κ z₁).negX = true) (X Y : ℤ) :
    (X, Y) ∈ t z₁ ↔ (ord (κ z₁) a Y, d - 1 - X) ∈ t i₀ := by
  rw [vert_mem_left L.h1.frame L.vz₁ hn, L.z₁box.1, zero_add]

theorem w₂_outer (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hn : (κ w₂).negX = true) (X Y : ℤ) :
    (X, Y) ∈ t w₂ ↔ (ord (κ w₂) a Y, a - 1 - X) ∈ t i₀ := by
  rw [vert_mem_left L.h1.frame L.vw₂ hn, L.w₂box.1, sub_add_cancel]

theorem w₂_inner (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hn : (κ w₂).negX = false) (X Y : ℤ) :
    (X, Y) ∈ t w₂ ↔ (ord (κ w₂) a Y, X - (a - d)) ∈ t i₀ := by
  rw [vert_mem_right L.h1.frame L.vw₂ hn, L.w₂box.1]

theorem z₂_outer (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hn : (κ z₂).negX = true) (X Y : ℤ) :
    (X, Y) ∈ t z₂ ↔ (ord (κ z₂) a Y, a - 1 - X) ∈ t i₀ := by
  rw [vert_mem_left L.h1.frame L.vz₂ hn, L.z₂box.1, sub_add_cancel]

theorem z₂_inner (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hn : (κ z₂).negX = false) (X Y : ℤ) :
    (X, Y) ∈ t z₂ ↔ (ord (κ z₂) a Y, X - (a - d)) ∈ t i₀ := by
  rw [vert_mem_right L.h1.frame L.vz₂ hn, L.z₂box.1]

/-- A cell of the top row in a top tile: the tile's top row is an end column of `T`. -/
theorem ord_top (g : GridIso) (a b : ℤ) (h : g.boxY a = b - a) :
    ord g a (b - 1) = if g.negY then 0 else a - 1 := by
  unfold ord
  split <;> omega

/-- The mirror image of a layout is a layout with the two walls exchanged.
PROVISIONAL (used for "and mirror images"). -/
theorem mirror (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) :
    Layout31 a b d (fun i => (t i).image (GridIso.flipX a).apply) i₀
      (fun i => (GridIso.flipX a).comp ((κ i).comp (GridIso.flipX a))) w₂ w₁ z₂ z₁ := by
  have e₁ := mir_boxX L.vw₁ a d
  have e₂ := mir_boxX L.vw₂ a d
  have e₃ := mir_boxX L.vz₁ a d
  have e₄ := mir_boxX L.vz₂ a d
  have f₁ := mir_boxY L.vw₁ a
  have f₂ := mir_boxY L.vw₂ a
  have f₃ := mir_boxY L.vz₁ a
  have f₄ := mir_boxY L.vz₂ a
  have g₁ := L.w₁box
  have g₂ := L.w₂box
  have g₃ := L.z₁box
  have g₄ := L.z₂box
  have hn := L.ne
  refine ⟨L.h1.mirror, L.long, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, List.nodup_nil,
      not_false_eq_true, and_true]
    exact ⟨⟨hn.1.2.1, hn.1.1, hn.1.2.2.2, hn.1.2.2.1⟩,
      ⟨hn.2.1.1.symm, hn.2.2.1.2, hn.2.2.1.1⟩, ⟨hn.2.1.2.2, hn.2.1.2.1⟩, hn.2.2.2.symm⟩
  · change (mir a (κ w₂)).boxX d = 0 ∧ (mir a (κ w₂)).boxY a = b - a
    rw [e₂, f₂]
    omega
  · change (mir a (κ w₁)).boxX d = a - d ∧ (mir a (κ w₁)).boxY a = b - a
    rw [e₁, f₁]
    omega
  · change (mir a (κ z₂)).boxX d = 0 ∧ 1 ≤ (mir a (κ z₂)).boxY a ∧
      b - a - a ≤ (mir a (κ z₂)).boxY a ∧ (mir a (κ z₂)).boxY a ≤ d
    rw [e₄, f₄]
    omega
  · change (mir a (κ z₁)).boxX d = a - d ∧ 1 ≤ (mir a (κ z₁)).boxY a ∧
      b - a - a ≤ (mir a (κ z₁)).boxY a ∧ (mir a (κ z₁)).boxY a ≤ d
    rw [e₃, f₃]
    omega

/-- Proposition 31 (iii). PROVISIONAL. Source: `report-4.md`, Proposition 31 (line
164): "Z_1 contains [0, a - d) x [d, h) and Z_2 contains [d, a) x [d, h); W_1
contains [0, a - d) x [y_1 + a, b) and W_2 contains [d, a) x [y_2 + a, b)". -/
theorem prop31_iii (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) :
    (∀ x y : ℤ, 0 ≤ x → x < a - d → d ≤ y → y < b - a → (x, y) ∈ t z₁) ∧
      (∀ x y : ℤ, d ≤ x → x < a → d ≤ y → y < b - a → (x, y) ∈ t z₂) ∧
      (∀ x y : ℤ, 0 ≤ x → x < a - d → (κ z₁).boxY a + a ≤ y → y < b → (x, y) ∈ t w₁) ∧
      (∀ x y : ℤ, d ≤ x → x < a → (κ z₂).boxY a + a ≤ y → y < b → (x, y) ∈ t w₂) := by
  have hn := L.nums
  have hz₁ := L.z₁box
  have hz₂ := L.z₂box
  refine ⟨fun x y hx0 hxa hy0 hyb => ?_, fun x y hx0 hxa hy0 hyb => ?_,
    fun x y hx0 hxa hy0 hyb => ?_, fun x y hx0 hxa hy0 hyb => ?_⟩
  · rcases L.tile_at (X := x) (Y := y) (by omega) (by omega) (by omega) (by omega)
      with h | h | h | h | h
    · have := L.bT h
      omega
    · have := L.bw₁ h
      omega
    · have := L.bw₂ h
      omega
    · exact h
    · have := L.bz₂ h
      omega
  · rcases L.tile_at (X := x) (Y := y) (by omega) (by omega) (by omega) (by omega)
      with h | h | h | h | h
    · have := L.bT h
      omega
    · have := L.bw₁ h
      omega
    · have := L.bw₂ h
      omega
    · have := L.bz₁ h
      omega
    · exact h
  · rcases L.tile_at (X := x) (Y := y) (by omega) (by omega) (by omega) (by omega)
      with h | h | h | h | h
    · have := L.bT h
      omega
    · exact h
    · have := L.bw₂ h
      omega
    · have := L.bz₁ h
      omega
    · have := L.bz₂ h
      omega
  · rcases L.tile_at (X := x) (Y := y) (by omega) (by omega) (by omega) (by omega)
      with h | h | h | h | h
    · have := L.bT h
      omega
    · have := L.bw₁ h
      omega
    · exact h
    · have := L.bz₁ h
      omega
    · have := L.bz₂ h
      omega

/-- Proposition 31 (vi). PROVISIONAL. Source: `report-4.md`, Proposition 31 (lines
167, 169): "not both y_1 = h - a and y_2 = h - a ... Otherwise the line y = h is
clean, and T, Z_1, Z_2 tile R(a, h) with T on row 0 and two vertical tiles, against
Proposition 27". Proof idea: `IsTiling.lower_part`, then `three_copy`. -/
theorem prop31_vi (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) :
    ¬ ((κ z₁).boxY a = b - a - a ∧ (κ z₂).boxY a = b - a - a) := by
  rintro ⟨h1, h2⟩
  have hn := L.nums
  have F := L.h1.frame
  have hne := L.ne
  have he : Function.Injective (![i₀, z₁, z₂] : Fin 3 → Fin 5) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [hne.1.2.2.1, hne.1.2.2.2, hne.2.2.2, hne.1.2.2.1.symm, hne.1.2.2.2.symm,
        hne.2.2.2.symm] at hij ⊢
  refine three_copy (t i₀) F.poly F.nonrect a (b - a) _
    (F.isTiling.lower_part ![i₀, z₁, z₂] he (c := b - a) (by omega) (by omega) ?_ ?_)
  · intro j p hp
    obtain ⟨x, y⟩ := p
    fin_cases j
    · have := L.bT (X := x) (Y := y) hp
      dsimp only
      omega
    · have := L.bz₁ (X := x) (Y := y) hp
      dsimp only
      omega
    · have := L.bz₂ (X := x) (Y := y) hp
      dsimp only
      omega
  · rintro i hi ⟨x, y⟩ hp
    rcases L.index_cases i with rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl (hi 0)
    · exact (L.bw₁ hp).2.2.1
    · exact (L.bw₂ hp).2.2.1
    · exact absurd rfl (hi 1)
    · exact absurd rfl (hi 2)

/-! ## Section 5a: the walls -/

/-- A cell of column 0 is on the boundary of `R a b`. -/
theorem onLeft (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) {y : ℤ} (h0 : 0 ≤ y) (hb : y < b) :
    OnBoundary a b (0, y) := by
  have hn := L.nums
  exact ⟨mem_R.2 ⟨⟨le_rfl, by dsimp only; omega⟩, h0, hb⟩, Or.inl rfl⟩

theorem two_le_ab (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) : 2 ≤ a ∧ 2 ≤ b :=
  L.h1.frame.two_le

theorem sub (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (i : Fin 5) : t i ⊆ R a b :=
  L.h1.frame.isTiling.subset_R i

theorem conn (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (i : Fin 5) : EdgeConnected (t i) :=
  (L.h1.frame.isTiling.tile_isPolyomino L.h1.frame.poly i).2

/-- Lemma 32 (a) at column 0. -/
theorem col0_T (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (y : ℤ) :
    (0, y) ∈ t i₀ ↔ 0 ≤ y ∧ y < colCount (t i₀) 0 := by
  have hn := L.nums
  have hab := L.two_le_ab
  have h00 : ((0, 0) : Cell) ∈ t i₀ := L.h1.frame.row0 0 le_rfl (by omega)
  have h := mem_iff_of_initial (A := colSet (t i₀) 0) (lo := 0)
    (fun y hy => (L.bT (mem_colSet.1 hy)).2.2.1) ?_ y
  · rwa [mem_colSet, card_colSet, zero_add] at h
  · intro y hy z hz0 hzy
    rw [mem_colSet] at hy ⊢
    by_contra hz
    have hyb := L.bT hy
    have hzy' : z < y := lt_of_le_of_ne hzy fun h => hz (h ▸ hy)
    have hz0' : 0 < z := lt_of_le_of_ne hz0 fun h => hz (h ▸ h00)
    have hzz : (0, z) ∈ t z₁ := by
      rcases L.tile_at (X := 0) (Y := z) le_rfl (by omega) hz0 (by omega)
        with h | h | h | h | h
      · exact absurd h hz
      · have := L.bw₁ h
        omega
      · have := L.bw₂ h
        omega
      · exact h
      · have := L.bz₂ h
        omega
    obtain ⟨c, hc, hc'⟩ := interlace_left hab.1 hab.2 (L.sub i₀) (L.conn i₀) (L.sub z₁)
      (L.conn z₁) hz0' hzy' h00 hy hzz (L.onLeft (y := d) (by omega) (by omega))
      (L.prop31_iii.1 0 d le_rfl (by omega) le_rfl (by omega))
      (by dsimp only; omega)
    exact L.uniq hc hc' L.ne.1.2.2.1

theorem u₀_bounds (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) :
    1 ≤ colCount (t i₀) 0 ∧ colCount (t i₀) 0 ≤ d := by
  have hn := L.nums
  have h0 := (L.col0_T 0).1 (L.h1.frame.row0 0 le_rfl (by omega))
  refine ⟨by omega, ?_⟩
  by_contra hd
  have h1 := L.bT ((L.col0_T d).2 ⟨by omega, by omega⟩)
  omega

/-- Lemma 32 (b) with the cells of column 0 in `Z_1` and `W_1`. -/
theorem col0 (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) :
    ∃ ρ : ℤ, b - a ≤ ρ ∧ ρ < b ∧
      (∀ y : ℤ, (0, y) ∈ t z₁ ↔ colCount (t i₀) 0 ≤ y ∧ y < ρ) ∧
      ∀ y : ℤ, (0, y) ∈ t w₁ ↔ ρ ≤ y ∧ y < b := by
  have hn := L.nums
  have hab := L.two_le_ab
  have hu := L.u₀_bounds
  have hz := L.z₁box
  have htop : (0, b - 1) ∈ t w₁ :=
    L.prop31_iii.2.2.1 0 (b - 1) le_rfl (by omega) (by omega) (by omega)
  obtain ⟨ρ, hρ, hmin⟩ := (colSet (t w₁) 0).exists_min_image id ⟨b - 1, mem_colSet.2 htop⟩
  simp only [id, mem_colSet] at hρ hmin
  have hρb := L.bw₁ hρ
  have hup : ∀ y, ρ ≤ y → y < b → (0, y) ∈ t w₁ := by
    intro y hy hyb
    by_contra hyw
    have hρy : ρ < y := lt_of_le_of_ne hy fun h => hyw (h ▸ hρ)
    have hyz : (0, y) ∈ t z₁ := by
      rcases L.tile_at (X := 0) (Y := y) le_rfl (by omega) (by omega) hyb
        with h | h | h | h | h
      · have := L.bT h
        omega
      · exact absurd h hyw
      · have := L.bw₂ h
        omega
      · exact h
      · have := L.bz₂ h
        omega
    obtain ⟨c, hc, hc'⟩ := interlace_left hab.1 hab.2 (L.sub z₁) (L.conn z₁) (L.sub w₁)
      (L.conn w₁) (by omega : d < ρ) hρy
      (L.prop31_iii.1 0 d le_rfl (by omega) le_rfl (by omega)) hyz hρ
      (L.onLeft (y := b - 1) (by omega) (by omega)) htop (by dsimp only; omega)
    exact L.uniq hc hc' L.ne.2.1.2.1.symm
  have hlow : ∀ y, colCount (t i₀) 0 ≤ y → y < ρ → (0, y) ∈ t z₁ := by
    intro y hy hyρ
    rcases L.tile_at (X := 0) (Y := y) le_rfl (by omega) (by omega) (by omega)
      with h | h | h | h | h
    · have := (L.col0_T y).1 h
      omega
    · have := hmin y h
      omega
    · have := L.bw₂ h
      omega
    · exact h
    · have := L.bz₂ h
      omega
  refine ⟨ρ, hρb.2.2.1, hρb.2.2.2, fun y => ⟨fun h => ?_, fun h => hlow y h.1 h.2⟩,
    fun y => ⟨fun h => ⟨hmin y h, (L.bw₁ h).2.2.2⟩, fun h => hup y h.1 h.2⟩⟩
  have hb := L.bz₁ h
  constructor
  · by_contra hlt
    exact L.uniq ((L.col0_T y).2 ⟨by omega, by omega⟩) h L.ne.1.2.2.1
  · by_contra hlt
    exact L.uniq (hup y (by omega) (by omega)) h L.ne.2.1.2.1

theorem colA_T (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (y : ℤ) :
    (a - 1, y) ∈ t i₀ ↔ 0 ≤ y ∧ y < colCount (t i₀) (a - 1) := by
  have h := L.mirror.col0_T y
  simpa only [mem_flip, colCount_image_flipX, sub_zero] using h

theorem u₁_bounds (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) :
    1 ≤ colCount (t i₀) (a - 1) ∧ colCount (t i₀) (a - 1) ≤ d := by
  have h := L.mirror.u₀_bounds
  simpa only [colCount_image_flipX, sub_zero] using h

/-- Lemma 32 (b) with the cells of column `a - 1` in `Z_2` and `W_2`. -/
theorem colA (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) :
    ∃ ρ : ℤ, b - a ≤ ρ ∧ ρ < b ∧
      (∀ y : ℤ, (a - 1, y) ∈ t z₂ ↔ colCount (t i₀) (a - 1) ≤ y ∧ y < ρ) ∧
      ∀ y : ℤ, (a - 1, y) ∈ t w₂ ↔ ρ ≤ y ∧ y < b := by
  have h := L.mirror.col0
  simpa only [mem_flip, colCount_image_flipX, sub_zero] using h

/-- Lemma 32 (b) at column 0: `y_1 <= u_0`. -/
theorem y₁_le (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) :
    (κ z₁).boxY a ≤ colCount (t i₀) 0 := by
  have hn := L.nums
  have hu := L.u₀_bounds
  obtain ⟨ρ, h1, -, h3, -⟩ := L.col0
  exact (L.bz₁ ((h3 (colCount (t i₀) 0)).2 ⟨le_rfl, by omega⟩)).2.2.1

theorem y₂_le (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) :
    (κ z₂).boxY a ≤ colCount (t i₀) (a - 1) := by
  have hn := L.nums
  have hu := L.u₁_bounds
  obtain ⟨ρ, h1, -, h3, -⟩ := L.colA
  exact (L.bz₂ ((h3 (colCount (t i₀) (a - 1))).2 ⟨le_rfl, by omega⟩)).2.2.1


/-- Lemma 32 (a). PROVISIONAL. Source: `report-4.md`, Lemma 32 (a) (line 186): "T
meets column 0 in rows 0, ..., u_0 - 1 exactly, and column a - 1 in rows
0, ..., u_1 - 1." Proof idea: `interlace_left` on `T`, `Z_1`, `T`, `Z_1`. -/
theorem lemma32a (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) :
    (∀ y : ℤ, (0, y) ∈ t i₀ ↔ 0 ≤ y ∧ y < colCount (t i₀) 0) ∧
      ∀ y : ℤ, (a - 1, y) ∈ t i₀ ↔ 0 ≤ y ∧ y < colCount (t i₀) (a - 1) := by
  exact ⟨L.col0_T, L.colA_T⟩

/-- Lemma 32 (b). PROVISIONAL. Source: `report-4.md`, Lemma 32 (b) (line 187):
column 0 reads `T`, `Z_1`, `W_1` from the bottom, so `y_1 <= u_0`. -/
theorem lemma32b (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) :
    (κ z₁).boxY a ≤ colCount (t i₀) 0 ∧
      ∃ ρ : ℤ, b - a ≤ ρ ∧
        (∀ y : ℤ, colCount (t i₀) 0 ≤ y → y < ρ → (0, y) ∈ t z₁) ∧
        ∀ y : ℤ, ρ ≤ y → y < b → (0, y) ∈ t w₁ := by
  obtain ⟨ρ, h1, -, h3, h4⟩ := L.col0
  exact ⟨L.y₁_le, ρ, h1, fun y hy hρ => (h3 y).2 ⟨hy, hρ⟩, fun y hy hb => (h4 y).2 ⟨hy, hb⟩⟩

/-- `Z_1` outer: its cells in column 0 are its spine. -/
theorem z₁_spine (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz : (κ z₁).negX = false) (y : ℤ) :
    (0, y) ∈ t z₁ ↔ (κ z₁).boxY a ≤ y ∧ y < (κ z₁).boxY a + a := by
  refine ⟨fun h => (L.bz₁ h).2.2, fun h => ?_⟩
  have := spine_right L.h1.frame L.vz₁ hz h.1 h.2
  rwa [L.z₁box.1] at this

/-- `Z_1` inner: its cells in column `d - 1` are its spine. -/
theorem z₁_spine' (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz : (κ z₁).negX = true) (y : ℤ) :
    (d - 1, y) ∈ t z₁ ↔ (κ z₁).boxY a ≤ y ∧ y < (κ z₁).boxY a + a := by
  refine ⟨fun h => (L.bz₁ h).2.2, fun h => ?_⟩
  have := spine_left L.h1.frame L.vz₁ hz h.1 h.2
  rwa [L.z₁box.1, zero_add] at this

/-- `W_1` outer: its cells in column 0 are its spine. -/
theorem w₁_spine (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hw : (κ w₁).negX = false) (y : ℤ) :
    (0, y) ∈ t w₁ ↔ b - a ≤ y ∧ y < b := by
  refine ⟨fun h => (L.bw₁ h).2.2, fun h => ?_⟩
  have hb := L.w₁box
  have := spine_right L.h1.frame L.vw₁ hw (Y := y) (by omega) (by omega)
  rwa [hb.1] at this

/-- `W_1` inner: its cells in column `d - 1` are its spine. -/
theorem w₁_spine' (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hw : (κ w₁).negX = true) (y : ℤ) :
    (d - 1, y) ∈ t w₁ ↔ b - a ≤ y ∧ y < b := by
  refine ⟨fun h => (L.bw₁ h).2.2, fun h => ?_⟩
  have hb := L.w₁box
  have := spine_left L.h1.frame L.vw₁ hw (Y := y) (by omega) (by omega)
  rwa [hb.1, zero_add] at this

/-- `Z_2` inner: its cells in column `a - d` are its spine. -/
theorem z₂_spine' (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz : (κ z₂).negX = false) (y : ℤ) :
    (a - d, y) ∈ t z₂ ↔ (κ z₂).boxY a ≤ y ∧ y < (κ z₂).boxY a + a := by
  refine ⟨fun h => (L.bz₂ h).2.2, fun h => ?_⟩
  have := spine_right L.h1.frame L.vz₂ hz h.1 h.2
  rwa [L.z₂box.1] at this

/-- `W_2` inner: its cells in column `a - d` are its spine. -/
theorem w₂_spine' (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hw : (κ w₂).negX = false) (y : ℤ) :
    (a - d, y) ∈ t w₂ ↔ b - a ≤ y ∧ y < b := by
  refine ⟨fun h => (L.bw₂ h).2.2, fun h => ?_⟩
  have hb := L.w₂box
  have := spine_right L.h1.frame L.vw₂ hw (Y := y) (by omega) (by omega)
  rwa [hb.1] at this

/-- `W_2` outer: its cells in column `a - 1` are its spine. -/
theorem w₂_spine (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hw : (κ w₂).negX = true) (y : ℤ) :
    (a - 1, y) ∈ t w₂ ↔ b - a ≤ y ∧ y < b := by
  refine ⟨fun h => (L.bw₂ h).2.2, fun h => ?_⟩
  have hb := L.w₂box
  have := spine_left L.h1.frame L.vw₂ hw (Y := y) (by omega) (by omega)
  rwa [hb.1, sub_add_cancel] at this

/-- Lemma 32 (d), `Z_1` outer: `u_0 = y_1` and `Z_1` ends column 0 at `y_1 + a`. -/
theorem col0_outer (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz : (κ z₁).negX = false) :
    colCount (t i₀) 0 = (κ z₁).boxY a ∧
      ∀ y : ℤ, (0, y) ∈ t w₁ ↔ (κ z₁).boxY a + a ≤ y ∧ y < b := by
  have hn := L.nums
  have hu := L.u₀_bounds
  obtain ⟨ρ, h1, h2, h3, h4⟩ := L.col0
  have h := interval_eq (lo := colCount (t i₀) 0) (hi := ρ)
    (fun y => (h3 y).symm.trans (L.z₁_spine hz y)) (by omega)
  refine ⟨h.1, fun y => ?_⟩
  rw [h4, h.2]

/-- Lemma 32 (d), `W_1` outer: column 0 holds `Z_1` in the rows `[u_0, h)`. -/
theorem col0_top_outer (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hw : (κ w₁).negX = false)
    (y : ℤ) : (0, y) ∈ t z₁ ↔ colCount (t i₀) 0 ≤ y ∧ y < b - a := by
  have hn := L.nums
  obtain ⟨ρ, h1, h2, h3, h4⟩ := L.col0
  have h := interval_eq (lo := ρ) (hi := b)
    (fun y => (h4 y).symm.trans (L.w₁_spine hw y)) h2
  rw [h3, h.1]

/-- Lemma 32 (d), `W_2` outer: column `a - 1` holds `Z_2` in the rows `[u_1, h)`. -/
theorem colA_top_outer (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hw : (κ w₂).negX = true)
    (y : ℤ) : (a - 1, y) ∈ t z₂ ↔ colCount (t i₀) (a - 1) ≤ y ∧ y < b - a := by
  have hn := L.nums
  obtain ⟨ρ, h1, h2, h3, h4⟩ := L.colA
  have h := interval_eq (lo := ρ) (hi := b)
    (fun y => (h4 y).symm.trans (L.w₂_spine hw y)) h2
  rw [h3, h.1]

/-- Case C at the left wall: the top row of `T` through `Z_1`. -/
theorem top_C (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz : (κ z₁).negX = true)
    (hw : (κ w₁).negX = false) (x : ℤ) :
    (x, d - 1) ∈ t i₀ ↔ colCount (t i₀) 0 ≤ place (κ z₁) a x ∧ place (κ z₁) a x < b - a := by
  rw [← L.col0_top_outer hw, L.z₁_inner hz, ord_place, sub_zero]

/-- Case C' at the right wall: the top row of `T` through `Z_2`. -/
theorem top_C' (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz : (κ z₂).negX = false)
    (hw : (κ w₂).negX = true) (x : ℤ) :
    (x, d - 1) ∈ t i₀ ↔
      colCount (t i₀) (a - 1) ≤ place (κ z₂) a x ∧ place (κ z₂) a x < b - a := by
  rw [← L.colA_top_outer hw, L.z₂_inner hz, ord_place]
  have e : a - 1 - (a - d) = d - 1 := by ring
  rw [e]

/-- Case C: `t = h - u_0`. -/
theorem count_C (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz : (κ z₁).negX = true)
    (hw : (κ w₁).negX = false) :
    rowCount (t i₀) (d - 1) = b - a - colCount (t i₀) 0 := by
  have hn := L.nums
  have hu := L.u₀_bounds
  have h1 := colCount_left L.h1.frame L.vz₁ hz 0
  rw [L.z₁box.1, zero_add, sub_zero] at h1
  rw [← h1]
  exact colCount_of_interval (by omega) (L.col0_top_outer hw)

/-- Case C': `t = h - u_1`. -/
theorem count_C' (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz : (κ z₂).negX = false)
    (hw : (κ w₂).negX = true) :
    rowCount (t i₀) (d - 1) = b - a - colCount (t i₀) (a - 1) := by
  have hn := L.nums
  have hu := L.u₁_bounds
  have h1 := colCount_right L.h1.frame L.vz₂ hz (a - 1)
  have e : a - 1 - (a - d) = d - 1 := by ring
  rw [L.z₂box.1, e] at h1
  rw [← h1]
  exact colCount_of_interval (by omega) (L.colA_top_outer hw)


/-- Lemma 32 (d), case A (`Z_1`, `W_1` outer). PROVISIONAL. Source: `report-4.md`,
Lemma 32 (d) (line 190): `u_0 = y_1 = h - a`. -/
theorem lemma32d_A (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz : (κ z₁).negX = false)
    (hw : (κ w₁).negX = false) :
    colCount (t i₀) 0 = (κ z₁).boxY a ∧ (κ z₁).boxY a = b - a - a := by
  have hn := L.nums
  obtain ⟨h1, h2⟩ := L.col0_outer hz
  have hzb := L.z₁box
  have h3 := interval_eq (lo := b - a) (hi := b)
    (fun y => (L.w₁_spine hw y).symm.trans (h2 y)) (by omega)
  exact ⟨h1, by omega⟩

/-- Lemma 32 (d), case B (`Z_1` outer, `W_1` inner). PROVISIONAL. Source:
`report-4.md`, Lemma 32 (d) (line 191): `u_0 = y_1`, `t = h - y_1`, and Top is an
end interval of `t` columns. -/
theorem lemma32d_B (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz : (κ z₁).negX = false)
    (hw : (κ w₁).negX = true) :
    colCount (t i₀) 0 = (κ z₁).boxY a ∧
      rowCount (t i₀) (d - 1) = b - a - (κ z₁).boxY a ∧
      ((∀ x : ℤ, (x, d - 1) ∈ t i₀ ↔ 0 ≤ x ∧ x < rowCount (t i₀) (d - 1)) ∨
        ∀ x : ℤ, (x, d - 1) ∈ t i₀ ↔ a - rowCount (t i₀) (d - 1) ≤ x ∧ x < a) := by
  have hn := L.nums
  obtain ⟨h1, h2⟩ := L.col0_outer hz
  have hzb := L.z₁box
  have hwb := L.w₁box
  have htop : ∀ x : ℤ, (x, d - 1) ∈ t i₀ ↔
      (κ z₁).boxY a + a ≤ place (κ w₁) a x ∧ place (κ w₁) a x < b := by
    intro x
    rw [← h2, L.w₁_inner hw, ord_place, sub_zero]
  cases hy : (κ w₁).negY
  · have h3 : ∀ x : ℤ, (x, d - 1) ∈ t i₀ ↔ a - (b - a - (κ z₁).boxY a) ≤ x ∧ x < a := by
      intro x
      rw [htop, place_keep hy, hwb.2]
      omega
    have h4 := rowCount_of_interval (by omega) h3
    have h5 : rowCount (t i₀) (d - 1) = b - a - (κ z₁).boxY a := by omega
    exact ⟨h1, h5, Or.inr (by rw [h5]; exact h3)⟩
  · have h3 : ∀ x : ℤ, (x, d - 1) ∈ t i₀ ↔ 0 ≤ x ∧ x < b - a - (κ z₁).boxY a := by
      intro x
      rw [htop, place_rev hy, hwb.2]
      omega
    have h4 := rowCount_of_interval (by omega) h3
    have h5 : rowCount (t i₀) (d - 1) = b - a - (κ z₁).boxY a := by omega
    exact ⟨h1, h5, Or.inl (by rw [h5]; exact h3)⟩

/-- Lemma 32 (d), case C (`Z_1` inner, `W_1` outer). PROVISIONAL. Source:
`report-4.md`, Lemma 32 (d) (line 192): `t = h - u_0`, and Top is the interval
`sigma_1([u_0 - y_1, h - y_1))`. -/
theorem lemma32d_C (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz : (κ z₁).negX = true)
    (hw : (κ w₁).negX = false) :
    rowCount (t i₀) (d - 1) = b - a - colCount (t i₀) 0 ∧
      ∀ x : ℤ, (x, d - 1) ∈ t i₀ ↔
        colCount (t i₀) 0 ≤ (if (κ z₁).negY then -x else x) + (κ z₁).shift.2 ∧
          (if (κ z₁).negY then -x else x) + (κ z₁).shift.2 < b - a := by
  refine ⟨L.count_C hz hw, fun x => ?_⟩
  rw [← place_eq]
  exact L.top_C hz hw x

/-- Lemma 32 (d), case D (`Z_1`, `W_1` inner). PROVISIONAL. Source: `report-4.md`,
Lemma 32 (d) (line 193): `y_1 = h - a`, `t = a`, `u_0 = u_1 = d` and `h = a + d`. -/
theorem lemma32d_D (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz : (κ z₁).negX = true)
    (hw : (κ w₁).negX = true) :
    (κ z₁).boxY a = b - a - a ∧ rowCount (t i₀) (d - 1) = a ∧ colCount (t i₀) 0 = d ∧
      colCount (t i₀) (a - 1) = d ∧ b - a = a + d := by
  have hn := L.nums
  have hzb := L.z₁box
  have hwb := L.w₁box
  have hy : (κ z₁).boxY a = b - a - a := by
    by_contra hne
    exact L.uniq ((L.z₁_spine' hz (b - a)).2 ⟨by omega, by omega⟩)
      ((L.w₁_spine' hw (b - a)).2 ⟨le_rfl, by omega⟩) L.ne.2.1.2.1.symm
  obtain ⟨ρ, h1, h2, h3, h4⟩ := L.col0
  have hρ : ρ = b - a := by
    by_contra hne
    have := L.bz₁ ((h3 (b - a)).2 ⟨by have := L.u₀_bounds; omega, by omega⟩)
    omega
  subst hρ
  have htop : ∀ x : ℤ, 0 ≤ x → x < a → (x, d - 1) ∈ t i₀ := by
    intro x hx0 hxa
    have h5 := (place_range (g := κ w₁) (a := a) (x := x)).2 ⟨hx0, hxa⟩
    have h6 := (h4 (place (κ w₁) a x)).2 ⟨by omega, by omega⟩
    rwa [L.w₁_inner hw, ord_place, sub_zero] at h6
  have ht : rowCount (t i₀) (d - 1) = a := by
    rw [rowCount_of_interval (lo := 0) (hi := a) (by omega), sub_zero]
    exact fun x => ⟨fun h => ⟨(L.bT h).1, (L.bT h).2.1⟩, fun h => htop x h.1 h.2⟩
  have hu₀ := (L.col0_T (d - 1)).1 (htop 0 le_rfl (by omega))
  have hu₁ := (L.colA_T (d - 1)).1 (htop (a - 1) (by omega) (by omega))
  have hb₀ := L.u₀_bounds
  have hb₁ := L.u₁_bounds
  have hc := colCount_left L.h1.frame L.vz₁ hz 0
  rw [hzb.1, zero_add, sub_zero, ht,
    colCount_of_interval (lo := colCount (t i₀) 0) (hi := b - a) (by omega) h3] at hc
  exact ⟨hy, ht, by omega, by omega, by omega⟩

/-- Lemma 32a. PROVISIONAL. Source: `report-4.md`, Lemma 32a (line 214): "In the
layout of Proposition 31, if W_1 or W_2 is inner then a = 2d." -/
theorem lemma32a_inner (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂)
    (h : (κ w₁).negX = true ∨ (κ w₂).negX = false) : a = 2 * d := by
  have hn := L.nums
  have hwb₁ := L.w₁box
  have hwb₂ := L.w₂box
  by_contra hne
  rcases h with h | h
  · obtain ⟨Y, hY⟩ := vert_exists_col L.h1.frame L.vw₂ (X := d - 1) (by omega) (by omega)
    have hb := L.bw₂ hY
    exact L.uniq ((L.w₁_spine' h Y).2 hb.2.2) hY L.ne.2.1.1
  · obtain ⟨Y, hY⟩ := vert_exists_col L.h1.frame L.vw₁ (X := a - d) (by omega) (by omega)
    have hb := L.bw₁ hY
    exact L.uniq ((L.w₂_spine' h Y).2 hb.2.2) hY L.ne.2.1.1.symm

/-! ## Sections 5a, 5b: the ten pairs of wall cases -/

/-- Case D is excluded. PROVISIONAL. Source: `report-4.md`, Proposition 34 (line
226): "Lemma 32a gives a = 2d and Lemma 32 (d) gives h = a + d, so a + h = 5d,
against Proposition 31 (i)." Covers every pair with D; the pairs with D' are its
mirror images. -/
theorem excl_D (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz : (κ z₁).negX = true)
    (hw : (κ w₁).negX = true) : False := by
  have hn := L.nums
  have h1 := L.lemma32a_inner (Or.inl hw)
  have h2 := L.lemma32d_D hz hw
  omega

/-- The four switches in the mirror image. -/
theorem mirror_negX {i : Fin 5} (hs : (κ i).swap = true) {v : Bool} (h : (κ i).negX = v) :
    ((GridIso.flipX a).comp ((κ i).comp (GridIso.flipX a))).negX = !v := by
  rw [← h]
  exact mir_negX hs a

theorem mirror_boxY {i : Fin 5} (hs : (κ i).swap = true) :
    ((GridIso.flipX a).comp ((κ i).comp (GridIso.flipX a))).boxY a = (κ i).boxY a :=
  mir_boxY hs a

/-- The rows below `y_1 <= y_2` are in `T`. -/
theorem full_below (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂)
    (h : (κ z₁).boxY a ≤ (κ z₂).boxY a) (x y : ℤ) (hx0 : 0 ≤ x) (hxa : x < a) (hy0 : 0 ≤ y)
    (hy : y < (κ z₁).boxY a) : (x, y) ∈ t i₀ := by
  have hn := L.nums
  have hz := L.z₁box
  rcases L.tile_at hx0 hxa hy0 (by omega : y < b) with h' | h' | h' | h' | h'
  · exact h'
  · have := L.bw₁ h'
    omega
  · have := L.bw₂ h'
    omega
  · have := L.bz₁ h'
    omega
  · have := L.bz₂ h'
    omega

/-- The cells of row `b - 1` are in the two top tiles. -/
theorem top_row (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (x : ℤ) (hx0 : 0 ≤ x) (hxa : x < a) :
    (x, b - 1) ∈ t w₁ ∨ (x, b - 1) ∈ t w₂ := by
  have hn := L.nums
  have hz₁ := L.z₁box
  have hz₂ := L.z₂box
  rcases L.tile_at hx0 hxa (by omega : 0 ≤ b - 1) (by omega) with h | h | h | h | h
  · have := L.bT h
    omega
  · exact Or.inl h
  · exact Or.inr h
  · have := L.bz₁ h
    omega
  · have := L.bz₂ h
    omega

/-- `W_1` inner: `a = 2d` and an end column of `T` is full (Lemma 32 (c)). -/
theorem full_end (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hw : (κ w₁).negX = true) :
    a = 2 * d ∧ (colCount (t i₀) 0 = d ∨ colCount (t i₀) (a - 1) = d) := by
  have hn := L.nums
  have ha := L.lemma32a_inner (Or.inl hw)
  have hu := L.u₀_bounds
  have hv := L.u₁_bounds
  have h0 : (0, b - 1) ∈ t w₁ := by
    rcases L.top_row 0 le_rfl (by omega) with h | h
    · exact h
    · have := L.bw₂ h
      omega
  rw [L.w₁_inner hw, ord_top _ _ _ L.w₁box.2, sub_zero] at h0
  refine ⟨ha, ?_⟩
  split at h0
  · have := (L.col0_T _).1 h0
    omega
  · have := (L.colA_T _).1 h0
    omega


/-- The pair AA' is excluded. PROVISIONAL. Source: `report-4.md`, Proposition 33
(line 203): both `y_i = h - a`, against Proposition 31 (vi). -/
theorem excl_AA (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz₁ : (κ z₁).negX = false)
    (hw₁ : (κ w₁).negX = false) (hz₂ : (κ z₂).negX = true) (hw₂ : (κ w₂).negX = true) :
    False := by
  have h1 := L.lemma32d_A hz₁ hw₁
  have h2 := L.mirror.lemma32d_A (mirror_negX L.vz₂ hz₂) (mirror_negX L.vw₂ hw₂)
  rw [mirror_boxY L.vz₂] at h2
  exact L.prop31_vi ⟨h1.2, h2.2⟩

/-- The pair BB' is excluded. PROVISIONAL. Source: `report-4.md`, Proposition 33
(line 203). -/
theorem excl_BB (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz₁ : (κ z₁).negX = false)
    (hw₁ : (κ w₁).negX = true) (hz₂ : (κ z₂).negX = true) (hw₂ : (κ w₂).negX = false) :
    False := by
  have hn := L.nums
  have h1 := L.lemma32d_B hz₁ hw₁
  have h2 := L.mirror.lemma32d_B (mirror_negX L.vz₂ hz₂) (mirror_negX L.vw₂ hw₂)
  rw [mirror_boxY L.vz₂, colCount_image_flipX, rowCount_image_flipX, sub_zero] at h2
  obtain ⟨ha, hfull⟩ := L.full_end hw₁
  have hu := L.u₀_bounds
  have hv := L.u₁_bounds
  refine base_not_full L.h1.frame fun x y hx0 hxa hy0 hyd => ?_
  exact L.full_below (by omega) x y hx0 hxa hy0 (by omega)

/-- The pair CC', counts: `u_0 = u_1 = a / 2`, `t = h - a / 2` and `e = a - d <= d - 2`.
Source: `report-4.md`, Proposition 33 (line 203) and Proposition 34 (line 230). -/
theorem CC_counts (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz₁ : (κ z₁).negX = true)
    (hw₁ : (κ w₁).negX = false) (hz₂ : (κ z₂).negX = false) (hw₂ : (κ w₂).negX = true) :
    colCount (t i₀) (a - 1) = colCount (t i₀) 0 ∧ a = 2 * colCount (t i₀) 0 ∧
      rowCount (t i₀) (d - 1) = b - a - colCount (t i₀) 0 ∧ a - d ≤ d - 2 := by
  have hn := L.nums
  have h1 := L.count_C hz₁ hw₁
  have h2 := L.count_C' hz₂ hw₂
  have hu := L.u₀_bounds
  have huv : colCount (t i₀) (a - 1) = colCount (t i₀) 0 := by omega
  -- the top row
  have hW₁ : ∀ X, (X, b - 1) ∈ t w₁ ↔ 0 ≤ X ∧ X < colCount (t i₀) 0 := by
    intro X
    rw [L.w₁_outer hw₁, ord_top _ _ _ L.w₁box.2]
    split
    · exact L.col0_T X
    · rw [L.colA_T, huv]
  have hW₂ : ∀ X, (X, b - 1) ∈ t w₂ ↔ 0 ≤ a - 1 - X ∧ a - 1 - X < colCount (t i₀) 0 := by
    intro X
    rw [L.w₂_outer hw₂, ord_top _ _ _ L.w₂box.2]
    split
    · exact L.col0_T _
    · rw [L.colA_T, huv]
  have ha : a = 2 * colCount (t i₀) 0 := by
    have hle : a ≤ 2 * colCount (t i₀) 0 := by
      rcases L.top_row (colCount (t i₀) 0) (by omega) (by omega) with h | h
      · have := (hW₁ _).1 h
        omega
      · have := (hW₂ _).1 h
        omega
    by_contra hne
    exact L.uniq ((hW₁ (colCount (t i₀) 0 - 1)).2 ⟨by omega, by omega⟩)
      ((hW₂ _).2 ⟨by omega, by omega⟩) L.ne.2.1.1
  refine ⟨huv, ha, h1, ?_⟩
  by_contra hcon
  -- `a = 2d`: the top row of `T` reaches both end columns
  have hd : colCount (t i₀) 0 = d := by omega
  have c0 := (L.top_C hz₁ hw₁ 0).1 ((L.col0_T (d - 1)).2 ⟨by omega, by omega⟩)
  have c1 := (L.top_C hz₁ hw₁ (a - 1)).1 ((L.colA_T (d - 1)).2 ⟨by omega, by omega⟩)
  cases hy : (κ z₁).negY
  · rw [place_keep hy] at c0 c1
    omega
  · rw [place_rev hy] at c0 c1
    omega

/-- The pair CC' with `y_1 < y_2`. Source: `report-4.md`, Proposition 34 (lines
230-235), steps (1) to (5). -/
theorem CC_lt (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz₁ : (κ z₁).negX = true)
    (hw₁ : (κ w₁).negX = false) (hz₂ : (κ z₂).negX = false) (hw₂ : (κ w₂).negX = true)
    (hlt : (κ z₁).boxY a < (κ z₂).boxY a) : False := by
  have hn := L.nums
  have F := L.h1.frame
  obtain ⟨huv, ha, ht, he⟩ := L.CC_counts hz₁ hw₁ hz₂ hw₂
  have hu := L.u₀_bounds
  have hz₁b := L.z₁box
  have hz₂b := L.z₂box
  have hw₁b := L.w₁box
  have hw₂b := L.w₂box
  have hfull := L.full_below hlt.le
  have hy₂ := L.y₂_le
  have hiii := L.prop31_iii
  -- (1) `Z_1` reverses the order, `Z_2` keeps it, `y_1 + y_2 = t`
  have hr₁ : (κ z₁).negY = true := by
    by_contra hk
    rw [Bool.not_eq_true] at hk
    have h1 : (d - (κ z₁).boxY a, d - 1) ∈ t i₀ := by
      rw [L.top_C hz₁ hw₁, place_keep hk]
      omega
    have h2 : (d - (κ z₁).boxY a, d - 1) ∈ t z₁ := by
      rw [L.z₁_inner hz₁]
      have := (ord_range (g := κ z₁) (a := a) (Y := d - 1)).2 ⟨by omega, by omega⟩
      exact hfull _ _ this.1 this.2 (by omega) (by omega)
    exact L.uniq h1 h2 L.ne.1.2.2.1
  have htop₁ : ∀ x : ℤ, (x, d - 1) ∈ t i₀ ↔
      (κ z₁).boxY a + a - (b - a) ≤ x ∧ x < (κ z₁).boxY a + a - colCount (t i₀) 0 := by
    intro x
    rw [L.top_C hz₁ hw₁, place_rev hr₁]
    omega
  have hk₂ : (κ z₂).negY = false := by
    by_contra hk
    rw [Bool.not_eq_false] at hk
    have h := interval_eq (fun x => (htop₁ x).symm.trans (L.top_C' hz₂ hw₂ x) |>.trans
      (b := colCount (t i₀) (a - 1) ≤ place (κ z₂) a x ∧ place (κ z₂) a x < b - a)
      (c := (κ z₂).boxY a + a - (b - a) ≤ x ∧
        x < (κ z₂).boxY a + a - colCount (t i₀) 0)
      (by rw [place_rev hk, huv]; omega)) (by omega)
    omega
  have hsum : (κ z₁).boxY a + (κ z₂).boxY a = b - a - colCount (t i₀) 0 := by
    have h := interval_eq (fun x => (htop₁ x).symm.trans (L.top_C' hz₂ hw₂ x) |>.trans
      (b := colCount (t i₀) (a - 1) ≤ place (κ z₂) a x ∧ place (κ z₂) a x < b - a)
      (c := colCount (t i₀) 0 - (κ z₂).boxY a ≤ x ∧ x < b - a - (κ z₂).boxY a)
      (by rw [place_keep hk₂, huv]; omega)) (by omega)
    omega
  -- (2) columns `a - d` and `d - 1`
  have hspine₂ := L.z₂_spine' hz₂
  have hspine₁ := L.z₁_spine' hz₁
  have cW : colCount (t w₁) (a - d) + colCount (t w₂) (a - d) =
      b - ((κ z₂).boxY a + a) := by
    refine colCount_add (by omega) (fun y => ⟨fun h => ?_, fun h => ?_⟩)
      fun y h h' => L.uniq h h' L.ne.2.1.1
    · have hb : b - a ≤ y ∧ y < b := by
        rcases h with h | h
        · exact (L.bw₁ h).2.2
        · exact (L.bw₂ h).2.2
      refine ⟨?_, hb.2⟩
      by_contra hy
      have hs := (hspine₂ y).2 ⟨by omega, by omega⟩
      rcases h with h | h
      · exact L.uniq h hs L.ne.2.1.2.2
      · exact L.uniq h hs L.ne.2.2.1.2
    · rcases L.tile_at (X := a - d) (Y := y) (by omega) (by omega) (by omega) h.2
        with h' | h' | h' | h' | h'
      · have := L.bT h'
        omega
      · exact Or.inl h'
      · exact Or.inr h'
      · have := L.bz₁ h'
        omega
      · have := L.bz₂ h'
        omega
  have cZ : colCount (t i₀) (a - d) + colCount (t z₁) (a - d) = (κ z₂).boxY a - 0 := by
    refine colCount_add (by omega) (fun y => ⟨fun h => ?_, fun h => ?_⟩)
      fun y h h' => L.uniq h h' L.ne.1.2.2.1
    · have hb : 0 ≤ y ∧ y < (κ z₁).boxY a + a := by
        rcases h with h | h
        · have := L.bT h
          omega
        · have := L.bz₁ h
          omega
      refine ⟨hb.1, ?_⟩
      by_contra hy
      have hs := (hspine₂ y).2 ⟨by omega, by omega⟩
      rcases h with h | h
      · exact L.uniq h hs L.ne.1.2.2.2
      · exact L.uniq h hs L.ne.2.2.2
    · rcases L.tile_at (X := a - d) (Y := y) (by omega) (by omega) (by omega) (by omega)
        with h' | h' | h' | h' | h'
      · exact Or.inl h'
      · have := L.bw₁ h'
        omega
      · have := L.bw₂ h'
        omega
      · exact Or.inr h'
      · have := L.bz₂ h'
        omega
  have hTd : ∀ y, (d - 1, y) ∈ t i₀ ↔ 0 ≤ y ∧ y < (κ z₁).boxY a := by
    refine fun y => ⟨fun h => ?_, fun h => hfull _ _ (by omega) (by omega) h.1 h.2⟩
    have hb := L.bT h
    refine ⟨hb.2.2.1, ?_⟩
    by_contra hy
    exact L.uniq h ((hspine₁ y).2 ⟨by omega, by omega⟩) L.ne.1.2.2.1
  have cTd := colCount_of_interval (by omega) hTd
  have cZd := colCount_of_interval (by omega) hspine₁
  have v1 := colCount_right F L.vw₁ hw₁ (a - d)
  have v2 := colCount_left F L.vw₂ hw₂ (a - d)
  have v3 := colCount_left F L.vz₁ hz₁ (a - d)
  have v4 := colCount_right F L.vw₁ hw₁ (d - 1)
  have v5 := colCount_right F L.vz₂ hz₂ (d - 1)
  have v6 := colCount_left F L.vw₂ hw₂ (d - 1)
  rw [hw₁b.1, sub_zero] at v1 v4
  rw [hw₂b.1, show a - d + d - 1 - (a - d) = d - 1 by ring] at v2
  rw [hw₂b.1, show a - d + d - 1 - (d - 1) = a - d by ring] at v6
  rw [hz₁b.1, zero_add] at v3
  rw [hz₂b.1] at v5
  have hcol := sum_colCount_of_cover t F.disjoint F.cover (by omega : (0 : ℤ) ≤ b)
    (x := d - 1) (by omega) (by omega)
  rw [L.sum_eq] at hcol
  have hue : colCount (t i₀) (a - d) = (κ z₁).boxY a := by omega
  -- (3) row `a - d` of `T` is not full
  have hse : (κ z₁).boxY a ≤ a - d := by
    by_contra hcon
    have h := rowCount_of_interval (S := t i₀) (y := a - d) (lo := 0) (hi := a) (by omega)
      fun x => ⟨fun h => ⟨(L.bT h).1, (L.bT h).2.1⟩,
        fun h => hfull x _ h.1 h.2 (by omega) (by omega)⟩
    omega
  -- (4) `T` holds an end interval of columns in full up to row `a - d`
  have hes : a - d ≤ (κ z₁).boxY a := by
    have hK : ∀ x j, 0 ≤ x → x < a → (κ z₂).boxY a + a ≤ place (κ w₂) a x → 0 ≤ j →
        j < a - d → (x, j) ∈ t i₀ := by
      intro x j hx0 hxa hp hj0 hj
      have hpr := (place_range (g := κ w₂) (a := a) (x := x)).2 ⟨hx0, hxa⟩
      have h := hiii.2.2.2 (a - 1 - j) (place (κ w₂) a x) (by omega) (by omega) hp (by omega)
      rwa [L.w₂_outer hw₂, ord_place, sub_sub_cancel] at h
    cases hy : (κ w₂).negY
    · have h := hK (d - 1) (a - d - 1) (by omega) (by omega)
        (by rw [place_keep hy]; omega) (by omega) (by omega)
      have := (hTd _).1 h
      omega
    · have h := le_colCount (S := t i₀) (x := a - d) (lo := 0) (hi := a - d)
        fun j hj0 hj => hK (a - d) j (by omega) (by omega)
          (by rw [place_rev hy]; omega) hj0 hj
      omega
  -- (5) the collision
  have h1 : (2 * (a - d) - 1, d - 1) ∈ t i₀ := by
    have h := hiii.1 0 d le_rfl (by omega) le_rfl (by omega)
    rw [L.z₁_inner hz₁, ord_rev hr₁, sub_zero] at h
    rwa [show (κ z₁).boxY a + a - 1 - d = 2 * (a - d) - 1 by omega] at h
  have h2 : (2 * (a - d) - 1, d - 1) ∈ t z₂ := by
    rw [L.z₂_inner hz₂]
    have := (ord_range (g := κ z₂) (a := a) (Y := d - 1)).2 ⟨by omega, by omega⟩
    exact hfull _ _ this.1 this.2 (by omega) (by omega)
  exact L.uniq h1 h2 L.ne.1.2.2.2


/-- The pair CC' is excluded. PROVISIONAL. Source: `report-4.md`, Proposition 33
(line 203) for `a - d >= d - 1` and Proposition 34 (lines 230-235), steps (1) to
(5), for `a - d <= d - 2`. -/
theorem excl_CC (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz₁ : (κ z₁).negX = true)
    (hw₁ : (κ w₁).negX = false) (hz₂ : (κ z₂).negX = false) (hw₂ : (κ w₂).negX = true) :
    False := by
  have hn := L.nums
  obtain ⟨-, -, -, he⟩ := L.CC_counts hz₁ hw₁ hz₂ hw₂
  rcases lt_trichotomy ((κ z₁).boxY a) ((κ z₂).boxY a) with h | h | h
  · exact L.CC_lt hz₁ hw₁ hz₂ hw₂ h
  · have hb := L.z₂box
    obtain ⟨Y, hY⟩ := vert_exists_col L.h1.frame L.vz₂ (X := d - 1) (by omega) (by omega)
    have hYb := L.bz₂ hY
    exact L.uniq ((L.z₁_spine' hz₁ Y).2 ⟨by omega, by omega⟩) hY L.ne.2.2.2
  · refine L.mirror.CC_lt (mirror_negX L.vz₂ hz₂) (mirror_negX L.vw₂ hw₂)
      (mirror_negX L.vz₁ hz₁) (mirror_negX L.vw₁ hw₁) ?_
    rw [mirror_boxY L.vz₁, mirror_boxY L.vz₂]
    exact h

/-- The pair AB' is excluded. PROVISIONAL. Source: `report-4.md`, Proposition 34
(line 224): `W_2` inner gives `a = 2d`, and `y_1 = h - a` makes `W_1` its whole
box. -/
theorem excl_AB (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz₁ : (κ z₁).negX = false)
    (hw₁ : (κ w₁).negX = false) (hz₂ : (κ z₂).negX = true) (hw₂ : (κ w₂).negX = false) :
    False := by
  have _ := hz₂ -- not needed: W_2 inner is enough
  have hn := L.nums
  have h1 := L.lemma32d_A hz₁ hw₁
  have ha := L.lemma32a_inner (Or.inr hw₂)
  refine base_not_full L.h1.frame fun x y hx0 hxa hy0 hyd => ?_
  have hp := (place_range (g := κ w₁) (a := a) (x := x)).2 ⟨hx0, hxa⟩
  have hwb := L.w₁box
  have h := L.prop31_iii.2.2.1 y (place (κ w₁) a x) hy0 (by omega) (by omega) (by omega)
  rwa [L.w₁_outer hw₁, ord_place] at h

/-- The pair AC', step (1): `y_1 = e`, `h = d + 2e` and `e < y_2` with `e = a - d`.
Source: `report-4.md`, Proposition 34 (lines 237, 238). -/
theorem AC_step1 (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz₁ : (κ z₁).negX = false)
    (hw₁ : (κ w₁).negX = false) (hz₂ : (κ z₂).negX = false) :
    colCount (t i₀) 0 = a - d ∧ (κ z₁).boxY a = a - d ∧ b - a = a + (a - d) ∧
      a - d < (κ z₂).boxY a := by
  have hn := L.nums
  obtain ⟨hu, hy₁⟩ := L.lemma32d_A hz₁ hw₁
  have hz₁b := L.z₁box
  have hz₂b := L.z₂box
  have hw₁b := L.w₁box
  have hy₂ : (κ z₂).boxY a ≠ b - a - a := fun h => L.prop31_vi ⟨hy₁, h⟩
  have hfull := L.full_below (by omega)
  -- `T` holds its bottom `a - d` rows
  have hes : a - d ≤ (κ z₁).boxY a := by
    by_contra hcon
    have hp := (place_range (g := κ w₁) (a := a) (x := 0)).2 ⟨le_rfl, by omega⟩
    have h := L.prop31_iii.2.2.1 ((κ z₁).boxY a) (place (κ w₁) a 0) (by omega) (by omega)
      (by omega) (by omega)
    rw [L.w₁_outer hw₁, ord_place] at h
    exact L.uniq h ((L.z₁_spine hz₁ _).2 ⟨le_rfl, by omega⟩) L.ne.1.2.2.1
  -- the thick spine of `Z_1` and the spine of `Z_2` share row `y_2`
  have hse : (κ z₁).boxY a ≤ a - d := by
    by_contra hcon
    have h1 : (a - d, (κ z₂).boxY a) ∈ t z₁ := by
      rw [L.z₁_outer hz₁]
      have := (ord_range (g := κ z₁) (a := a) (Y := (κ z₂).boxY a)).2 ⟨by omega, by omega⟩
      exact hfull _ _ this.1 this.2 (by omega) (by omega)
    exact L.uniq h1 ((L.z₂_spine' hz₂ _).2 ⟨le_rfl, by omega⟩) L.ne.2.2.2
  omega

/-- The pair AC', step (2): a cell `(x, j)` of `T` with `e <= j < 2e` goes below `y_2` in
`Z_1` and above `y_2 + a` in `W_1`. Source: `report-4.md`, Proposition 34 (line 239). -/
theorem AC_step2 (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz₁ : (κ z₁).negX = false)
    (hw₁ : (κ w₁).negX = false) (hz₂ : (κ z₂).negX = false) {x j : ℤ} (h : (x, j) ∈ t i₀)
    (hj : a - d ≤ j) (hj' : j < 2 * (a - d)) :
    place (κ z₁) a x < (κ z₂).boxY a ∧ (κ z₂).boxY a + a ≤ place (κ w₁) a x := by
  have hn := L.nums
  obtain ⟨hu, hy₁, hh, hy₂⟩ := L.AC_step1 hz₁ hw₁ hz₂
  have hz₂b := L.z₂box
  have hw₁b := L.w₁box
  have hb := L.bT h
  have hfull := L.full_below (by omega)
  -- the thick spine of `Z_2`
  have hthick : ∀ Y, (κ z₂).boxY a ≤ Y → Y < (κ z₂).boxY a + a → (j, Y) ∈ t z₂ := by
    intro Y hY hY'
    rw [L.z₂_inner hz₂]
    have := (ord_range (g := κ z₂) (a := a) (Y := Y)).2 ⟨hY, hY'⟩
    exact hfull _ _ this.1 this.2 (by omega) (by omega)
  have c1 : (j, place (κ z₁) a x) ∈ t z₁ := by rwa [L.z₁_outer hz₁, ord_place]
  have c2 : (j, place (κ w₁) a x) ∈ t w₁ := by rwa [L.w₁_outer hw₁, ord_place]
  have b1 := L.bz₁ c1
  have b2 := L.bw₁ c2
  constructor
  · by_contra hcon
    exact L.uniq c1 (hthick _ (by omega) (by omega)) L.ne.2.2.2
  · by_contra hcon
    exact L.uniq c2 (hthick _ (by omega) (by omega)) L.ne.2.1.2.2

/-- The pair AC', step (3): `Z_1` keeps the order and `W_1` reverses it. Source:
`report-4.md`, Proposition 34 (line 240). -/
theorem AC_step3 (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz₁ : (κ z₁).negX = false)
    (hw₁ : (κ w₁).negX = false) (hz₂ : (κ z₂).negX = false) (hw₂ : (κ w₂).negX = true)
    (hk : (κ z₁).negY = false) (hr : (κ w₁).negY = true) : False := by
  have hn := L.nums
  obtain ⟨hu, hy₁, hh, hy₂⟩ := L.AC_step1 hz₁ hw₁ hz₂
  have hz₂b := L.z₂box
  -- the top row of `W_1` is the image of column 0
  have h1 : (a - d, b - 1) ∈ t w₂ := by
    rcases L.top_row (a - d) (by omega) (by omega) with h | h
    · rw [L.w₁_outer hw₁, ord_top _ _ _ L.w₁box.2, hr, ite_eq_left rfl, L.col0_T] at h
      omega
    · exact h
  rw [L.w₂_outer hw₂, ord_top _ _ _ L.w₂box.2,
    show a - 1 - (a - d) = d - 1 by ring] at h1
  split at h1
  · have := (L.col0_T _).1 h1
    omega
  · have h2 := (L.colA_T _).1 h1
    have h3 := (L.AC_step2 hz₁ hw₁ hz₂ ((L.colA_T (a - d)).2 ⟨by omega, by omega⟩) le_rfl
      (by omega)).1
    rw [place_keep hk] at h3
    omega

/-- The pair AC', step (4): `Z_1` reverses the order and `W_1` keeps it. Source:
`report-4.md`, Proposition 34 (lines 241-243). -/
theorem AC_step4 (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz₁ : (κ z₁).negX = false)
    (hw₁ : (κ w₁).negX = false) (hz₂ : (κ z₂).negX = false) (hw₂ : (κ w₂).negX = true)
    (hr : (κ z₁).negY = true) (hk : (κ w₁).negY = false) : False := by
  have hn := L.nums
  obtain ⟨hu, hy₁, hh, hy₂⟩ := L.AC_step1 hz₁ hw₁ hz₂
  have hz₂b := L.z₂box
  have hw₁b := L.w₁box
  have hv := L.u₁_bounds
  have hy₂' := L.y₂_le
  have hfull := L.full_below (by omega)
  have hst : ∀ {x j : ℤ}, (x, j) ∈ t i₀ → a - d ≤ j → j < 2 * (a - d) →
      2 * a - d - 1 - (κ z₂).boxY a < x := by
    intro x j h hj hj'
    have := (L.AC_step2 hz₁ hw₁ hz₂ h hj hj').1
    rw [place_rev hr] at this
    omega
  -- below row `y_2`, from row `a - d` up, there are only `T` and `Z_1`
  have hrow : ∀ x r, 0 ≤ x → x < a → a - d ≤ r → r < (κ z₂).boxY a →
      (x, r) ∈ t i₀ ∨ (x, r) ∈ t z₁ := by
    intro x r hx0 hxa hr0 hr1
    rcases L.tile_at hx0 hxa (by omega : 0 ≤ r) (by omega) with h | h | h | h | h
    · exact Or.inl h
    · have := L.bw₁ h
      omega
    · have := L.bw₂ h
      omega
    · exact Or.inr h
    · have := L.bz₂ h
      omega
  have h2e : 2 * (a - d) ≤ (κ z₂).boxY a := by
    rcases hrow d (a - d) (by omega) (by omega) le_rfl hy₂ with h | h
    · have := hst h le_rfl (by omega)
      omega
    · have := L.bz₁ h
      omega
  -- `Z_1` holds the cells left of the end interval of step (2)
  have hu₁ : 2 * a - d - (κ z₂).boxY a ≤ colCount (t i₀) (a - 1) := by
    have h : (2 * a - d - 1 - (κ z₂).boxY a, a - d) ∈ t z₁ := by
      rcases hrow (2 * a - d - 1 - (κ z₂).boxY a) (a - d) (by omega) (by omega) le_rfl hy₂
        with h | h
      · have := hst h le_rfl (by omega)
        omega
      · exact h
    rw [L.z₁_outer hz₁, ord_rev hr, show (κ z₁).boxY a + a - 1 - (a - d) = a - 1 by omega] at h
    have := (L.colA_T _).1 h
    omega
  -- the top row
  have hW₁ : ∀ X, (X, b - 1) ∈ t w₁ ↔ 0 ≤ X ∧ X < colCount (t i₀) (a - 1) := by
    intro X
    rw [L.w₁_outer hw₁, ord_top _ _ _ L.w₁box.2, hk]
    exact L.colA_T X
  have hX : (colCount (t i₀) (a - 1), b - 1) ∈ t w₂ := by
    rcases L.top_row (colCount (t i₀) (a - 1)) (by omega) (by omega) with h | h
    · have := (hW₁ _).1 h
      omega
    · exact h
  rw [L.w₂_outer hw₂, ord_top _ _ _ L.w₂box.2] at hX
  have hd : colCount (t i₀) (a - 1) = d := by
    split at hX
    · have := (L.col0_T _).1 hX
      omega
    · -- (4a) `2 u_1 >= a` against `y_2 <= u_1`, unless the two top tiles overlap
      rename_i hneg
      have hle := (L.colA_T _).1 hX
      have hdis : (colCount (t i₀) (a - 1) - 1, b - 1) ∉ t w₂ := fun h =>
        L.uniq ((hW₁ _).2 ⟨by omega, by omega⟩) h L.ne.2.1.1
      rw [L.w₂_outer hw₂, ord_top _ _ _ L.w₂box.2, ite_eq_right hneg, L.colA_T] at hdis
      omega
  -- (4b) `u_1 = d`: `Z_2` reverses the order and starts in row `d`
  have htop := (L.top_C' hz₂ hw₂ (a - 1)).1 ((L.colA_T (d - 1)).2 ⟨by omega, by omega⟩)
  have hr₂ : (κ z₂).negY = true := by
    by_contra hk₂
    rw [Bool.not_eq_true] at hk₂
    rw [place_keep hk₂] at htop
    omega
  rw [place_rev hr₂] at htop
  have hyd : (κ z₂).boxY a = d := by omega
  -- row `a - d` of `Z_1` is `[0, d)`
  have c1 : (d - 1, a - d) ∈ t z₁ := by
    rw [L.z₁_outer hz₁, ord_rev hr, show (κ z₁).boxY a + a - 1 - (a - d) = a - 1 by omega,
      L.colA_T]
    omega
  -- `Z_2` holds `(2e, d + e)`, the image of `(d - 1, e)`
  have c2 : (2 * (a - d), a) ∈ t z₂ := by
    rcases L.tile_at (X := 2 * (a - d)) (Y := a) (by omega) (by omega) (by omega) (by omega)
      with h | h | h | h | h
    · have := L.bT h
      omega
    · have := L.bw₁ h
      omega
    · have := L.bw₂ h
      omega
    · exfalso
      rw [L.z₁_outer hz₁, ord_rev hr,
        show (κ z₁).boxY a + a - 1 - a = a - d - 1 by omega] at h
      have hb := L.bT h
      have h' : (a - d - 1, 2 * (a - d)) ∈ t z₁ := by
        rw [L.z₁_outer hz₁]
        have := (ord_range (g := κ z₁) (a := a) (Y := 2 * (a - d))).2 ⟨by omega, by omega⟩
        exact hfull _ _ this.1 this.2 (by omega) (by omega)
      exact L.uniq h h' L.ne.1.2.2.1
    · exact h
  rw [L.z₂_inner hz₂, ord_rev hr₂, show (κ z₂).boxY a + a - 1 - a = d - 1 by omega,
    show 2 * (a - d) - (a - d) = a - d by ring] at c2
  exact L.uniq c2 c1 L.ne.1.2.2.1


/-- The pair AC' is excluded. PROVISIONAL. Source: `report-4.md`, Proposition 34
(lines 237-243), steps (1) to (4b). -/
theorem excl_AC (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz₁ : (κ z₁).negX = false)
    (hw₁ : (κ w₁).negX = false) (hz₂ : (κ z₂).negX = false) (hw₂ : (κ w₂).negX = true) :
    False := by
  have hn := L.nums
  obtain ⟨hu, hy₁, hh, hy₂⟩ := L.AC_step1 hz₁ hw₁ hz₂
  have hz₂b := L.z₂box
  have hw₁b := L.w₁box
  obtain ⟨x, hx⟩ := L.h1.frame.exists_in_row (y := a - d) (by omega) (by omega)
  have h := L.AC_step2 hz₁ hw₁ hz₂ hx le_rfl (by omega)
  cases hk₁ : (κ z₁).negY <;> cases hk₂ : (κ w₁).negY
  · rw [place_keep hk₁, place_keep hk₂] at h
    omega
  · exact L.AC_step3 hz₁ hw₁ hz₂ hw₂ hk₁ hk₂
  · exact L.AC_step4 hz₁ hw₁ hz₂ hw₂ hk₁ hk₂
  · rw [place_rev hk₁, place_rev hk₂] at h
    omega

/-- The pair BC' is excluded. PROVISIONAL. Source: `report-4.md`, Proposition 34
(line 228). -/
theorem excl_BC (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) (hz₁ : (κ z₁).negX = false)
    (hw₁ : (κ w₁).negX = true) (hz₂ : (κ z₂).negX = false) (hw₂ : (κ w₂).negX = true) :
    False := by
  have hn := L.nums
  have h1 := L.lemma32d_B hz₁ hw₁
  have h2 := L.count_C' hz₂ hw₂
  obtain ⟨ha, hfull⟩ := L.full_end hw₁
  have hu := L.u₀_bounds
  have hv := L.u₁_bounds
  have c0 := (L.col0_T (d - 1)).2 ⟨by omega, by omega⟩
  have c1 := (L.colA_T (d - 1)).2 ⟨by omega, by omega⟩
  rcases h1.2.2 with h | h
  · have := (h _).1 c1
    omega
  · have := (h _).1 c0
    omega

/-- No layout exists. Source: `report-4.md`, Proposition 34 (line 220), first
sentence: "The layout of Proposition 31 does not occur". Proof idea: the four
switches `negX` of `Z_1`, `W_1`, `Z_2`, `W_2` give 16 cases; each is one of the
seven exclusions above or the mirror image of one (`Layout31.mirror`). -/
theorem absurd (L : Layout31 a b d t i₀ κ w₁ w₂ z₁ z₂) : False := by
  have M := L.mirror
  cases h₁ : (κ z₁).negX <;> cases h₂ : (κ w₁).negX <;> cases h₃ : (κ z₂).negX <;>
    cases h₄ : (κ w₂).negX
  -- the left case is A
  · exact M.excl_D (mirror_negX L.vz₂ h₃) (mirror_negX L.vw₂ h₄)
  · exact L.excl_AC h₁ h₂ h₃ h₄
  · exact L.excl_AB h₁ h₂ h₃ h₄
  · exact L.excl_AA h₁ h₂ h₃ h₄
  -- B
  · exact M.excl_D (mirror_negX L.vz₂ h₃) (mirror_negX L.vw₂ h₄)
  · exact L.excl_BC h₁ h₂ h₃ h₄
  · exact L.excl_BB h₁ h₂ h₃ h₄
  · exact M.excl_AB (mirror_negX L.vz₂ h₃) (mirror_negX L.vw₂ h₄) (mirror_negX L.vz₁ h₁)
      (mirror_negX L.vw₁ h₂)
  -- C
  · exact M.excl_D (mirror_negX L.vz₂ h₃) (mirror_negX L.vw₂ h₄)
  · exact L.excl_CC h₁ h₂ h₃ h₄
  · exact M.excl_BC (mirror_negX L.vz₂ h₃) (mirror_negX L.vw₂ h₄) (mirror_negX L.vz₁ h₁)
      (mirror_negX L.vw₁ h₂)
  · exact M.excl_AC (mirror_negX L.vz₂ h₃) (mirror_negX L.vw₂ h₄) (mirror_negX L.vz₁ h₁)
      (mirror_negX L.vw₁ h₂)
  -- D
  · exact L.excl_D h₁ h₂
  · exact L.excl_D h₁ h₂
  · exact L.excl_D h₁ h₂
  · exact L.excl_D h₁ h₂

end Layout31

/-- Proposition 34. Source: `report-4.md`, section 5b, Proposition 34 (line 220):
"in case (II.2) with k = 5 and two top tiles, b - a <= d". (For `b - a > d` there
are two top tiles by Corollary 26.) -/
theorem proposition34 {a b d : ℤ} {t : Fin 5 → Finset Cell} {i₀ : Fin 5}
    {κ : Fin 5 → GridIso} (H : TypeH1 a b d t i₀ κ) : b - a ≤ d := by
  by_contra hlong
  obtain ⟨_, w₁, w₂, z₁, z₂, L⟩ := proposition31 H (by omega)
  exact L.absurd

/-- Corollary 35. Source: `report-4.md`, Corollary 35 (line 247): "In case (II.2)
of Theorem 6 (k = 5): 2 <= d < a and a + 2 <= b <= a + d." -/
theorem corollary35 {a b d : ℤ} {t : Fin 5 → Finset Cell} {i₀ : Fin 5}
    {κ : Fin 5 → GridIso} (H : TypeH1 a b d t i₀ κ) :
    2 ≤ d ∧ d < a ∧ a + 2 ≤ b ∧ b ≤ a + d := by
  have h23 := H.corollary23 (by norm_num) (by decide)
  have h34 := proposition34 H
  omega

end PolyominoOddOrder
