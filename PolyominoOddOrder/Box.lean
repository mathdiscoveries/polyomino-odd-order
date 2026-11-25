module

public import PolyominoOddOrder.Iso

/-!
# Foundation 3: bounding boxes and their dimensions (`Box.lean`)

Blueprint unit F. Spans, the bounding box, its two dimensions
`width` and `height`, how an isometry acts on them, and the two remarks of
`report.md` section 1 that the reports use "without further mention":

> (Boxes.) box(g(P)) = g(box(P)) for an isometry g. So all tiles have boxes with the
> same pair of dimensions, up to order.

> (Thin rectangles.) A connected subset of a rectangle with a = 1 or b = 1 is
> rectangular. So if P is not rectangular then a >= 2 and b >= 2.

Commit `e5ca51d`.
-/

@[expose] public section

namespace PolyominoOddOrder

/-! ## Spans and the box -/

theorem mem_xSpan {S : Finset Cell} {x : ℤ} :
    x ∈ xSpan S ↔ ∃ c ∈ S, ∃ d ∈ S, c.1 ≤ x ∧ x ≤ d.1 := by
  simp [xSpan, Finset.mem_biUnion, Finset.mem_Icc]

theorem mem_ySpan {S : Finset Cell} {y : ℤ} :
    y ∈ ySpan S ↔ ∃ c ∈ S, ∃ d ∈ S, c.2 ≤ y ∧ y ≤ d.2 := by
  simp [ySpan, Finset.mem_biUnion, Finset.mem_Icc]

theorem mem_boundingBox {S : Finset Cell} {c : Cell} :
    c ∈ boundingBox S ↔ c.1 ∈ xSpan S ∧ c.2 ∈ ySpan S := by
  simp [boundingBox, Finset.mem_product]

/-- A set lies in its box. -/
theorem subset_boundingBox (S : Finset Cell) : S ⊆ boundingBox S := by
  intro c hc
  rw [mem_boundingBox, mem_xSpan, mem_ySpan]
  exact ⟨⟨c, hc, c, hc, le_rfl, le_rfl⟩, ⟨c, hc, c, hc, le_rfl, le_rfl⟩⟩

/-- A set that is not rectangular misses a cell of its box. -/
theorem exists_hole_of_not_isRectangular {S : Finset Cell} (h : ¬ IsRectangular S) :
    ∃ c ∈ boundingBox S, c ∉ S := by
  by_contra hno
  push Not at hno
  exact h (Finset.Subset.antisymm (subset_boundingBox S) hno)

/-- The horizontal extent of `box(S)`: the number of its columns. -/
def width (S : Finset Cell) : ℤ := ((xSpan S).card : ℤ)

/-- The vertical extent of `box(S)`: the number of its rows. -/
def height (S : Finset Cell) : ℤ := ((ySpan S).card : ℤ)

/-- For non-empty `S` the columns of the box are an interval whose two end columns
hold cells of `S` ("a box is the smallest rectangle containing the tile",
`report.md`, proof of Lemma 4 (a)). -/
theorem xSpan_eq_Icc {S : Finset Cell} (hS : S.Nonempty) :
    ∃ lo hi : ℤ, lo ≤ hi ∧ xSpan S = Finset.Icc lo hi ∧ (∃ y, (lo, y) ∈ S) ∧
      ∃ y, (hi, y) ∈ S := by
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image S (fun c => c.1) hS
  obtain ⟨q, hq, hmax⟩ := Finset.exists_max_image S (fun c => c.1) hS
  refine ⟨p.1, q.1, hmin q hq, ?_, ⟨p.2, hp⟩, ⟨q.2, hq⟩⟩
  ext v
  rw [mem_xSpan, Finset.mem_Icc]
  constructor
  · rintro ⟨c, hc, d, hd, h1, h2⟩
    exact ⟨le_trans (hmin c hc) h1, le_trans h2 (hmax d hd)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨p, hp, q, hq, h1, h2⟩

/-- For non-empty `S` the rows of the box are an interval whose two end rows hold
cells of `S`. -/
theorem ySpan_eq_Icc {S : Finset Cell} (hS : S.Nonempty) :
    ∃ lo hi : ℤ, lo ≤ hi ∧ ySpan S = Finset.Icc lo hi ∧ (∃ x, (x, lo) ∈ S) ∧
      ∃ x, (x, hi) ∈ S := by
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image S (fun c => c.2) hS
  obtain ⟨q, hq, hmax⟩ := Finset.exists_max_image S (fun c => c.2) hS
  refine ⟨p.2, q.2, hmin q hq, ?_, ⟨p.1, hp⟩, ⟨q.1, hq⟩⟩
  ext v
  rw [mem_ySpan, Finset.mem_Icc]
  constructor
  · rintro ⟨c, hc, d, hd, h1, h2⟩
    exact ⟨le_trans (hmin c hc) h1, le_trans h2 (hmax d hd)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨p, hp, q, hq, h1, h2⟩

/-- The spans are monotone. -/
theorem xSpan_mono {S T : Finset Cell} (h : S ⊆ T) : xSpan S ⊆ xSpan T := by
  intro x hx
  rw [mem_xSpan] at hx ⊢
  obtain ⟨c, hc, d, hd, h1, h2⟩ := hx
  exact ⟨c, h hc, d, h hd, h1, h2⟩

theorem ySpan_mono {S T : Finset Cell} (h : S ⊆ T) : ySpan S ⊆ ySpan T := by
  intro y hy
  rw [mem_ySpan] at hy ⊢
  obtain ⟨c, hc, d, hd, h1, h2⟩ := hy
  exact ⟨c, h hc, d, h hd, h1, h2⟩

/-- A set inside `R a b` has its columns inside `[0, a)`. -/
theorem xSpan_subset_of_subset_R {S : Finset Cell} {a b : ℤ} (h : S ⊆ R a b) :
    xSpan S ⊆ Finset.Ico 0 a := by
  intro x hx
  rw [mem_xSpan] at hx
  obtain ⟨c, hc, d, hd, h1, h2⟩ := hx
  have hc' := mem_R.1 (h hc)
  have hd' := mem_R.1 (h hd)
  rw [Finset.mem_Ico]
  omega

/-- A set inside `R a b` has its rows inside `[0, b)`. -/
theorem ySpan_subset_of_subset_R {S : Finset Cell} {a b : ℤ} (h : S ⊆ R a b) :
    ySpan S ⊆ Finset.Ico 0 b := by
  intro y hy
  rw [mem_ySpan] at hy
  obtain ⟨c, hc, d, hd, h1, h2⟩ := hy
  have hc' := mem_R.1 (h hc)
  have hd' := mem_R.1 (h hd)
  rw [Finset.mem_Ico]
  omega

/-- The box of a set inside `R a b` lies in `R a b` ("box(T) lying inside R",
`report.md`, proof of Lemma 2). -/
theorem boundingBox_subset_R {S : Finset Cell} {a b : ℤ} (h : S ⊆ R a b) :
    boundingBox S ⊆ R a b := by
  intro c hc
  rw [mem_boundingBox] at hc
  have h1 := Finset.mem_Ico.1 (xSpan_subset_of_subset_R h hc.1)
  have h2 := Finset.mem_Ico.1 (ySpan_subset_of_subset_R h hc.2)
  exact mem_R.2 ⟨h1, h2⟩

/-- A set inside `R a b` is at most `a` wide and `b` high. -/
theorem width_le_of_subset_R {S : Finset Cell} {a b : ℤ} (h : S ⊆ R a b) (ha : 0 ≤ a) :
    width S ≤ a := by
  have hc := Finset.card_le_card (xSpan_subset_of_subset_R h)
  rw [Int.card_Ico] at hc
  unfold width
  omega

/-- A set inside `R a b` is at most `b` high. -/
theorem height_le_of_subset_R {S : Finset Cell} {a b : ℤ} (h : S ⊆ R a b) (hb : 0 ≤ b) :
    height S ≤ b := by
  have hc := Finset.card_le_card (ySpan_subset_of_subset_R h)
  rw [Int.card_Ico] at hc
  unfold height
  omega

/-- A set inside `R a b` that is `a` wide has cells in column `0` and in column
`a - 1` ("hence equal to R", `report.md`, proof of Lemma 2). -/
theorem xSpan_eq_of_width_eq {S : Finset Cell} {a b : ℤ} (h : S ⊆ R a b) (ha : 0 < a)
    (hw : width S = a) : xSpan S = Finset.Ico 0 a := by
  refine Finset.eq_of_subset_of_card_le (xSpan_subset_of_subset_R h) ?_
  rw [Int.card_Ico]
  unfold width at hw
  omega

/-- A set inside `R a b` that is `b` high has cells in row `0` and in row `b - 1`. -/
theorem ySpan_eq_of_height_eq {S : Finset Cell} {a b : ℤ} (h : S ⊆ R a b) (hb : 0 < b)
    (hw : height S = b) : ySpan S = Finset.Ico 0 b := by
  refine Finset.eq_of_subset_of_card_le (ySpan_subset_of_subset_R h) ?_
  rw [Int.card_Ico]
  unfold height at hw
  omega

/-- A non-empty rectangular set has `width * height` cells; a non-empty set with
that many cells is rectangular. Used for "T is its box, a rectangle". -/
theorem isRectangular_iff_card {S : Finset Cell} (hS : S.Nonempty) :
    IsRectangular S ↔ (S.card : ℤ) = width S * height S := by
  have _ := hS -- not needed: for empty `S` both sides are true
  have hbox : ((boundingBox S).card : ℤ) = width S * height S := by
    simp [boundingBox, width, height, Finset.card_product]
  constructor
  · intro h
    rw [← hbox, ← show S = boundingBox S from h]
  · intro h
    refine Finset.eq_of_subset_of_card_le (subset_boundingBox S) ?_
    rw [← hbox] at h
    exact_mod_cast h.ge

/-! ## Isometries and boxes (the remark "Boxes") -/

/-- The columns of the image: the columns of `S` moved if `g` keeps the axis
directions, the rows of `S` moved if `g` exchanges them. -/
theorem xSpan_image (g : GridIso) (S : Finset Cell) :
    xSpan (S.image g.apply) =
      (if g.swap then ySpan S else xSpan S).image
        fun v => (if g.negX then -v else v) + g.shift.1 := by
  obtain ⟨gs, gx, gy, u, w⟩ := g
  ext x
  cases gs <;> cases gx <;>
    simp only [mem_xSpan, mem_ySpan, Finset.mem_image, GridIso.apply, Bool.false_eq_true,
      ite_true, ite_false] <;>
    constructor
  all_goals
    first
      | (rintro ⟨_, ⟨c, hc, rfl⟩, _, ⟨d, hd, rfl⟩, h1, h2⟩
         dsimp only at h1 h2
         first
           | exact ⟨x - u, ⟨c, hc, d, hd, by omega, by omega⟩, by omega⟩
           | exact ⟨-(x - u), ⟨d, hd, c, hc, by omega, by omega⟩, by omega⟩)
      | (rintro ⟨v, ⟨c, hc, d, hd, h1, h2⟩, rfl⟩
         first
           | exact ⟨_, ⟨c, hc, rfl⟩, _, ⟨d, hd, rfl⟩, by dsimp only; omega, by dsimp only; omega⟩
           | exact ⟨_, ⟨d, hd, rfl⟩, _, ⟨c, hc, rfl⟩, by dsimp only; omega, by dsimp only; omega⟩)

/-- The rows of the image. -/
theorem ySpan_image (g : GridIso) (S : Finset Cell) :
    ySpan (S.image g.apply) =
      (if g.swap then xSpan S else ySpan S).image
        fun v => (if g.negY then -v else v) + g.shift.2 := by
  obtain ⟨gs, gx, gy, u, w⟩ := g
  ext x
  cases gs <;> cases gy <;>
    simp only [mem_xSpan, mem_ySpan, Finset.mem_image, GridIso.apply, Bool.false_eq_true,
      ite_true, ite_false] <;>
    constructor
  all_goals
    first
      | (rintro ⟨_, ⟨c, hc, rfl⟩, _, ⟨d, hd, rfl⟩, h1, h2⟩
         dsimp only at h1 h2
         first
           | exact ⟨x - w, ⟨c, hc, d, hd, by omega, by omega⟩, by omega⟩
           | exact ⟨-(x - w), ⟨d, hd, c, hc, by omega, by omega⟩, by omega⟩)
      | (rintro ⟨v, ⟨c, hc, d, hd, h1, h2⟩, rfl⟩
         first
           | exact ⟨_, ⟨c, hc, rfl⟩, _, ⟨d, hd, rfl⟩, by dsimp only; omega, by dsimp only; omega⟩
           | exact ⟨_, ⟨d, hd, rfl⟩, _, ⟨c, hc, rfl⟩, by dsimp only; omega, by dsimp only; omega⟩)

/-- The map `v -> ±v + s` of one coordinate under an isometry is injective. -/
theorem signed_injective (n : Bool) (s : ℤ) :
    Function.Injective fun v : ℤ => (if n then -v else v) + s := by
  intro v w h
  cases n <;> simp at h <;> omega

/-- Membership in the image of a set of integers under `v -> ±v + s`. -/
theorem mem_image_signed {A : Finset ℤ} {n : Bool} {s x : ℤ} :
    x ∈ A.image (fun v => (if n then -v else v) + s) ↔ (if n then s - x else x - s) ∈ A := by
  have h : (fun v : ℤ => (if n then -v else v) + s) (if n then s - x else x - s) = x := by
    cases n <;> simp
  constructor
  · intro hx
    obtain ⟨v, hv, hvx⟩ := Finset.mem_image.1 hx
    rwa [← signed_injective n s (hvx.trans h.symm)]
  · intro hx
    exact Finset.mem_image.2 ⟨_, hx, h⟩

/-- `box(g(S)) = g(box(S))` (`report.md` section 1, remark "Boxes"). -/
theorem boundingBox_image (g : GridIso) (S : Finset Cell) :
    boundingBox (S.image g.apply) = (boundingBox S).image g.apply := by
  ext c
  rw [GridIso.mem_image_iff, mem_boundingBox, mem_boundingBox, xSpan_image, ySpan_image,
    mem_image_signed, mem_image_signed]
  obtain ⟨gs, gx, gy, u, w⟩ := g
  cases gs <;> cases gx <;> cases gy <;>
    simp [GridIso.inv, GridIso.apply, sub_eq_add_neg, add_comm, and_comm]

/-- The width of the image: the width of `S` if `g` keeps the axis directions, its
height if `g` exchanges them. -/
theorem width_image (g : GridIso) (S : Finset Cell) :
    width (S.image g.apply) = if g.swap then height S else width S := by
  unfold width height
  rw [xSpan_image, Finset.card_image_of_injective _ (signed_injective _ _)]
  cases g.swap <;> rfl

/-- The height of the image. -/
theorem height_image (g : GridIso) (S : Finset Cell) :
    height (S.image g.apply) = if g.swap then width S else height S := by
  unfold width height
  rw [ySpan_image, Finset.card_image_of_injective _ (signed_injective _ _)]
  cases g.swap <;> rfl

/-- An isometry preserves being rectangular. -/
theorem isRectangular_image_iff (g : GridIso) (S : Finset Cell) :
    IsRectangular (S.image g.apply) ↔ IsRectangular S := by
  unfold IsRectangular
  rw [boundingBox_image]
  exact (Finset.image_injective g.apply_injective).eq_iff

/-- Congruent sets have boxes with the same pair of dimensions, up to order
(`report.md` section 1, remark "Boxes"). -/
theorem Congruent.dims {S T : Finset Cell} (h : Congruent S T) :
    (width T = width S ∧ height T = height S) ∨
      (width T = height S ∧ height T = width S) := by
  obtain ⟨g, rfl⟩ := h
  rw [width_image, height_image]
  cases g.swap <;> simp

/-- A set smaller than `T` in both box dimensions is not congruent to `T`
(`report-4.md`, Lemma 56: "A congruent copy has the same two box sides"). -/
theorem not_congruent_of_smaller {S T : Finset Cell} (hw : width S < width T)
    (hh : height S < height T) : ¬ Congruent T S := by
  intro h
  rcases h.dims with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem Congruent.isRectangular_iff {S T : Finset Cell} (h : Congruent S T) :
    IsRectangular T ↔ IsRectangular S := by
  obtain ⟨g, rfl⟩ := h
  exact isRectangular_image_iff g S

/-! ## Thin rectangles -/

/-- A connected subset of a rectangle with `a = 1` or `b = 1` is rectangular
(`report.md` section 1, remark "Thin rectangles"). -/
theorem EdgeConnected.isRectangular_of_thin {S : Finset Cell} (hS : EdgeConnected S)
    {a b : ℤ} (hSR : S ⊆ R a b) (h : a = 1 ∨ b = 1) : IsRectangular S := by
  refine Finset.Subset.antisymm (subset_boundingBox S) fun c hc => ?_
  have hcR := mem_R.1 (boundingBox_subset_R hSR hc)
  rw [mem_boundingBox, mem_xSpan, mem_ySpan] at hc
  obtain ⟨⟨p, hp, q, hq, h1, h2⟩, p', hp', q', hq', h3, h4⟩ := hc
  rcases h with rfl | rfl
  · obtain ⟨x, hx⟩ := hS.exists_in_row hp' hq' h3 h4
    have hxR := mem_R.1 (hSR hx)
    have : c = (x, c.2) := Prod.ext (by dsimp only at hxR ⊢; omega) rfl
    rwa [this]
  · obtain ⟨y, hy⟩ := hS.exists_in_col hp hq h1 h2
    have hyR := mem_R.1 (hSR hy)
    have : c = (c.1, y) := Prod.ext rfl (by dsimp only at hyR ⊢; omega)
    rwa [this]

end PolyominoOddOrder
