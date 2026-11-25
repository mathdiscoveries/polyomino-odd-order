module

public import PolyominoOddOrder.CaseI
public import PolyominoOddOrder.ThreeCopy

/-!
# Case (I): the fifth tile does not meet two opposite sides (`CaseIOpposite.lean`)

Blueprint unit I2. `report-4.md`, section 7: Proposition 57 (d), Proposition 58
(the fifth tile across the rectangle), Proposition 60, and with Corollary 59 the
internal form `free_tile_one_side` of the frozen statement (g).

The binding statement of this file is `free_tile_one_side`. Every node of the file
is proved; it uses `sides_are_intervals`, `corner_tile_sides`,
`free_tile_not_adjacent` and `CornersInDistinctTiles.transpose` (`CaseI.lean`) and
`three_copy` (`ThreeCopy.lean`).

Where the proofs leave the report's route:

* 58 (a) is `crossing` for the free tile and the tile extended by the part of the
  column above (below) the cell.
* Proposition 60 is not reduced to `{BL}`, `{BL, TL}`, `{BL, TR}` by symmetry: the
  interval equations (*) are stated for all four corners (`PatternD.side_BL` to
  `PatternD.side_TL`) and `CaseIOpposite.corner_cells_absurd` treats every choice of
  the `K_i` at once.
* The case `{BL, TL}` needs only that `a = 2q` is impossible
  (`PatternD.two_mul_height_ne`), so no column counts `u[j]` are used; 58 (e) supplies
  the cells in row `y_5`.

Names local to this file are in the namespaces `CaseIOpposite` and `PatternD`.

Commit `e5ca51d`.
-/

@[expose] public section

namespace PolyominoOddOrder

namespace CaseIOpposite

/-! ## Extreme rows and columns -/

/-- The column of a cell is a column of the box. -/
theorem mem_xSpan_of_mem {S : Finset Cell} {c : Cell} (h : c ∈ S) : c.1 ∈ xSpan S :=
  mem_xSpan.2 ⟨c, h, c, h, le_rfl, le_rfl⟩

/-- The row of a cell is a row of the box. -/
theorem mem_ySpan_of_mem {S : Finset Cell} {c : Cell} (h : c ∈ S) : c.2 ∈ ySpan S :=
  mem_ySpan.2 ⟨c, h, c, h, le_rfl, le_rfl⟩

/-- A connected set has a cell in every column of its box. -/
theorem exists_of_mem_xSpan {S : Finset Cell} (hS : EdgeConnected S) {x : ℤ}
    (h : x ∈ xSpan S) : ∃ y : ℤ, (x, y) ∈ S := by
  obtain ⟨c, hc, d, hd, h1, h2⟩ := mem_xSpan.1 h
  exact hS.exists_in_col hc hd h1 h2

/-- A connected set has a cell in every row of its box. -/
theorem exists_of_mem_ySpan {S : Finset Cell} (hS : EdgeConnected S) {y : ℤ}
    (h : y ∈ ySpan S) : ∃ x : ℤ, (x, y) ∈ S := by
  obtain ⟨c, hc, d, hd, h1, h2⟩ := mem_ySpan.1 h
  exact hS.exists_in_row hc hd h1 h2

/-- The columns of a set with a cell in column `0` of `R a b`. -/
theorem xSpan_of_left {S : Finset Cell} {a b y : ℤ} (hSR : S ⊆ R a b) (h : (0, y) ∈ S) :
    xSpan S = Finset.Ico 0 (width S) := by
  obtain ⟨lo, hi, hle, hspan, ⟨y₁, h1⟩, -⟩ := xSpan_eq_Icc ⟨_, h⟩
  have h0 := mem_xSpan_of_mem h
  have hR := mem_R.1 (hSR h1)
  rw [hspan, Finset.mem_Icc] at h0
  simp only at h0 hR
  have hw : width S = hi + 1 - lo := by
    unfold width
    rw [hspan, Int.card_Icc]
    omega
  rw [hspan, hw]
  ext x
  rw [Finset.mem_Icc, Finset.mem_Ico]
  omega

/-- The columns of a set with a cell in column `a - 1` of `R a b`. -/
theorem xSpan_of_right {S : Finset Cell} {a b y : ℤ} (hSR : S ⊆ R a b) (h : (a - 1, y) ∈ S) :
    xSpan S = Finset.Ico (a - width S) a := by
  obtain ⟨lo, hi, hle, hspan, -, ⟨y₁, h1⟩⟩ := xSpan_eq_Icc ⟨_, h⟩
  have h0 := mem_xSpan_of_mem h
  have hR := mem_R.1 (hSR h1)
  rw [hspan, Finset.mem_Icc] at h0
  simp only at h0 hR
  have hw : width S = hi + 1 - lo := by
    unfold width
    rw [hspan, Int.card_Icc]
    omega
  rw [hspan, hw]
  ext x
  rw [Finset.mem_Icc, Finset.mem_Ico]
  omega

/-- The rows of a set with a cell in row `0` of `R a b`. -/
theorem ySpan_of_bottom {S : Finset Cell} {a b x : ℤ} (hSR : S ⊆ R a b) (h : (x, 0) ∈ S) :
    ySpan S = Finset.Ico 0 (height S) := by
  obtain ⟨lo, hi, hle, hspan, ⟨x₁, h1⟩, -⟩ := ySpan_eq_Icc ⟨_, h⟩
  have h0 := mem_ySpan_of_mem h
  have hR := mem_R.1 (hSR h1)
  rw [hspan, Finset.mem_Icc] at h0
  simp only at h0 hR
  have hw : height S = hi + 1 - lo := by
    unfold height
    rw [hspan, Int.card_Icc]
    omega
  rw [hspan, hw]
  ext y
  rw [Finset.mem_Icc, Finset.mem_Ico]
  omega

/-- The rows of a set with a cell in row `b - 1` of `R a b`. -/
theorem ySpan_of_top {S : Finset Cell} {a b x : ℤ} (hSR : S ⊆ R a b) (h : (x, b - 1) ∈ S) :
    ySpan S = Finset.Ico (b - height S) b := by
  obtain ⟨lo, hi, hle, hspan, -, ⟨x₁, h1⟩⟩ := ySpan_eq_Icc ⟨_, h⟩
  have h0 := mem_ySpan_of_mem h
  have hR := mem_R.1 (hSR h1)
  rw [hspan, Finset.mem_Icc] at h0
  simp only at h0 hR
  have hw : height S = hi + 1 - lo := by
    unfold height
    rw [hspan, Int.card_Icc]
    omega
  rw [hspan, hw]
  ext y
  rw [Finset.mem_Icc, Finset.mem_Ico]
  omega

/-- An isometry that exchanges the axis directions, read from a cell `K`: the two
coordinates of the image move with the row and with the column, each with one sign. -/
theorem swap_apply (g : GridIso) (hs : g.swap = true) (K : Cell) :
    ((∀ c, (g.apply c).1 - (g.apply K).1 = c.2 - K.2) ∨
        ∀ c, (g.apply c).1 - (g.apply K).1 = K.2 - c.2) ∧
      ((∀ c, (g.apply c).2 - (g.apply K).2 = c.1 - K.1) ∨
        ∀ c, (g.apply c).2 - (g.apply K).2 = K.1 - c.1) := by
  obtain ⟨gs, gx, gy, ⟨u, v⟩⟩ := g
  simp only at hs
  subst hs
  constructor
  · cases gx
    · exact Or.inl fun c => by simp [GridIso.apply]
    · refine Or.inr fun c => ?_
      simp only [GridIso.apply, ite_true]
      omega
  · cases gy
    · exact Or.inl fun c => by simp [GridIso.apply]
    · refine Or.inr fun c => ?_
      simp only [GridIso.apply, ite_true]
      omega

/-- A column that holds the cells of rows `[u, v)` has at least `v - u` cells. -/
theorem le_colCount {S : Finset Cell} {x u v : ℤ}
    (h : ∀ y, u ≤ y → y < v → (x, y) ∈ S) : v - u ≤ colCount S x := by
  have hsub : ({x} : Finset ℤ) ×ˢ Finset.Ico u v ⊆ S.filter fun c : Cell => c.1 = x := by
    rintro ⟨x', y⟩ hc
    simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico] at hc
    obtain ⟨rfl, hy1, hy2⟩ := hc
    exact Finset.mem_filter.2 ⟨h y hy1 hy2, rfl⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_singleton, one_mul, Int.card_Ico] at hcard
  have hdef : colCount S x = ((S.filter fun c : Cell => c.1 = x).card : ℤ) := rfl
  rw [hdef]
  omega

/-- A column whose cells lie in the rows `[u, v)` has at most `v - u` cells. -/
theorem colCount_le {S : Finset Cell} {x u v : ℤ} (huv : u ≤ v)
    (h : ∀ y, (x, y) ∈ S → u ≤ y ∧ y < v) : colCount S x ≤ v - u := by
  have hsub : (S.filter fun c : Cell => c.1 = x) ⊆ ({x} : Finset ℤ) ×ˢ Finset.Ico u v := by
    rintro ⟨x', y⟩ hc
    have hc' := Finset.mem_filter.1 hc
    obtain rfl : x' = x := hc'.2
    simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico, true_and]
    exact h y hc'.1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_singleton, one_mul, Int.card_Ico] at hcard
  have hdef : colCount S x = ((S.filter fun c : Cell => c.1 = x).card : ℤ) := rfl
  rw [hdef]
  omega

/-- A column interval that starts at the bottom and holds the rows `[0, n)`: it has
at least `n` cells, and exactly `n` when row `n` is not in it. -/
theorem col_count_low {S : Finset Cell} {x n : ℤ} (hn : 0 < n)
    (hlow : ∀ y, 0 ≤ y → y < n → (x, y) ∈ S) (hS : ∀ y, (x, y) ∈ S → 0 ≤ y)
    (hint : ColInterval S x) :
    n ≤ colCount S x ∧ (colCount S x = n ↔ (x, n) ∉ S) := by
  have h1 := le_colCount (x := x) (u := 0) (v := n) hlow
  refine ⟨by omega, fun hc hmem => ?_, fun hmem => ?_⟩
  · have h2 := le_colCount (S := S) (x := x) (u := 0) (v := n + 1) fun y hy0 hy1 => by
      rcases lt_or_eq_of_le (Int.lt_add_one_iff.1 hy1) with h | h
      · exact hlow y hy0 h
      · exact h ▸ hmem
    omega
  · have h2 := colCount_le (S := S) (x := x) (u := 0) (v := n) hn.le fun y hy => by
      refine ⟨hS y hy, ?_⟩
      by_contra hcon
      exact hmem (hint 0 n y hn.le (by omega) (hlow 0 le_rfl hn) hy)
    omega

/-- A column interval that ends at row `b - 1` and holds the rows `[n, b)`: it has at
least `b - n` cells, and exactly `b - n` when row `n - 1` is not in it. -/
theorem col_count_high {S : Finset Cell} {x n b : ℤ} (hn : n < b)
    (hhigh : ∀ y, n ≤ y → y < b → (x, y) ∈ S) (hS : ∀ y, (x, y) ∈ S → y < b)
    (hint : ColInterval S x) :
    b - n ≤ colCount S x ∧ (colCount S x = b - n ↔ (x, n - 1) ∉ S) := by
  have h1 := le_colCount (x := x) (u := n) (v := b) hhigh
  refine ⟨by omega, fun hc hmem => ?_, fun hmem => ?_⟩
  · have h2 := le_colCount (S := S) (x := x) (u := n - 1) (v := b) fun y hy0 hy1 => by
      rcases eq_or_lt_of_le hy0 with h | h
      · exact h ▸ hmem
      · exact hhigh y (by omega) hy1
    omega
  · have h2 := colCount_le (S := S) (x := x) (u := n) (v := b) hn.le fun y hy => by
      refine ⟨?_, hS y hy⟩
      by_contra hcon
      exact hmem (hint y (n - 1) (b - 1) (by omega) (by omega) hy
        (hhigh (b - 1) (by omega) (by omega)))
    omega

/-! ## Proposition 60, the choice of the corner cells -/

/-- Proposition 60, the choice of the corner cells, free of geometry. `S` is the free
tile, `y₅` and `y₆` are the two end rows of its box, `m` is the number of rows above
the box, and `K₁`, `K₂`, `K₃`, `K₄` are the corner cells of the box that the four
corner tiles put on the corners of `R`. The hypotheses: `n₁` to `n₄` are "No two of
the K_i are the two ends of one long row" (58 (d)); `l` and `s` are the equations
(*); `hturn` is the half turn; `hsame` is the case `{BL, TL}`. Source: `report-4.md`,
Proposition 60 (lines 555-565), all choices of the corners in use at once. -/
theorem corner_cells_absurd {S : Finset Cell} {a y₅ y₆ m : ℤ} {K₁ K₂ K₃ K₄ : Cell}
    (m₁ : K₁ ∈ S) (m₂ : K₂ ∈ S) (m₃ : K₃ ∈ S) (m₄ : K₄ ∈ S)
    (x₁ : K₁.1 = 0 ∨ K₁.1 = a - 1) (x₂ : K₂.1 = 0 ∨ K₂.1 = a - 1)
    (x₃ : K₃.1 = 0 ∨ K₃.1 = a - 1) (x₄ : K₄.1 = 0 ∨ K₄.1 = a - 1)
    (r₁ : K₁.2 = y₅ ∨ K₁.2 = y₆) (r₂ : K₂.2 = y₅ ∨ K₂.2 = y₆)
    (r₃ : K₃.2 = y₅ ∨ K₃.2 = y₆) (r₄ : K₄.2 = y₅ ∨ K₄.2 = y₆)
    (n₁ : (0, K₁.2) ∈ S → (a - 1, K₁.2) ∈ S → False)
    (n₂ : (0, K₂.2) ∈ S → (a - 1, K₂.2) ∈ S → False)
    (n₃ : (0, K₃.2) ∈ S → (a - 1, K₃.2) ∈ S → False)
    (n₄ : (0, K₄.2) ∈ S → (a - 1, K₄.2) ∈ S → False)
    (l₁ : y₅ ≤ rowCount S K₁.2) (l₂ : y₅ ≤ rowCount S K₂.2)
    (l₃ : m ≤ rowCount S K₃.2) (l₄ : m ≤ rowCount S K₄.2)
    (s₁ : rowCount S K₁.2 = y₅ ↔ (0, y₅) ∈ S) (s₂ : rowCount S K₂.2 = y₅ ↔ (a - 1, y₅) ∈ S)
    (s₃ : rowCount S K₃.2 = m ↔ (a - 1, y₆) ∈ S) (s₄ : rowCount S K₄.2 = m ↔ (0, y₆) ∈ S)
    (hturn : K₁ = K₃ → K₂ = K₄ → rowCount S y₅ = rowCount S y₆)
    (hsame : ∀ x : ℤ, K₁.1 = x → K₂.1 = x → (x, y₅) ∈ S → (x, y₆) ∈ S → False) : False := by
  -- a corner cell of the box in the free tile, by its side
  have hend : ∀ {K : Cell} {y : ℤ}, K ∈ S → (K.1 = 0 ∨ K.1 = a - 1) → K.2 = y →
      (K.1 = 0 ∧ (0, y) ∈ S) ∨ (K.1 = a - 1 ∧ (a - 1, y) ∈ S) := by
    rintro ⟨u, v⟩ y hK hu hv
    simp only at hu hv
    subst hv
    rcases hu with hu | hu
    · exact Or.inl ⟨hu, hu ▸ hK⟩
    · exact Or.inr ⟨hu, hu ▸ hK⟩
  have hnot : ∀ {K : Cell} {y : ℤ}, ((0, K.2) ∈ S → (a - 1, K.2) ∈ S → False) → K.2 = y →
      (0, y) ∈ S → (a - 1, y) ∈ S → False := by
    intro K y hn hKy
    subst hKy
    exact hn
  -- the two bottom tiles use the two long rows of the box
  have e12 : K₁.2 ≠ K₂.2 := by
    intro e12
    rw [← e12] at s₂
    have hbl : (0, y₅) ∈ S ↔ (a - 1, y₅) ∈ S := s₁.symm.trans s₂
    have hno : ∀ {K : Cell}, K ∈ S → (K.1 = 0 ∨ K.1 = a - 1) →
        (K.2 = y₅ ∨ K.2 = y₆) → ((0, K.2) ∈ S → (a - 1, K.2) ∈ S → False) →
        K.2 = y₆ := by
      intro K hK hx hr hI
      rcases hr with h | h
      · rcases hend hK hx h with ⟨-, h'⟩ | ⟨-, h'⟩
        · exact (hnot hI h h' (hbl.1 h')).elim
        · exact (hnot hI h (hbl.2 h') h').elim
      · exact h
    have e1 := hno m₁ x₁ r₁ n₁
    have e3 := hno m₃ x₃ r₃ n₃
    have e4 := hno m₄ x₄ r₄ n₄
    rw [show K₄.2 = K₃.2 from e4.trans e3.symm] at s₄
    have htl : (0, y₆) ∈ S ↔ (a - 1, y₆) ∈ S :=
      s₄.symm.trans s₃
    rcases hend m₁ x₁ e1 with ⟨-, h'⟩ | ⟨-, h'⟩
    · exact hnot n₁ e1 h' (htl.1 h')
    · exact hnot n₁ e1 (htl.2 h') h'
  -- and so do the two top tiles
  have e34 : K₃.2 ≠ K₄.2 := by
    intro e34
    rw [← e34] at s₄
    have htl : (0, y₆) ∈ S ↔ (a - 1, y₆) ∈ S :=
      s₄.symm.trans s₃
    have hno : ∀ {K : Cell}, K ∈ S → (K.1 = 0 ∨ K.1 = a - 1) →
        (K.2 = y₅ ∨ K.2 = y₆) → ((0, K.2) ∈ S → (a - 1, K.2) ∈ S → False) → K.2 = y₅ := by
      intro K hK hx hr hI
      rcases hr with h | h
      · exact h
      · rcases hend hK hx h with ⟨-, h'⟩ | ⟨-, h'⟩
        · exact (hnot hI h h' (htl.1 h')).elim
        · exact (hnot hI h (htl.2 h') h').elim
    exact e12 ((hno m₁ x₁ r₁ n₁).trans (hno m₂ x₂ r₂ n₂).symm)
  -- so each long row of the box has exactly one end in the free tile
  have hbot : ¬ ((0, y₅) ∈ S ∧ (a - 1, y₅) ∈ S) := by
    rintro ⟨h, h'⟩
    rcases r₁ with r | r
    · exact hnot n₁ r h h'
    · rcases r₂ with r' | r'
      · exact hnot n₂ r' h h'
      · exact e12 (r.trans r'.symm)
  have htop : ¬ ((0, y₆) ∈ S ∧
      (a - 1, y₆) ∈ S) := by
    rintro ⟨h, h'⟩
    rcases r₁ with r | r
    · rcases r₂ with r' | r'
      · exact e12 (r.trans r'.symm)
      · exact hnot n₂ r' h h'
    · exact hnot n₁ r h h'
  -- the end in use on each long row
  have hxB : ((0, y₅) ∈ S ∧ (a - 1, y₅) ∉ S) ∨ ((a - 1, y₅) ∈ S ∧ (0, y₅) ∉ S) := by
    have : (0, y₅) ∈ S ∨ (a - 1, y₅) ∈ S := by
      rcases r₁ with r | r
      · exact (hend m₁ x₁ r).imp And.right And.right
      · rcases r₂ with r' | r'
        · exact (hend m₂ x₂ r').imp And.right And.right
        · exact (e12 (r.trans r'.symm)).elim
    exact this.imp (fun h => ⟨h, fun h' => hbot ⟨h, h'⟩⟩) fun h => ⟨h, fun h' => hbot ⟨h', h⟩⟩
  have hxT : ((0, y₆) ∈ S ∧ (a - 1, y₆) ∉ S) ∨
      ((a - 1, y₆) ∈ S ∧ (0, y₆) ∉ S) := by
    have : (0, y₆) ∈ S ∨ (a - 1, y₆) ∈ S := by
      rcases r₁ with r | r
      · rcases r₂ with r' | r'
        · exact (e12 (r.trans r'.symm)).elim
        · exact (hend m₂ x₂ r').imp And.right And.right
      · exact (hend m₁ x₁ r).imp And.right And.right
    exact this.imp (fun h => ⟨h, fun h' => htop ⟨h, h'⟩⟩) fun h => ⟨h, fun h' => htop ⟨h', h⟩⟩
  -- the column of a corner cell in use is determined by its row
  have hcol : ∀ {K : Cell} {y x x' : ℤ}, K ∈ S → (K.1 = 0 ∨ K.1 = a - 1) → K.2 = y →
      (x = 0 ∧ x' = a - 1 ∨ x = a - 1 ∧ x' = 0) → (x', y) ∉ S → K.1 = x := by
    intro K y x x' hK hx hKy hxx' hx'
    rcases hend hK hx hKy with ⟨h, h'⟩ | ⟨h, h'⟩ <;>
      rcases hxx' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · exact (hx' h').elim
    · exact (hx' h').elim
    · exact h
  obtain ⟨xB, xT, hB, hT, hxx⟩ : ∃ xB xT : ℤ,
      (∀ {K : Cell}, K ∈ S → (K.1 = 0 ∨ K.1 = a - 1) → K.2 = y₅ → K.1 = xB) ∧
      (∀ {K : Cell}, K ∈ S → (K.1 = 0 ∨ K.1 = a - 1) → K.2 = y₆ →
        K.1 = xT) ∧
      ((xB = xT ∧ (xB, y₅) ∈ S ∧ (xB, y₆) ∈ S) ∨
        (((0, y₅) ∈ S ∧ (a - 1, y₅) ∉ S) ∧
          (a - 1, y₆) ∈ S ∧ (0, y₆) ∉ S) ∨
        (((a - 1, y₅) ∈ S ∧ (0, y₅) ∉ S) ∧
          (0, y₆) ∈ S ∧ (a - 1, y₆) ∉ S)) := by
    rcases hxB with ⟨hB, hB'⟩ | ⟨hB, hB'⟩ <;> rcases hxT with ⟨hT, hT'⟩ | ⟨hT, hT'⟩
    · exact ⟨0, 0, fun hK hx h => hcol hK hx h (Or.inl ⟨rfl, rfl⟩) hB',
        fun hK hx h => hcol hK hx h (Or.inl ⟨rfl, rfl⟩) hT', Or.inl ⟨rfl, hB, hT⟩⟩
    · exact ⟨0, a - 1, fun hK hx h => hcol hK hx h (Or.inl ⟨rfl, rfl⟩) hB',
        fun hK hx h => hcol hK hx h (Or.inr ⟨rfl, rfl⟩) hT',
        Or.inr (Or.inl ⟨⟨hB, hB'⟩, hT, hT'⟩)⟩
    · exact ⟨a - 1, 0, fun hK hx h => hcol hK hx h (Or.inr ⟨rfl, rfl⟩) hB',
        fun hK hx h => hcol hK hx h (Or.inl ⟨rfl, rfl⟩) hT',
        Or.inr (Or.inr ⟨⟨hB, hB'⟩, hT, hT'⟩)⟩
    · exact ⟨a - 1, a - 1, fun hK hx h => hcol hK hx h (Or.inr ⟨rfl, rfl⟩) hB',
        fun hK hx h => hcol hK hx h (Or.inr ⟨rfl, rfl⟩) hT', Or.inl ⟨rfl, hB, hT⟩⟩
  have hfst : ∀ {K K' : Cell}, K ∈ S → (K.1 = 0 ∨ K.1 = a - 1) →
      (K.2 = y₅ ∨ K.2 = y₆) → K' ∈ S → (K'.1 = 0 ∨ K'.1 = a - 1) →
      K.2 = K'.2 → K = K' := by
    intro K K' hK hx hr hK' hx' h
    refine Prod.ext ?_ h
    rcases hr with r | r
    · rw [hB hK hx r, hB hK' hx' (h ▸ r)]
    · rw [hT hK hx r, hT hK' hx' (h ▸ r)]
  rcases hxx with ⟨hBT, hlo, hhi⟩ | hdiag
  · -- both ends in use lie in one column of the box
    have c₁ : K₁.1 = xB := by
      rcases r₁ with r | r
      · exact hB m₁ x₁ r
      · exact (hT m₁ x₁ r).trans hBT.symm
    have c₂ : K₂.1 = xB := by
      rcases r₂ with r | r
      · exact hB m₂ x₂ r
      · exact (hT m₂ x₂ r).trans hBT.symm
    exact hsame xB c₁ c₂ hlo (hBT ▸ hhi)
  · -- the ends in use lie on a diagonal of the box
    have hβ : rowCount S K₁.2 ≠ rowCount S K₂.2 := by
      intro h
      rw [← h] at s₂
      have hbl := s₁.symm.trans s₂
      rcases hdiag with ⟨⟨h1, h2⟩, -⟩ | ⟨⟨h1, h2⟩, -⟩
      · exact h2 (hbl.1 h1)
      · exact h2 (hbl.2 h1)
    by_cases e13 : K₁.2 = K₃.2
    · have e24 : K₂.2 = K₄.2 := by omega
      have hBT := hturn (hfst m₁ x₁ r₁ m₃ x₃ e13) (hfst m₂ x₂ r₂ m₄ x₄ e24)
      rcases r₁ with r | r <;> rcases r₂ with r' | r'
      · exact e12 (r.trans r'.symm)
      · exact hβ (by rw [r, r', hBT])
      · exact hβ (by rw [r, r', hBT])
      · exact e12 (r.trans r'.symm)
    · have e14 : K₁.2 = K₄.2 := by omega
      have e23 : K₂.2 = K₃.2 := by omega
      rw [← e14] at s₄ l₄
      rw [← e23] at s₃ l₃
      rcases hdiag with ⟨⟨p1, p2⟩, p3, p4⟩ | ⟨⟨p1, p2⟩, p3, p4⟩
      · have q1 := s₁.2 p1
        have q2 := fun h => p2 (s₂.1 h)
        have q3 := s₃.2 p3
        have q4 := fun h => p4 (s₄.1 h)
        omega
      · have q1 := s₂.2 p1
        have q2 := fun h => p2 (s₁.1 h)
        have q3 := s₄.2 p3
        have q4 := fun h => p4 (s₃.1 h)
        omega

/-! ## Corner tiles in case (I) -/

/-- In case (I) with five tiles, every tile other than the free one is a corner
tile. Source: `report-4.md`, section 7, opening (line 485): the four corners lie in
"four tiles T_1, T_2, T_3, T_4; T_5 is the fifth". -/
theorem exists_corner_of_ne_free {P : Finset Cell} {a b : ℤ} {t : Fin 5 → Finset Cell}
    (ha : 0 < a) (hb : 0 < b) (ht : IsTiling P a b t) (hI : CornersInDistinctTiles a b t)
    {i : Fin 5} (hi : ∀ j : Fin 4, corner a b j ∉ t i) (i' : Fin 5) (hne : i' ≠ i) :
    ∃ j : Fin 4, corner a b j ∈ t i' := by
  have hex : ∀ j : Fin 4, ∃ k, corner a b j ∈ t k := fun j =>
    ht.exists_tile (corner_mem_R ha hb j)
  choose f hf using hex
  have hinj : Function.Injective f := fun j j' h => hI (f j) j j' (hf j) (by rw [h]; exact hf j')
  have hsub : Finset.univ.image f ⊆ Finset.univ.erase i := by
    intro k hk
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hk
    refine Finset.mem_erase.2 ⟨fun h => hi j ?_, Finset.mem_univ _⟩
    rw [← h]
    exact hf j
  have hcard : (Finset.univ.erase i).card ≤ (Finset.univ.image f).card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : i' ∈ Finset.univ.image f := by
    rw [heq]
    exact Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hmem
  exact ⟨j, hf j⟩

/-- A corner tile is less wide and less high than the rectangle. Source:
`report-4.md`, proof of Proposition 57 (d): "By (b) the box of a corner tile has at
most a - 1 columns and at most b - 1 rows". -/
theorem corner_tile_dims {P : Finset Cell} (hP : IsPolyomino P) (hnr : ¬ IsRectangular P)
    {a b : ℤ} {t : Fin 5 → Finset Cell} (ht : IsTiling P a b t)
    (hI : CornersInDistinctTiles a b t) {i : Fin 5} {j : Fin 4} (hj : corner a b j ∈ t i) :
    width (t i) ≤ a - 1 ∧ height (t i) ≤ b - 1 := by
  obtain ⟨ha, hb⟩ := ht.two_le hP hnr (by norm_num)
  have hR := ht.subset_R i
  have hc := (ht.tile_isPolyomino hP i).2
  have hside := corner_tile_sides P hP hnr a b t ht hI i j hj
  constructor
  · by_contra h
    have hw : width (t i) = a := by
      have := width_le_of_subset_R hR (by omega)
      omega
    have hspan := xSpan_eq_of_width_eq hR (by omega) hw
    obtain ⟨y, hy⟩ := exists_of_mem_xSpan hc (x := 0) (by
      rw [hspan, Finset.mem_Ico]
      omega)
    obtain ⟨y', hy'⟩ := exists_of_mem_xSpan hc (x := a - 1) (by
      rw [hspan, Finset.mem_Ico]
      omega)
    have h1 := (mem_leftCol.1 (hside 3 ⟨_, hy, mem_leftCol.2 ⟨hR hy, rfl⟩⟩)).2
    have h2 := (mem_rightCol.1 (hside 1 ⟨_, hy', mem_rightCol.2 ⟨hR hy', rfl⟩⟩)).2
    omega
  · by_contra h
    have hw : height (t i) = b := by
      have := height_le_of_subset_R hR (by omega)
      omega
    have hspan := ySpan_eq_of_height_eq hR (by omega) hw
    obtain ⟨x, hx⟩ := exists_of_mem_ySpan hc (y := 0) (by
      rw [hspan, Finset.mem_Ico]
      omega)
    obtain ⟨x', hx'⟩ := exists_of_mem_ySpan hc (y := b - 1) (by
      rw [hspan, Finset.mem_Ico]
      omega)
    have h1 := (mem_bottomRow.1 (hside 0 ⟨_, hx, mem_bottomRow.2 ⟨hR hx, rfl⟩⟩)).2
    have h2 := (mem_topRow.1 (hside 2 ⟨_, hx', mem_topRow.2 ⟨hR hx', rfl⟩⟩)).2
    omega

end CaseIOpposite

open CaseIOpposite

/-! ## Proposition 57 (d) -/

/-- Proposition 57 (d). PROVISIONAL. Source: `report-4.md`, Proposition 57 (d)
(line 510): "If T_5 meets two opposite sides, say the left and the right one, then
p = a < b, box(T_5) is a wide and q high, and every corner tile has a box q wide
and a high with q <= a - 1." In case (I) with five tiles, every tile other than
the free tile is a corner tile. -/
theorem proposition57d (P : Finset Cell) (hP : IsPolyomino P) (hnr : ¬ IsRectangular P)
    (a b : ℤ) (t : Fin 5 → Finset Cell) (ht : IsTiling P a b t)
    (hI : CornersInDistinctTiles a b t) (i : Fin 5) (hi : ∀ j : Fin 4, corner a b j ∉ t i)
    (hl : Meets (t i) (leftCol a b)) (hr : Meets (t i) (rightCol a b)) :
    width (t i) = a ∧ a ≤ b - 1 ∧ height (t i) ≤ a - 1 ∧
      ∀ i', i' ≠ i → width (t i') = height (t i) ∧ height (t i') = a := by
  obtain ⟨ha, hb⟩ := ht.two_le hP hnr (by norm_num)
  have hR := ht.subset_R i
  obtain ⟨⟨xl, yl⟩, hl, hl'⟩ := hl
  obtain ⟨⟨xr, yr⟩, hr, hr'⟩ := hr
  obtain rfl : xl = 0 := (mem_leftCol.1 hl').2
  obtain rfl : xr = a - 1 := (mem_rightCol.1 hr').2
  have hw : width (t i) = a := by
    have h1 := width_le_of_subset_R hR (by omega)
    have h2 := mem_xSpan_of_mem hr
    rw [xSpan_of_left hR hl, Finset.mem_Ico] at h2
    simp only at h2
    omega
  have hother : ∀ i', i' ≠ i → width (t i') = height (t i) ∧ height (t i') = a ∧
      width (t i') ≤ a - 1 ∧ height (t i') ≤ b - 1 := by
    intro i' hne
    obtain ⟨j, hj⟩ := exists_corner_of_ne_free (by omega) (by omega) ht hI hi i' hne
    obtain ⟨h1, h2⟩ := corner_tile_dims hP hnr ht hI hj
    rcases ht.dims i i' with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
  obtain ⟨i₁, hi₁⟩ := ht.exists_tile (corner_mem_R (a := a) (b := b) (by omega) (by omega) 0)
  obtain ⟨h1, h2, h3, h4⟩ := hother i₁ fun h => hi 0 (h ▸ hi₁)
  exact ⟨hw, by omega, by omega, fun i' hne => ⟨(hother i' hne).1, (hother i' hne).2.1⟩⟩

/-! ## Propositions 58 and 60: two opposite sides -/

/-- The setting of Proposition 58: case (I), and the free tile `t i₅` meets the
left and the right side. Source: `report-4.md`, Proposition 58 (line 526). -/
structure PatternD (P : Finset Cell) (a b : ℤ) (t : Fin 5 → Finset Cell) (i₅ : Fin 5) :
    Prop where
  /-- `P` is a polyomino. -/
  poly : IsPolyomino P
  /-- `P` is not rectangular. -/
  nonrect : ¬ IsRectangular P
  /-- A 5-copy tiling. -/
  tiling : IsTiling P a b t
  /-- Case (I). -/
  caseI : CornersInDistinctTiles a b t
  /-- `t i₅` holds no corner cell. -/
  free : ∀ j : Fin 4, corner a b j ∉ t i₅
  /-- `t i₅` meets the left side. -/
  left : Meets (t i₅) (leftCol a b)
  /-- `t i₅` meets the right side. -/
  right : Meets (t i₅) (rightCol a b)

namespace PatternD

variable {P : Finset Cell} {a b : ℤ} {t : Fin 5 → Finset Cell} {i₅ : Fin 5}

/-! ### The boxes in the setting of Proposition 58 -/

/-- The rectangle is at least 2 by 2. -/
theorem two_le (D : PatternD P a b t i₅) : 2 ≤ a ∧ 2 ≤ b :=
  D.tiling.two_le D.poly D.nonrect (by norm_num)

/-- Proposition 57 (d) in the setting of Proposition 58. -/
theorem dims (D : PatternD P a b t i₅) :
    width (t i₅) = a ∧ a ≤ b - 1 ∧ height (t i₅) ≤ a - 1 ∧
      ∀ i, i ≠ i₅ → width (t i) = height (t i₅) ∧ height (t i) = a :=
  proposition57d P D.poly D.nonrect a b t D.tiling D.caseI i₅ D.free D.left D.right

/-- Every tile lies in the rectangle, cell by cell. -/
theorem bounds (D : PatternD P a b t i₅) {i : Fin 5} {c : Cell} (hc : c ∈ t i) :
    (0 ≤ c.1 ∧ c.1 < a) ∧ 0 ≤ c.2 ∧ c.2 < b :=
  mem_R.1 (D.tiling.subset_R i hc)

/-- Every tile is connected. -/
theorem conn (D : PatternD P a b t i₅) (i : Fin 5) : EdgeConnected (t i) :=
  (D.tiling.tile_isPolyomino D.poly i).2

/-- A tile with a corner cell is not the free tile. -/
theorem ne_free (D : PatternD P a b t i₅) {i : Fin 5} {j : Fin 4} (hj : corner a b j ∈ t i) :
    i ≠ i₅ :=
  fun h => D.free j (h ▸ hj)

/-- The tiles are the free tile and the four corner tiles. -/
theorem tile_cases (D : PatternD P a b t i₅) (i : Fin 5) :
    i = i₅ ∨ ((0, 0) ∈ t i ∨ (a - 1, 0) ∈ t i) ∨
      (a - 1, b - 1) ∈ t i ∨ (0, b - 1) ∈ t i := by
  by_cases h : i = i₅
  · exact Or.inl h
  · obtain ⟨ha, hb⟩ := D.two_le
    obtain ⟨j, hj⟩ := exists_corner_of_ne_free (by omega) (by omega) D.tiling D.caseI D.free i h
    right
    fin_cases j
    · exact Or.inl (Or.inl hj)
    · exact Or.inl (Or.inr hj)
    · exact Or.inr (Or.inl hj)
    · exact Or.inr (Or.inr hj)

/-- The box of the tile at `(0, 0)`. -/
theorem cells_BL (D : PatternD P a b t i₅) {i : Fin 5} (h : (0, 0) ∈ t i) {c : Cell}
    (hc : c ∈ t i) : (0 ≤ c.1 ∧ c.1 < height (t i₅)) ∧ 0 ≤ c.2 ∧ c.2 < a := by
  obtain ⟨hw, hh⟩ := D.dims.2.2.2 i (D.ne_free (j := 0) h)
  have h1 := mem_xSpan_of_mem hc
  have h2 := mem_ySpan_of_mem hc
  rw [xSpan_of_left (D.tiling.subset_R i) h, Finset.mem_Ico] at h1
  rw [ySpan_of_bottom (D.tiling.subset_R i) h, Finset.mem_Ico] at h2
  omega

/-- The box of the tile at `(a - 1, 0)`. -/
theorem cells_BR (D : PatternD P a b t i₅) {i : Fin 5} (h : (a - 1, 0) ∈ t i) {c : Cell}
    (hc : c ∈ t i) : (a - height (t i₅) ≤ c.1 ∧ c.1 < a) ∧ 0 ≤ c.2 ∧ c.2 < a := by
  obtain ⟨hw, hh⟩ := D.dims.2.2.2 i (D.ne_free (j := 1) h)
  have h1 := mem_xSpan_of_mem hc
  have h2 := mem_ySpan_of_mem hc
  rw [xSpan_of_right (D.tiling.subset_R i) h, Finset.mem_Ico] at h1
  rw [ySpan_of_bottom (D.tiling.subset_R i) h, Finset.mem_Ico] at h2
  omega

/-- The box of the tile at `(a - 1, b - 1)`. -/
theorem cells_TR (D : PatternD P a b t i₅) {i : Fin 5} (h : (a - 1, b - 1) ∈ t i) {c : Cell}
    (hc : c ∈ t i) : (a - height (t i₅) ≤ c.1 ∧ c.1 < a) ∧ b - a ≤ c.2 ∧ c.2 < b := by
  obtain ⟨hw, hh⟩ := D.dims.2.2.2 i (D.ne_free (j := 2) h)
  have h1 := mem_xSpan_of_mem hc
  have h2 := mem_ySpan_of_mem hc
  rw [xSpan_of_right (D.tiling.subset_R i) h, Finset.mem_Ico] at h1
  rw [ySpan_of_top (D.tiling.subset_R i) h, Finset.mem_Ico] at h2
  omega

/-- The box of the tile at `(0, b - 1)`. -/
theorem cells_TL (D : PatternD P a b t i₅) {i : Fin 5} (h : (0, b - 1) ∈ t i) {c : Cell}
    (hc : c ∈ t i) : (0 ≤ c.1 ∧ c.1 < height (t i₅)) ∧ b - a ≤ c.2 ∧ c.2 < b := by
  obtain ⟨hw, hh⟩ := D.dims.2.2.2 i (D.ne_free (j := 3) h)
  have h1 := mem_xSpan_of_mem hc
  have h2 := mem_ySpan_of_mem hc
  rw [xSpan_of_left (D.tiling.subset_R i) h, Finset.mem_Ico] at h1
  rw [ySpan_of_top (D.tiling.subset_R i) h, Finset.mem_Ico] at h2
  omega

/-- The rows of the two bottom corner tiles. -/
theorem rows_bottom (D : PatternD P a b t i₅) {i : Fin 5}
    (h : (0, 0) ∈ t i ∨ (a - 1, 0) ∈ t i) {c : Cell} (hc : c ∈ t i) : 0 ≤ c.2 ∧ c.2 < a := by
  rcases h with h | h
  · exact (D.cells_BL h hc).2
  · exact (D.cells_BR h hc).2

/-- The rows of the two top corner tiles. -/
theorem rows_top (D : PatternD P a b t i₅) {i : Fin 5}
    (h : (a - 1, b - 1) ∈ t i ∨ (0, b - 1) ∈ t i) {c : Cell} (hc : c ∈ t i) :
    b - a ≤ c.2 ∧ c.2 < b := by
  rcases h with h | h
  · exact (D.cells_TR h hc).2
  · exact (D.cells_TL h hc).2

/-- A bottom corner tile has a cell in every row of `[0, a)`. -/
theorem exists_row_bottom (D : PatternD P a b t i₅) {i : Fin 5}
    (h : (0, 0) ∈ t i ∨ (a - 1, 0) ∈ t i) {r : ℤ} (h0 : 0 ≤ r) (hr : r < a) :
    ∃ x : ℤ, (x, r) ∈ t i := by
  refine exists_of_mem_ySpan (D.conn i) ?_
  rcases h with h | h
  · rw [ySpan_of_bottom (D.tiling.subset_R i) h,
      (D.dims.2.2.2 i (D.ne_free (j := 0) h)).2, Finset.mem_Ico]
    omega
  · rw [ySpan_of_bottom (D.tiling.subset_R i) h,
      (D.dims.2.2.2 i (D.ne_free (j := 1) h)).2, Finset.mem_Ico]
    omega

/-- A top corner tile has a cell in every row of `[b - a, b)`. -/
theorem exists_row_top (D : PatternD P a b t i₅) {i : Fin 5}
    (h : (a - 1, b - 1) ∈ t i ∨ (0, b - 1) ∈ t i) {r : ℤ} (h0 : b - a ≤ r) (hr : r < b) :
    ∃ x : ℤ, (x, r) ∈ t i := by
  refine exists_of_mem_ySpan (D.conn i) ?_
  rcases h with h | h
  · rw [ySpan_of_top (D.tiling.subset_R i) h,
      (D.dims.2.2.2 i (D.ne_free (j := 2) h)).2, Finset.mem_Ico]
    omega
  · rw [ySpan_of_top (D.tiling.subset_R i) h,
      (D.dims.2.2.2 i (D.ne_free (j := 3) h)).2, Finset.mem_Ico]
    omega

/-- The columns of the free tile. -/
theorem free_col (D : PatternD P a b t i₅) {c : Cell} (hc : c ∈ t i₅) : 0 ≤ c.1 ∧ c.1 < a :=
  (D.bounds hc).1

/-- The rows of the free tile. -/
theorem free_row (_D : PatternD P a b t i₅) {y₅ : ℤ}
    (hy : ySpan (t i₅) = Finset.Ico y₅ (y₅ + height (t i₅))) {c : Cell} (hc : c ∈ t i₅) :
    y₅ ≤ c.2 ∧ c.2 < y₅ + height (t i₅) := by
  have h := mem_ySpan_of_mem hc
  rw [hy, Finset.mem_Ico] at h
  exact h

/-! ### Proposition 58 -/

/-- Proposition 58 (a). PROVISIONAL. Source: `report-4.md`, Proposition 58 (a)
(line 528): "Every cell of T_1 or T_2 has a cell of T_5 strictly above it in its
column; every cell of T_3 or T_4 has one strictly below." Proof: `crossing`
("a connected set that avoids T_5 and contains (0, 0) and a cell of the top side
would interlace with T_5"), applied to the tile together with the cells of the
column above (below) `c`. -/
theorem prop58a (D : PatternD P a b t i₅) (i : Fin 5) :
    (((0, 0) ∈ t i ∨ (a - 1, 0) ∈ t i) →
        ∀ c ∈ t i, ∃ y : ℤ, c.2 < y ∧ (c.1, y) ∈ t i₅) ∧
      (((a - 1, b - 1) ∈ t i ∨ (0, b - 1) ∈ t i) →
        ∀ c ∈ t i, ∃ y : ℤ, y < c.2 ∧ (c.1, y) ∈ t i₅) := by
  obtain ⟨ha, hb⟩ := D.two_le
  constructor
  · intro h c hc
    have hcR := D.bounds hc
    have hne : i ≠ i₅ := h.elim (fun h => D.ne_free (j := 0) h) fun h => D.ne_free (j := 1) h
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, (x₀, (0 : ℤ)) ∈ t i := h.elim (fun h => ⟨_, h⟩) fun h => ⟨_, h⟩
    set A : Finset Cell := Finset.Ico c.1 (c.1 + 1) ×ˢ Finset.Ico c.2 b with hA
    have hmem : ∀ d : Cell, d ∈ A ↔ d.1 = c.1 ∧ c.2 ≤ d.2 ∧ d.2 < b := by
      intro d
      rw [hA, Finset.mem_product, Finset.mem_Ico, Finset.mem_Ico]
      omega
    have hAR : A ⊆ R a b := by
      intro d hd
      have hd' := (hmem d).1 hd
      exact mem_R.2 ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    have htop : (c.1, b - 1) ∈ A := (hmem _).2 ⟨rfl, by dsimp only; omega, by dsimp only; omega⟩
    obtain ⟨d, hd5, hd⟩ := crossing a b ha hb (t i₅) (t i ∪ A) (D.tiling.subset_R _) (D.conn _)
      D.left D.right (Finset.union_subset (D.tiling.subset_R i) hAR)
      ((D.conn i).union (edgeConnected_rect _ _ _ _) ⟨c, hc, (hmem c).2 ⟨rfl, le_rfl, hcR.2.2⟩⟩)
      ⟨_, Finset.mem_union_left _ hx₀, mem_bottomRow.2 ⟨D.tiling.subset_R i hx₀, rfl⟩⟩
      ⟨_, Finset.mem_union_right _ htop, mem_topRow.2 ⟨hAR htop, rfl⟩⟩
    rcases Finset.mem_union.1 hd with hd | hd
    · exact absurd (D.tiling.tile_unique hd hd5) hne
    · rw [hmem] at hd
      refine ⟨d.2, ?_, by rw [← hd.1]; exact hd5⟩
      rcases eq_or_lt_of_le hd.2.1 with h2 | h2
      · exact absurd (D.tiling.tile_unique hc
          (by rw [show c = d from Prod.ext hd.1.symm h2]; exact hd5)) hne
      · exact h2
  · intro h c hc
    have hcR := D.bounds hc
    have hne : i ≠ i₅ := h.elim (fun h => D.ne_free (j := 2) h) fun h => D.ne_free (j := 3) h
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, (x₀, b - 1) ∈ t i := h.elim (fun h => ⟨_, h⟩) fun h => ⟨_, h⟩
    set A : Finset Cell := Finset.Ico c.1 (c.1 + 1) ×ˢ Finset.Ico 0 (c.2 + 1) with hA
    have hmem : ∀ d : Cell, d ∈ A ↔ d.1 = c.1 ∧ 0 ≤ d.2 ∧ d.2 ≤ c.2 := by
      intro d
      rw [hA, Finset.mem_product, Finset.mem_Ico, Finset.mem_Ico]
      omega
    have hAR : A ⊆ R a b := by
      intro d hd
      have hd' := (hmem d).1 hd
      exact mem_R.2 ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    have hbot : (c.1, 0) ∈ A := (hmem _).2 ⟨rfl, le_rfl, hcR.2.1⟩
    obtain ⟨d, hd5, hd⟩ := crossing a b ha hb (t i₅) (t i ∪ A) (D.tiling.subset_R _) (D.conn _)
      D.left D.right (Finset.union_subset (D.tiling.subset_R i) hAR)
      ((D.conn i).union (edgeConnected_rect _ _ _ _) ⟨c, hc, (hmem c).2 ⟨rfl, hcR.2.1, le_rfl⟩⟩)
      ⟨_, Finset.mem_union_right _ hbot, mem_bottomRow.2 ⟨hAR hbot, rfl⟩⟩
      ⟨_, Finset.mem_union_left _ hx₀, mem_topRow.2 ⟨D.tiling.subset_R i hx₀, rfl⟩⟩
    rcases Finset.mem_union.1 hd with hd | hd
    · exact absurd (D.tiling.tile_unique hd hd5) hne
    · rw [hmem] at hd
      refine ⟨d.2, ?_, by rw [← hd.1]; exact hd5⟩
      rcases eq_or_lt_of_le hd.2.2 with h2 | h2
      · exact absurd (D.tiling.tile_unique hc
          (by rw [show c = d from Prod.ext hd.1.symm h2.symm]; exact hd5)) hne
      · exact h2

/-- Proposition 58 (a) in rows, bottom tiles: a cell of a bottom corner tile lies
below the last row of the free tile. -/
theorem row_lt_of_bottom (D : PatternD P a b t i₅) {y₅ : ℤ}
    (hy : ySpan (t i₅) = Finset.Ico y₅ (y₅ + height (t i₅))) {i : Fin 5}
    (h : (0, 0) ∈ t i ∨ (a - 1, 0) ∈ t i) {c : Cell} (hc : c ∈ t i) :
    c.2 < y₅ + height (t i₅) - 1 := by
  obtain ⟨y, hy1, hy2⟩ := (D.prop58a i).1 h c hc
  have := D.free_row hy hy2
  simp only at this
  omega

/-- Proposition 58 (a) in rows, top tiles: a cell of a top corner tile lies above
the first row of the free tile. -/
theorem lt_row_of_top (D : PatternD P a b t i₅) {y₅ : ℤ}
    (hy : ySpan (t i₅) = Finset.Ico y₅ (y₅ + height (t i₅))) {i : Fin 5}
    (h : (a - 1, b - 1) ∈ t i ∨ (0, b - 1) ∈ t i) {c : Cell} (hc : c ∈ t i) :
    y₅ < c.2 := by
  obtain ⟨y, hy1, hy2⟩ := (D.prop58a i).2 h c hc
  have := D.free_row hy hy2
  simp only at this
  omega

/-- The four corner tiles. -/
theorem exists_corner_tiles (D : PatternD P a b t i₅) :
    ∃ i₁ i₂ i₃ i₄ : Fin 5, (0, 0) ∈ t i₁ ∧ (a - 1, 0) ∈ t i₂ ∧ (a - 1, b - 1) ∈ t i₃ ∧
      (0, b - 1) ∈ t i₄ := by
  obtain ⟨ha, hb⟩ := D.two_le
  have hex : ∀ j : Fin 4, ∃ k, corner a b j ∈ t k := fun j =>
    D.tiling.exists_tile (corner_mem_R (by omega) (by omega) j)
  obtain ⟨i₁, h1⟩ := hex 0
  obtain ⟨i₂, h2⟩ := hex 1
  obtain ⟨i₃, h3⟩ := hex 2
  obtain ⟨i₄, h4⟩ := hex 3
  exact ⟨i₁, i₂, i₃, i₄, h1, h2, h3, h4⟩

/-- A cell below the first row of the free tile is in a bottom corner tile. -/
theorem below (D : PatternD P a b t i₅) {y₅ : ℤ}
    (hy : ySpan (t i₅) = Finset.Ico y₅ (y₅ + height (t i₅))) {i : Fin 5} {c : Cell}
    (hc : c ∈ t i) (hlt : c.2 < y₅) : (0, 0) ∈ t i ∨ (a - 1, 0) ∈ t i := by
  rcases D.tile_cases i with rfl | h | h
  · have := D.free_row hy hc
    omega
  · exact h
  · have := D.lt_row_of_top hy h hc
    omega

/-- A cell above the last row of the free tile is in a top corner tile. -/
theorem above (D : PatternD P a b t i₅) {y₅ : ℤ}
    (hy : ySpan (t i₅) = Finset.Ico y₅ (y₅ + height (t i₅))) {i : Fin 5} {c : Cell}
    (hc : c ∈ t i) (hlt : y₅ + height (t i₅) ≤ c.2) :
    (a - 1, b - 1) ∈ t i ∨ (0, b - 1) ∈ t i := by
  rcases D.tile_cases i with rfl | h | h
  · have := D.free_row hy hc
    omega
  · have := D.row_lt_of_bottom hy h hc
    omega
  · exact h

/-- The bounds of Proposition 58 (b) that do not need (c). Source: `report-4.md`,
proof of Proposition 58 (b) (line 536): "T_1 has a cell in row a - 1, so
y_5 + q - 1 >= a; T_4 has one in row b - a, so y_5 < b - a". -/
theorem prop58b_weak (D : PatternD P a b t i₅) {y₅ : ℤ}
    (hy : ySpan (t i₅) = Finset.Ico y₅ (y₅ + height (t i₅))) :
    (a + 1 - height (t i₅) ≤ y₅ ∧ y₅ ≤ a) ∧
      (a + 1 - height (t i₅) ≤ b - y₅ - height (t i₅) ∧ b - y₅ - height (t i₅) ≤ a) ∧
      a ≤ 2 * height (t i₅) := by
  obtain ⟨ha, hb⟩ := D.two_le
  obtain ⟨hw, hab, hq, hcorner⟩ := D.dims
  obtain ⟨i₁, i₂, i₃, i₄, h1, h2, h3, h4⟩ := D.exists_corner_tiles
  obtain ⟨x, hx⟩ := D.exists_row_bottom (r := a - 1) (Or.inl h1) (by omega) (by omega)
  have hb1 := D.row_lt_of_bottom hy (Or.inl h1) hx
  obtain ⟨x', hx'⟩ := D.exists_row_top (r := b - a) (Or.inr h4) (by omega) (by omega)
  have hb2 := D.lt_row_of_top hy (Or.inr h4) hx'
  simp only at hb1 hb2
  -- a row of `R` below `y₅` lies in the bottom tiles, so `y₅ ≤ a`
  have hya : y₅ ≤ a := by
    by_contra hcon
    have hR : ((0, a) : Cell) ∈ R a b := mem_R.2 (by simp only; omega)
    obtain ⟨i, hi⟩ := D.tiling.exists_tile hR
    have := D.rows_bottom (D.below hy hi (by simp only; omega)) hi
    simp only at this
    omega
  have hma : b - y₅ - height (t i₅) ≤ a := by
    by_contra hcon
    have hR : ((0, b - a - 1) : Cell) ∈ R a b := mem_R.2 (by simp only; omega)
    obtain ⟨i, hi⟩ := D.tiling.exists_tile hR
    have := D.rows_top (D.above hy hi (by simp only; omega)) hi
    simp only at this
    omega
  have ha2 : a ≤ 2 * height (t i₅) := by
    have hR : ((height (t i₅), 0) : Cell) ∈ R a b :=
      mem_R.2 (by
        have : 0 ≤ height (t i₅) := Int.natCast_nonneg _
        simp only
        omega)
    obtain ⟨i, hi⟩ := D.tiling.exists_tile hR
    rcases D.below hy hi (by simp only; omega) with h | h
    · have := D.cells_BL h hi
      simp only at this
      omega
    · have := D.cells_BR h hi
      simp only at this
      omega
  omega

/-- Proposition 58 (c). PROVISIONAL. Source: `report-4.md`, Proposition 58 (c)
(line 530): "P contains neither long side of its box in full." Proof idea (line
536): a full bottom row of `box(T_5)` gives `y_5 = a` and a 3-copy tiling of
`[0, a) x [a, b)` by `T_5`, `T_3`, `T_4`; the report cites Proposition 27, and
`three_copy` with `IsTiling.upper_part` does the same. -/
theorem prop58c (D : PatternD P a b t i₅) {y₅ : ℤ}
    (hy : ySpan (t i₅) = Finset.Ico y₅ (y₅ + height (t i₅))) :
    (∃ x : ℤ, 0 ≤ x ∧ x < a ∧ (x, y₅) ∉ t i₅) ∧
      ∃ x : ℤ, 0 ≤ x ∧ x < a ∧ (x, y₅ + height (t i₅) - 1) ∉ t i₅ := by
  obtain ⟨ha, hb⟩ := D.two_le
  obtain ⟨hw, hab, hq, hcorner⟩ := D.dims
  obtain ⟨i₁, i₂, i₃, i₄, h1, h2, h3, h4⟩ := D.exists_corner_tiles
  obtain ⟨⟨hb1, hb2⟩, ⟨hb3, hb4⟩, hb5⟩ := D.prop58b_weak hy
  have hn1 := D.ne_free (j := 0) h1
  have hn2 := D.ne_free (j := 1) h2
  have hn3 := D.ne_free (j := 2) h3
  have hn4 := D.ne_free (j := 3) h4
  have h12 : i₁ ≠ i₂ := by
    rintro rfl
    exact absurd (D.caseI i₁ 0 1 h1 h2) (by decide)
  have h34 : i₃ ≠ i₄ := by
    rintro rfl
    exact absurd (D.caseI i₃ 2 3 h3 h4) (by decide)
  constructor
  · by_contra hno
    push Not at hno
    have hya : y₅ = a := by
      by_contra hne
      obtain ⟨x, hx⟩ := D.exists_row_bottom (r := y₅) (Or.inl h1) (by omega) (by omega)
      have hxR := D.bounds hx
      simp only at hxR
      exact hn1 (D.tiling.tile_unique hx (hno x hxR.1.1 hxR.1.2))
    subst hya
    refine three_copy P D.poly D.nonrect y₅ (b - y₅) _
      (D.tiling.upper_part (m := 3) ![i₅, i₃, i₄] ?_ (c := y₅) (by omega) (by omega) ?_ ?_)
    · intro m n hmn
      fin_cases m <;> fin_cases n <;> simp at hmn ⊢
      · exact hn3 hmn.symm
      · exact hn4 hmn.symm
      · exact hn3 hmn
      · exact h34 hmn
      · exact hn4 hmn
      · exact h34 hmn.symm
    · intro m p hp
      fin_cases m
      · exact (D.free_row hy hp).1
      · exact (D.lt_row_of_top hy (Or.inl h3) hp).le
      · exact (D.lt_row_of_top hy (Or.inr h4) hp).le
    · intro i hi p hp
      rcases D.tile_cases i with rfl | h | h | h
      · exact absurd rfl (hi 0)
      · exact (D.rows_bottom h hp).2
      · exact absurd (D.tiling.tile_unique h3 h) (hi 1)
      · exact absurd (D.tiling.tile_unique h4 h) (hi 2)
  · by_contra hno
    push Not at hno
    have hya : y₅ + height (t i₅) = b - a := by
      by_contra hne
      obtain ⟨x, hx⟩ := D.exists_row_top (r := y₅ + height (t i₅) - 1) (Or.inl h3)
        (by omega) (by omega)
      have hxR := D.bounds hx
      simp only at hxR
      exact hn3 (D.tiling.tile_unique hx (hno x hxR.1.1 hxR.1.2))
    refine three_copy P D.poly D.nonrect a (b - a) _
      (D.tiling.lower_part (m := 3) ![i₅, i₁, i₂] ?_ (c := b - a) (by omega) (by omega) ?_ ?_)
    · intro m n hmn
      fin_cases m <;> fin_cases n <;> simp at hmn ⊢
      · exact hn1 hmn.symm
      · exact hn2 hmn.symm
      · exact hn1 hmn
      · exact h12 hmn
      · exact hn2 hmn
      · exact h12 hmn.symm
    · intro m p hp
      fin_cases m
      · have := (D.free_row hy hp).2
        omega
      · have := D.row_lt_of_bottom hy (Or.inl h1) hp
        omega
      · have := D.row_lt_of_bottom hy (Or.inr h2) hp
        omega
    · intro i hi p hp
      rcases D.tile_cases i with rfl | (h | h) | h
      · exact absurd rfl (hi 0)
      · exact absurd (D.tiling.tile_unique h1 h) (hi 1)
      · exact absurd (D.tiling.tile_unique h2 h) (hi 2)
      · exact (D.rows_top h hp).1

/-- Proposition 58 (b). PROVISIONAL. Source: `report-4.md`, Proposition 58 (b)
(line 529), with `q = height (t i₅)`, `[y₅, y₅ + q)` the rows of `box(T_5)` and
`m = b - y₅ - q`: "T_5 meets neither the bottom nor the top side.
a + 1 - q <= y_5 <= a - 1 and a + 1 - q <= m <= a - 1. The rows [0, y_5) lie in T_1
and T_2, the rows [y_5 + q, b) in T_3 and T_4. a <= 2q." -/
theorem prop58b (D : PatternD P a b t i₅) {y₅ : ℤ}
    (hy : ySpan (t i₅) = Finset.Ico y₅ (y₅ + height (t i₅))) :
    (a + 1 - height (t i₅) ≤ y₅ ∧ y₅ ≤ a - 1) ∧
      (a + 1 - height (t i₅) ≤ b - y₅ - height (t i₅) ∧
        b - y₅ - height (t i₅) ≤ a - 1) ∧
      a ≤ 2 * height (t i₅) ∧
      (∀ i, ∀ c ∈ t i, c.2 < y₅ → (0, 0) ∈ t i ∨ (a - 1, 0) ∈ t i) ∧
      ∀ i, ∀ c ∈ t i, y₅ + height (t i₅) ≤ c.2 → (a - 1, b - 1) ∈ t i ∨ (0, b - 1) ∈ t i := by
  obtain ⟨ha, hb⟩ := D.two_le
  obtain ⟨hw, hab, hq, hcorner⟩ := D.dims
  obtain ⟨⟨hb1, hb2⟩, ⟨hb3, hb4⟩, hb5⟩ := D.prop58b_weak hy
  obtain ⟨⟨x, hx0, hxa, hx⟩, x', hx'0, hx'a, hx'⟩ := D.prop58c hy
  refine ⟨⟨hb1, ?_⟩, ⟨hb3, ?_⟩, hb5, fun i c hc h => D.below hy hc h,
    fun i c hc h => D.above hy hc h⟩
  · by_contra hcon
    obtain ⟨i, hi⟩ := D.tiling.exists_tile (c := (x, y₅)) (mem_R.2 (by simp only; omega))
    rcases D.tile_cases i with rfl | h | h
    · exact hx hi
    · have := D.rows_bottom h hi
      simp only at this
      omega
    · have := D.lt_row_of_top hy h hi
      simp only at this
      omega
  · by_contra hcon
    obtain ⟨i, hi⟩ := D.tiling.exists_tile (c := (x', y₅ + height (t i₅) - 1))
      (mem_R.2 (by simp only; omega))
    rcases D.tile_cases i with rfl | h | h
    · exact hx' hi
    · have := D.row_lt_of_bottom hy h hi
      simp only at this
      omega
    · have := D.rows_top h hi
      simp only at this
      omega

/-- A congruence from the free tile to another tile, read cell by cell. -/
theorem mem_tile_iff {i : Fin 5} {g : GridIso} (hg : (t i₅).image g.apply = t i) (c : Cell) :
    g.apply c ∈ t i ↔ c ∈ t i₅ := by
  rw [← hg]
  exact g.apply_injective.mem_finset_image

/-- Proposition 58 (d), first sentence. PROVISIONAL. Source: `report-4.md`,
Proposition 58 (d) (line 531): "Each corner tile T_i puts a corner cell K_i of
box(P) on its corner of R". With `g` an isometry carrying `T_5` onto the corner
tile, the preimage `K_i` of the corner of `R` is one of the four corner cells of
`box(T_5)`, and `g` exchanges the axis directions. The equations for `beta_i` are
`colCount_corner` with `side_BL`, `side_BR`, `side_TR`, `side_TL`; the intervals and
the last sentence of (d) are `rowInterval_corner` and `not_both_ends`. -/
theorem prop58d (D : PatternD P a b t i₅) {y₅ : ℤ}
    (hy : ySpan (t i₅) = Finset.Ico y₅ (y₅ + height (t i₅))) (i : Fin 5) (j : Fin 4)
    (hj : corner a b j ∈ t i) (g : GridIso) (hg : (t i₅).image g.apply = t i) :
    g.swap = true ∧
      (g.inv.apply (corner a b j)).1 ∈ ({0, a - 1} : Finset ℤ) ∧
      (g.inv.apply (corner a b j)).2 ∈ ({y₅, y₅ + height (t i₅) - 1} : Finset ℤ) := by
  obtain ⟨ha, hb⟩ := D.two_le
  obtain ⟨hw, hab, hq, hcorner⟩ := D.dims
  have hs : g.swap = true := by
    by_contra h
    have h1 := (hcorner i (D.ne_free hj)).1
    rw [← hg, width_image, ite_eq_right h] at h1
    omega
  have hgK : g.apply (g.inv.apply (corner a b j)) = corner a b j := g.apply_inv_apply _
  generalize g.inv.apply (corner a b j) = K at hgK ⊢
  have hK : K ∈ t i₅ := (mem_tile_iff hg K).1 (by rw [hgK]; exact hj)
  obtain ⟨⟨xl, yl⟩, hl, hl'⟩ := D.left
  obtain ⟨⟨xr, yr⟩, hr, hr'⟩ := D.right
  obtain rfl : xl = 0 := (mem_leftCol.1 hl').2
  obtain rfl : xr = a - 1 := (mem_rightCol.1 hr').2
  have hq0 : 0 < height (t i₅) := by
    have := D.free_row hy hK
    omega
  obtain ⟨xb, hbo⟩ := exists_of_mem_ySpan (D.conn i₅) (y := y₅) (by
    rw [hy, Finset.mem_Ico]
    omega)
  obtain ⟨xt, hto⟩ := exists_of_mem_ySpan (D.conn i₅) (y := y₅ + height (t i₅) - 1) (by
    rw [hy, Finset.mem_Ico]
    omega)
  have b1 := D.bounds ((mem_tile_iff hg _).2 hl)
  have b2 := D.bounds ((mem_tile_iff hg _).2 hr)
  have b3 := D.bounds ((mem_tile_iff hg _).2 hbo)
  have b4 := D.bounds ((mem_tile_iff hg _).2 hto)
  have hKc := D.free_col hK
  have hKr := D.free_row hy hK
  have hcor : ((corner a b j).1 = 0 ∨ (corner a b j).1 = a - 1) ∧
      ((corner a b j).2 = 0 ∨ (corner a b j).2 = b - 1) := by
    fin_cases j <;> simp
  obtain ⟨hx, hy'⟩ := swap_apply g hs K
  rw [hgK] at hx hy'
  refine ⟨hs, ?_, ?_⟩
  · rw [Finset.mem_insert, Finset.mem_singleton]
    rcases hy' with h | h
    · have e1 := h (0, yl)
      have e2 := h (a - 1, yr)
      simp only at e1 e2
      omega
    · have e1 := h (0, yl)
      have e2 := h (a - 1, yr)
      simp only at e1 e2
      omega
  · rw [Finset.mem_insert, Finset.mem_singleton]
    rcases hx with h | h
    · have e1 := h (xb, y₅)
      have e2 := h (xt, y₅ + height (t i₅) - 1)
      simp only at e1 e2
      omega
    · have e1 := h (xb, y₅)
      have e2 := h (xt, y₅ + height (t i₅) - 1)
      simp only at e1 e2
      omega

/-- Proposition 58 (e), in row counts. PROVISIONAL. Source: `report-4.md`,
Proposition 58 (e) (line 532): the rows below `y_5` are shared by `T_1` and `T_2`
("u[c_1(j)] + u[c_2(j)] = a for 0 <= j < y_5"), and "In row y_5 each of T_1, T_2
has a cell". -/
theorem prop58e (D : PatternD P a b t i₅) {y₅ : ℤ}
    (hy : ySpan (t i₅) = Finset.Ico y₅ (y₅ + height (t i₅))) {i₁ i₂ : Fin 5}
    (h₁ : (0, 0) ∈ t i₁) (h₂ : (a - 1, 0) ∈ t i₂) :
    (∀ r : ℤ, 0 ≤ r → r < y₅ → rowCount (t i₁) r + rowCount (t i₂) r = a) ∧
      (∃ x : ℤ, (x, y₅) ∈ t i₁) ∧ ∃ x : ℤ, (x, y₅) ∈ t i₂ := by
  obtain ⟨ha, hb⟩ := D.two_le
  obtain ⟨⟨hb1, hb2⟩, -⟩ := D.prop58b hy
  obtain ⟨hw, hab, hq, hcorner⟩ := D.dims
  have h12 : i₁ ≠ i₂ := by
    rintro rfl
    exact Fin.zero_ne_one (D.caseI i₁ 0 1 h₁ h₂)
  refine ⟨fun r hr0 hr => ?_, D.exists_row_bottom (Or.inl h₁) (by omega) (by omega),
    D.exists_row_bottom (Or.inr h₂) (by omega) (by omega)⟩
  have hunion : ((t i₁).filter fun c => c.2 = r) ∪ ((t i₂).filter fun c => c.2 = r) =
      Finset.Ico 0 a ×ˢ ({r} : Finset ℤ) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico,
      Finset.mem_singleton]
    constructor
    · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩)
      · exact ⟨(D.bounds h).1, rfl⟩
      · exact ⟨(D.bounds h).1, rfl⟩
    · rintro ⟨hx, rfl⟩
      obtain ⟨i, hi⟩ := D.tiling.exists_tile (c := (x, y)) (mem_R.2 (by simp only; omega))
      rcases D.below hy hi hr with h | h
      · exact Or.inl ⟨D.tiling.tile_unique h h₁ ▸ hi, rfl⟩
      · exact Or.inr ⟨D.tiling.tile_unique h h₂ ▸ hi, rfl⟩
  have hdisj : Disjoint ((t i₁).filter fun c => c.2 = r) ((t i₂).filter fun c => c.2 = r) :=
    Finset.disjoint_filter_filter (D.tiling.disjoint _ _ h12)
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_product, Finset.card_singleton, mul_one, Int.card_Ico] at hcard
  unfold rowCount
  omega

/-! ### The corner cells `K_i` and the sides -/

/-- The data of a corner tile: an isometry from the free tile, and the corner cell
`K` of the box of the free tile that it puts on the corner of `R`. -/
theorem corner_data (D : PatternD P a b t i₅) {y₅ : ℤ}
    (hy : ySpan (t i₅) = Finset.Ico y₅ (y₅ + height (t i₅))) {i : Fin 5} {j : Fin 4}
    (hj : corner a b j ∈ t i) :
    ∃ (g : GridIso) (K : Cell), (t i₅).image g.apply = t i ∧ g.swap = true ∧
      g.apply K = corner a b j ∧ K ∈ t i₅ ∧ (K.1 = 0 ∨ K.1 = a - 1) ∧
      (K.2 = y₅ ∨ K.2 = y₅ + height (t i₅) - 1) := by
  obtain ⟨g, hg⟩ := D.tiling.tiles_congruent i₅ i
  obtain ⟨hs, h1, h2⟩ := D.prop58d hy i j hj g hg
  rw [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  have hK := g.apply_inv_apply (corner a b j)
  exact ⟨g, _, hg, hs, hK, (mem_tile_iff hg _).1 (by rw [hK]; exact hj), h1, h2⟩

/-- `beta_i`: the cells of a corner tile on its vertical side are the cells of the
free tile in the row of `K`. Source: `report-4.md`, Proposition 58 (d). -/
theorem colCount_corner (_D : PatternD P a b t i₅) {i : Fin 5} {g : GridIso} {K c₀ : Cell}
    (hg : (t i₅).image g.apply = t i) (hs : g.swap = true) (hK : g.apply K = c₀) :
    colCount (t i) c₀.1 = rowCount (t i₅) K.2 := by
  have hx : ∀ c, (g.apply c).1 = c₀.1 ↔ c.2 = K.2 := by
    intro c
    rw [← hK]
    rcases (swap_apply g hs K).1 with h | h
    · have := h c
      omega
    · have := h c
      omega
  have hset : (t i).filter (fun c => c.1 = c₀.1) =
      ((t i₅).filter fun c => c.2 = K.2).image g.apply := by
    ext c
    rw [Finset.mem_filter, ← hg, Finset.mem_image, Finset.mem_image]
    constructor
    · rintro ⟨⟨d, hd, rfl⟩, h⟩
      exact ⟨d, Finset.mem_filter.2 ⟨hd, (hx d).1 h⟩, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      rw [Finset.mem_filter] at hd
      exact ⟨⟨d, hd.1, rfl⟩, (hx d).2 hd.2⟩
  unfold colCount rowCount
  rw [hset, Finset.card_image_of_injective _ g.apply_injective]

/-- The row of the free tile through `K` is an interval. Source: `report-4.md`,
Proposition 58 (d): "P meets ... the long row through K_i in intervals". -/
theorem rowInterval_corner (D : PatternD P a b t i₅) {i : Fin 5} {g : GridIso} {K c₀ : Cell}
    (hg : (t i₅).image g.apply = t i) (hs : g.swap = true) (hK : g.apply K = c₀)
    (hc₀ : c₀.1 = 0 ∨ c₀.1 = a - 1) : RowInterval (t i₅) K.2 := by
  obtain ⟨-, -, hI0, hI1⟩ := sides_are_intervals P D.poly 5 a b t D.tiling i
  have hcol : ColInterval (t i) c₀.1 := by
    rcases hc₀ with h | h <;> rw [h] <;> assumption
  intro x₁ x₂ x₃ h12 h23 h1 h3
  have hx : ∀ x, (g.apply (x, K.2)).1 = c₀.1 := by
    intro x
    rw [← hK]
    rcases (swap_apply g hs K).1 with h | h
    · have := h (x, K.2)
      simp only at this
      omega
    · have := h (x, K.2)
      simp only at this
      omega
  have hmem : ∀ x, (x, K.2) ∈ t i₅ ↔ (c₀.1, (g.apply (x, K.2)).2) ∈ t i := by
    intro x
    rw [← mem_tile_iff hg, ← hx x]
  rw [hmem] at h1 h3 ⊢
  rcases (swap_apply g hs K).2 with h | h
  · have e1 := h (x₁, K.2)
    have e2 := h (x₂, K.2)
    have e3 := h (x₃, K.2)
    simp only at e1 e2 e3
    exact hcol _ _ _ (by omega) (by omega) h1 h3
  · have e1 := h (x₁, K.2)
    have e2 := h (x₂, K.2)
    have e3 := h (x₃, K.2)
    simp only at e1 e2 e3
    exact hcol _ _ _ (by omega) (by omega) h3 h1

/-- Equations (*) at `(0, 0)`: the tile there has at least `y₅` cells in column 0,
and exactly `y₅` when the free tile holds the lower left corner of its box. Source:
`report-4.md`, Proposition 58 (d), "beta_1 = y_5 + l". -/
theorem side_BL (D : PatternD P a b t i₅) {y₅ : ℤ}
    (hy : ySpan (t i₅) = Finset.Ico y₅ (y₅ + height (t i₅))) {i : Fin 5}
    (h : (0, 0) ∈ t i) :
    y₅ ≤ colCount (t i) 0 ∧ (colCount (t i) 0 = y₅ ↔ (0, y₅) ∈ t i₅) := by
  obtain ⟨ha, hb⟩ := D.two_le
  obtain ⟨hw, hab, hq, -⟩ := D.dims
  obtain ⟨⟨hb1, hb2⟩, -⟩ := D.prop58b hy
  obtain ⟨-, -, hI0, -⟩ := sides_are_intervals P D.poly 5 a b t D.tiling i
  obtain ⟨h1, h2⟩ := col_count_low (S := t i) (x := 0) (n := y₅) (by omega)
    (fun y hy0 hyy => by
      obtain ⟨k, hk⟩ := D.tiling.exists_tile (c := (0, y)) (mem_R.2 (by simp only; omega))
      rcases D.below hy hk hyy with h' | h'
      · exact D.tiling.tile_unique h' h ▸ hk
      · have := D.cells_BR h' hk
        simp only at this
        omega)
    (fun y hy' => (D.bounds hy').2.1) hI0
  refine ⟨h1, h2.trans ⟨fun hn => ?_, fun h5 hn => D.ne_free (j := 0) h
    (D.tiling.tile_unique hn h5)⟩⟩
  obtain ⟨k, hk⟩ := D.tiling.exists_tile (c := (0, y₅)) (mem_R.2 (by simp only; omega))
  rcases D.tile_cases k with rfl | (h' | h') | h'
  · exact hk
  · exact (hn (D.tiling.tile_unique h' h ▸ hk)).elim
  · have := D.cells_BR h' hk
    simp only at this
    omega
  · have := D.lt_row_of_top hy h' hk
    simp only at this
    omega

/-- Equations (*) at `(a - 1, 0)`. -/
theorem side_BR (D : PatternD P a b t i₅) {y₅ : ℤ}
    (hy : ySpan (t i₅) = Finset.Ico y₅ (y₅ + height (t i₅))) {i : Fin 5}
    (h : (a - 1, 0) ∈ t i) :
    y₅ ≤ colCount (t i) (a - 1) ∧
      (colCount (t i) (a - 1) = y₅ ↔ (a - 1, y₅) ∈ t i₅) := by
  obtain ⟨ha, hb⟩ := D.two_le
  obtain ⟨hw, hab, hq, -⟩ := D.dims
  obtain ⟨⟨hb1, hb2⟩, -⟩ := D.prop58b hy
  obtain ⟨-, -, -, hI1⟩ := sides_are_intervals P D.poly 5 a b t D.tiling i
  obtain ⟨h1, h2⟩ := col_count_low (S := t i) (x := a - 1) (n := y₅) (by omega)
    (fun y hy0 hyy => by
      obtain ⟨k, hk⟩ := D.tiling.exists_tile (c := (a - 1, y)) (mem_R.2 (by simp only; omega))
      rcases D.below hy hk hyy with h' | h'
      · have := D.cells_BL h' hk
        simp only at this
        omega
      · exact D.tiling.tile_unique h' h ▸ hk)
    (fun y hy' => (D.bounds hy').2.1) hI1
  refine ⟨h1, h2.trans ⟨fun hn => ?_, fun h5 hn => D.ne_free (j := 1) h
    (D.tiling.tile_unique hn h5)⟩⟩
  obtain ⟨k, hk⟩ := D.tiling.exists_tile (c := (a - 1, y₅)) (mem_R.2 (by simp only; omega))
  rcases D.tile_cases k with rfl | (h' | h') | h'
  · exact hk
  · have := D.cells_BL h' hk
    simp only at this
    omega
  · exact (hn (D.tiling.tile_unique h' h ▸ hk)).elim
  · have := D.lt_row_of_top hy h' hk
    simp only at this
    omega

/-- Equations (*) at `(a - 1, b - 1)`. -/
theorem side_TR (D : PatternD P a b t i₅) {y₅ : ℤ}
    (hy : ySpan (t i₅) = Finset.Ico y₅ (y₅ + height (t i₅))) {i : Fin 5}
    (h : (a - 1, b - 1) ∈ t i) :
    b - (y₅ + height (t i₅)) ≤ colCount (t i) (a - 1) ∧
      (colCount (t i) (a - 1) = b - (y₅ + height (t i₅)) ↔
        (a - 1, y₅ + height (t i₅) - 1) ∈ t i₅) := by
  obtain ⟨ha, hb⟩ := D.two_le
  obtain ⟨hw, hab, hq, -⟩ := D.dims
  obtain ⟨⟨hb1, hb2⟩, ⟨hb3, hb4⟩, -⟩ := D.prop58b hy
  obtain ⟨-, -, -, hI1⟩ := sides_are_intervals P D.poly 5 a b t D.tiling i
  obtain ⟨h1, h2⟩ := col_count_high (S := t i) (x := a - 1) (n := y₅ + height (t i₅)) (b := b)
    (by omega)
    (fun y hy0 hyy => by
      obtain ⟨k, hk⟩ := D.tiling.exists_tile (c := (a - 1, y)) (mem_R.2 (by simp only; omega))
      rcases D.above hy hk hy0 with h' | h'
      · exact D.tiling.tile_unique h' h ▸ hk
      · have := D.cells_TL h' hk
        simp only at this
        omega)
    (fun y hy' => (D.bounds hy').2.2) hI1
  refine ⟨h1, h2.trans ⟨fun hn => ?_, fun h5 hn => D.ne_free (j := 2) h
    (D.tiling.tile_unique hn h5)⟩⟩
  obtain ⟨k, hk⟩ := D.tiling.exists_tile (c := (a - 1, y₅ + height (t i₅) - 1))
    (mem_R.2 (by simp only; omega))
  rcases D.tile_cases k with rfl | h' | h' | h'
  · exact hk
  · have := D.row_lt_of_bottom hy h' hk
    simp only at this
    omega
  · exact (hn (D.tiling.tile_unique h' h ▸ hk)).elim
  · have := D.cells_TL h' hk
    simp only at this
    omega

/-- Equations (*) at `(0, b - 1)`. -/
theorem side_TL (D : PatternD P a b t i₅) {y₅ : ℤ}
    (hy : ySpan (t i₅) = Finset.Ico y₅ (y₅ + height (t i₅))) {i : Fin 5}
    (h : (0, b - 1) ∈ t i) :
    b - (y₅ + height (t i₅)) ≤ colCount (t i) 0 ∧
      (colCount (t i) 0 = b - (y₅ + height (t i₅)) ↔
        (0, y₅ + height (t i₅) - 1) ∈ t i₅) := by
  obtain ⟨ha, hb⟩ := D.two_le
  obtain ⟨hw, hab, hq, -⟩ := D.dims
  obtain ⟨⟨hb1, hb2⟩, ⟨hb3, hb4⟩, -⟩ := D.prop58b hy
  obtain ⟨-, -, hI0, -⟩ := sides_are_intervals P D.poly 5 a b t D.tiling i
  obtain ⟨h1, h2⟩ := col_count_high (S := t i) (x := 0) (n := y₅ + height (t i₅)) (b := b)
    (by omega)
    (fun y hy0 hyy => by
      obtain ⟨k, hk⟩ := D.tiling.exists_tile (c := (0, y)) (mem_R.2 (by simp only; omega))
      rcases D.above hy hk hy0 with h' | h'
      · have := D.cells_TR h' hk
        simp only at this
        omega
      · exact D.tiling.tile_unique h' h ▸ hk)
    (fun y hy' => (D.bounds hy').2.2) hI0
  refine ⟨h1, h2.trans ⟨fun hn => ?_, fun h5 hn => D.ne_free (j := 3) h
    (D.tiling.tile_unique hn h5)⟩⟩
  obtain ⟨k, hk⟩ := D.tiling.exists_tile (c := (0, y₅ + height (t i₅) - 1))
    (mem_R.2 (by simp only; omega))
  rcases D.tile_cases k with rfl | h' | h' | h'
  · exact hk
  · have := D.row_lt_of_bottom hy h' hk
    simp only at this
    omega
  · have := D.cells_TR h' hk
    simp only at this
    omega
  · exact (hn (D.tiling.tile_unique h' h ▸ hk)).elim

/-! ### Proposition 60 -/

/-- The interval through `K` on a long row of the box does not reach both ends of
the row. Source: `report-4.md`, Proposition 58 (d): "No two of the K_i are the two
ends of one long row." -/
theorem not_both_ends (D : PatternD P a b t i₅) {y₅ : ℤ}
    (hy : ySpan (t i₅) = Finset.Ico y₅ (y₅ + height (t i₅))) {y : ℤ}
    (hyy : y = y₅ ∨ y = y₅ + height (t i₅) - 1) (hrow : RowInterval (t i₅) y)
    (h0 : (0, y) ∈ t i₅) (h1 : (a - 1, y) ∈ t i₅) : False := by
  obtain ⟨⟨x, hx0, hxa, hx⟩, x', hx'0, hx'a, hx'⟩ := D.prop58c hy
  rcases hyy with rfl | rfl
  · exact hx (hrow 0 x (a - 1) hx0 (by omega) h0 h1)
  · exact hx' (hrow 0 x' (a - 1) hx'0 (by omega) h0 h1)

/-- The case `a = 2 q` of Proposition 60. Source: `report-4.md`, Proposition 60,
"{BL, TL}" (line 559): "by 58(e) u[j] = q for j < y_5: these columns of P are full.
So x_B >= y_5 >= a + 1 - q = q + 1, and the bottom row of T_5 covers [0, q) in row
y_5: against 58(e)." Here it is used for either side of the box, through `T_1` or
`T_2`. -/
theorem two_mul_height_ne (D : PatternD P a b t i₅) {y₅ : ℤ}
    (hy : ySpan (t i₅) = Finset.Ico y₅ (y₅ + height (t i₅))) :
    a ≠ 2 * height (t i₅) := by
  intro ha2
  obtain ⟨ha, hb⟩ := D.two_le
  obtain ⟨hw, hab, hq, -⟩ := D.dims
  obtain ⟨⟨hb1, hb2⟩, -⟩ := D.prop58b hy
  obtain ⟨i₁, i₂, i₃, i₄, h1, h2, h3, h4⟩ := D.exists_corner_tiles
  obtain ⟨g, K, hg, hs, hgK, hK, hK1, hK2⟩ := D.corner_data hy (j := 0) h1
  rw [corner_zero] at hgK
  have hn1 := D.ne_free (j := 0) h1
  have hn2 := D.ne_free (j := 1) h2
  obtain ⟨-, ⟨x₁, hx₁⟩, x₂, hx₂⟩ := D.prop58e hy h1 h2
  have hc1 := D.cells_BL h1 hx₁
  have hc2 := D.cells_BR h2 hx₂
  simp only at hc1 hc2
  -- a cell `(u, y₅)` whose image under `g` lies below row `y₅` is in the free tile
  have key : ∀ u : ℤ, 0 ≤ u → u < a → (u - K.1 < y₅ ∧ K.1 - u < y₅) → (u, y₅) ∈ t i₅ := by
    intro u hu0 hua hlt
    have hbox : ((u, y₅) : Cell) ∈ boundingBox (t i₅) := by
      rw [mem_boundingBox, hy, Finset.mem_Ico,
        xSpan_eq_of_width_eq (D.tiling.subset_R i₅) (by omega) hw, Finset.mem_Ico]
      simp only
      omega
    have himg : g.apply (u, y₅) ∈ boundingBox (t i₁) := by
      rw [← hg, boundingBox_image]
      exact Finset.mem_image_of_mem _ hbox
    rw [mem_boundingBox, xSpan_of_left (D.tiling.subset_R i₁) h1,
      ySpan_of_bottom (D.tiling.subset_R i₁) h1, Finset.mem_Ico, Finset.mem_Ico,
      (D.dims.2.2.2 i₁ hn1).1, (D.dims.2.2.2 i₁ hn1).2] at himg
    have hrow : (g.apply (u, y₅)).2 < y₅ := by
      rcases (swap_apply g hs K).2 with h | h
      · have e := h (u, y₅)
        rw [hgK] at e
        simp only at e
        omega
      · have e := h (u, y₅)
        rw [hgK] at e
        simp only at e
        omega
    obtain ⟨k, hk⟩ := D.tiling.exists_tile (c := g.apply (u, y₅)) (mem_R.2 (by omega))
    rw [← mem_tile_iff hg]
    rcases D.below hy hk hrow with h' | h'
    · exact D.tiling.tile_unique h' h1 ▸ hk
    · have := D.cells_BR h' hk
      omega
  rcases hK1 with h | h
  · exact hn1 (D.tiling.tile_unique hx₁ (key x₁ (by omega) (by omega) (by omega)))
  · exact hn2 (D.tiling.tile_unique hx₂ (key x₂ (by omega) (by omega) (by omega)))

/-- A full end column of the free tile is not the column of both `K_1` and `K_2`.
Source: `report-4.md`, Proposition 60, "{BL, TL}" (line 559): "Both ends of the left
column are in P, so l = 0 and lambda = q; all four K_i are in the left column, so
alpha_1 = alpha_2 = q and a = 2q". -/
theorem not_same_full_column (D : PatternD P a b t i₅) {y₅ : ℤ}
    (hy : ySpan (t i₅) = Finset.Ico y₅ (y₅ + height (t i₅))) {i₁ i₂ : Fin 5}
    (h1 : (0, 0) ∈ t i₁) (h2 : (a - 1, 0) ∈ t i₂) {g₁ g₂ : GridIso} {K₁ K₂ : Cell}
    (hg₁ : (t i₅).image g₁.apply = t i₁) (hs₁ : g₁.swap = true) (hK₁ : g₁.apply K₁ = (0, 0))
    (hg₂ : (t i₅).image g₂.apply = t i₂) (hs₂ : g₂.swap = true)
    (hK₂ : g₂.apply K₂ = (a - 1, 0))
    (hr₁ : K₁.2 = y₅ ∨ K₁.2 = y₅ + height (t i₅) - 1)
    (hr₂ : K₂.2 = y₅ ∨ K₂.2 = y₅ + height (t i₅) - 1) {x : ℤ} (hx₁ : K₁.1 = x)
    (hx₂ : K₂.1 = x) (hlo : (x, y₅) ∈ t i₅) (hhi : (x, y₅ + height (t i₅) - 1) ∈ t i₅) :
    False := by
  obtain ⟨ha, hb⟩ := D.two_le
  obtain ⟨hw, hab, hq, -⟩ := D.dims
  obtain ⟨⟨hb1, hb2⟩, -, hb5, -⟩ := D.prop58b hy
  refine D.two_mul_height_ne hy ?_
  by_contra hne
  have h12 : i₁ ≠ i₂ := by
    rintro rfl
    exact Fin.zero_ne_one (D.caseI i₁ 0 1 h1 h2)
  -- the cell of the column opposite to `K`
  have hopp : ∀ {K : Cell}, K.1 = x → (K.2 = y₅ ∨ K.2 = y₅ + height (t i₅) - 1) →
      ∃ v : ℤ, (x, v) ∈ t i₅ ∧
        (v - K.2 = height (t i₅) - 1 ∨ K.2 - v = height (t i₅) - 1) := by
    intro K _ h
    rcases h with h | h
    · exact ⟨_, hhi, Or.inl (by omega)⟩
    · exact ⟨_, hlo, Or.inr (by omega)⟩
  obtain ⟨v₁, hv₁, hd₁⟩ := hopp hx₁ hr₁
  obtain ⟨v₂, hv₂, hd₂⟩ := hopp hx₂ hr₂
  have m₁ := (mem_tile_iff hg₁ _).2 hv₁
  have m₂ := (mem_tile_iff hg₂ _).2 hv₂
  have b₁ := D.bounds m₁
  have b₂ := D.bounds m₂
  have e₁ : g₁.apply (x, v₁) = (height (t i₅) - 1, 0) := by
    obtain ⟨hp, hq'⟩ := swap_apply g₁ hs₁ K₁
    rw [hK₁] at hp hq'
    have hp' := hp.imp (fun h => h (x, v₁)) fun h => h (x, v₁)
    have hq'' := hq'.imp (fun h => h (x, v₁)) fun h => h (x, v₁)
    simp only at hp' hq''
    exact Prod.ext (by simp only; omega) (by simp only; omega)
  have e₂ : g₂.apply (x, v₂) = (a - height (t i₅), 0) := by
    obtain ⟨hp, hq'⟩ := swap_apply g₂ hs₂ K₂
    rw [hK₂] at hp hq'
    have hp' := hp.imp (fun h => h (x, v₂)) fun h => h (x, v₂)
    have hq'' := hq'.imp (fun h => h (x, v₂)) fun h => h (x, v₂)
    simp only at hp' hq''
    exact Prod.ext (by simp only; omega) (by simp only; omega)
  rw [e₁] at m₁
  rw [e₂] at m₂
  have hrow := (sides_are_intervals P D.poly 5 a b t D.tiling i₂).1
  have m₂' := hrow _ (height (t i₅) - 1) _ (by omega) (by omega) m₂ h2
  exact h12 (D.tiling.tile_unique m₁ m₂')

/-- The half turn of `R` carries a corner tile onto the opposite one when both put
the same corner cell `K` of the box on their corners. Source: `report-4.md`,
Proposition 60 (line 565): "The half turn H of R carries T_1 ... onto the image of P
with K_1 on the corner (a - 1, b - 1), which is T_3". -/
theorem halfTurn_mem (D : PatternD P a b t i₅) {i i' : Fin 5} {g g' : GridIso} {K c₀ : Cell}
    (hg : (t i₅).image g.apply = t i) (hs : g.swap = true) (hK : g.apply K = c₀)
    (hg' : (t i₅).image g'.apply = t i') (hs' : g'.swap = true)
    (hK' : g'.apply K = (a - 1 - c₀.1, b - 1 - c₀.2)) (hx : c₀.1 = 0 ∨ c₀.1 = a - 1)
    (hy : c₀.2 = 0 ∨ c₀.2 = b - 1) {c : Cell} (hc : c ∈ t i) :
    (a - 1 - c.1, b - 1 - c.2) ∈ t i' := by
  have hc' := hc
  rw [← hg] at hc'
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hc'
  have m' := (mem_tile_iff hg' d).2 hd
  have b1 := D.bounds hc
  have b2 := D.bounds m'
  obtain ⟨p1, p2⟩ := swap_apply g hs K
  obtain ⟨q1, q2⟩ := swap_apply g' hs' K
  rw [hK] at p1 p2
  rw [hK'] at q1 q2
  have p1' := p1.imp (fun h => h d) fun h => h d
  have p2' := p2.imp (fun h => h d) fun h => h d
  have q1' := q1.imp (fun h => h d) fun h => h d
  have q2' := q2.imp (fun h => h d) fun h => h d
  simp only at q1' q2'
  have e : g'.apply d = (a - 1 - (g.apply d).1, b - 1 - (g.apply d).2) :=
    Prod.ext (by simp only; omega) (by simp only; omega)
  rw [← e]
  exact m'

/-- Proposition 60, the last two assignments. Source: `report-4.md`, Proposition 60
(line 565): "So H(T_5) = T_5, and P is preserved by the half turn of its box. Then
the top row of P is the half turn of the bottom row". -/
theorem rowCount_eq_of_halfTurn (D : PatternD P a b t i₅) {y₅ : ℤ}
    (hy : ySpan (t i₅) = Finset.Ico y₅ (y₅ + height (t i₅)))
    (hH : ∀ i, i ≠ i₅ → ∃ i', i' ≠ i₅ ∧ ∀ c ∈ t i, (a - 1 - c.1, b - 1 - c.2) ∈ t i') :
    rowCount (t i₅) y₅ = rowCount (t i₅) (y₅ + height (t i₅) - 1) := by
  have hclosed : ∀ c ∈ t i₅, (a - 1 - c.1, b - 1 - c.2) ∈ t i₅ := by
    intro c hc
    have hcR := D.bounds hc
    obtain ⟨k, hk⟩ := D.tiling.exists_tile (c := (a - 1 - c.1, b - 1 - c.2))
      (mem_R.2 (by simp only; omega))
    by_cases hk5 : k = i₅
    · exact hk5 ▸ hk
    · obtain ⟨k', hk', hmap⟩ := hH k hk5
      have hb := hmap _ hk
      simp only [sub_sub_cancel] at hb
      exact (hk' (D.tiling.tile_unique hb hc)).elim
  have hq0 : 0 < height (t i₅) := by
    obtain ⟨c, hc, -⟩ := D.left
    have := D.free_row hy hc
    omega
  obtain ⟨xb, hbo⟩ := exists_of_mem_ySpan (D.conn i₅) (y := y₅) (by
    rw [hy, Finset.mem_Ico]
    omega)
  obtain ⟨xt, hto⟩ := exists_of_mem_ySpan (D.conn i₅) (y := y₅ + height (t i₅) - 1) (by
    rw [hy, Finset.mem_Ico]
    omega)
  have r1 := D.free_row hy (hclosed _ hbo)
  have r2 := D.free_row hy (hclosed _ hto)
  simp only at r1 r2
  have hle : ∀ y y' : ℤ, b - 1 - y = y' → rowCount (t i₅) y ≤ rowCount (t i₅) y' := by
    intro y y' hyy'
    unfold rowCount
    refine Int.ofNat_le.2 (Finset.card_le_card_of_injOn
      (fun c : Cell => (a - 1 - c.1, b - 1 - c.2)) ?_ ?_)
    · intro c hc
      have hc' := Finset.mem_filter.1 hc
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hclosed c hc'.1, ?_⟩)
      have := hc'.2
      dsimp only
      omega
    · intro c _ c' _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (by omega) (by omega)
  exact le_antisymm (hle _ _ (by omega)) (hle _ _ (by omega))

/-- Proposition 60. Source: `report-4.md`, section 7, Proposition 60 (line 553):
"In case (I), T_5 does not meet two opposite sides of R." Proof (lines 555-565):
the set of corners of `box(P)` in use is `{BL}`, `{BL, TL}` or `{BL, TR}` up to the
symmetries; each is excluded by the interval equations (*) and 58 (c), (e), the
last two assignments by the half turn. -/
theorem absurd (D : PatternD P a b t i₅) : False := by
  obtain ⟨ha, hb⟩ := D.two_le
  obtain ⟨hw, hab, hq, -⟩ := D.dims
  obtain ⟨lo, hi, hle, hspan, -⟩ := ySpan_eq_Icc (D.tiling.tile_isPolyomino D.poly i₅).1
  obtain ⟨y₅, hy⟩ : ∃ y₅, ySpan (t i₅) = Finset.Ico y₅ (y₅ + height (t i₅)) := by
    refine ⟨lo, ?_⟩
    have hh : height (t i₅) = hi + 1 - lo := by
      unfold height
      rw [hspan, Int.card_Icc]
      omega
    rw [hh, hspan]
    ext y
    rw [Finset.mem_Icc, Finset.mem_Ico]
    omega
  obtain ⟨⟨hb1, hb2⟩, ⟨hb3, hb4⟩, hb5, -⟩ := D.prop58b hy
  obtain ⟨i₁, i₂, i₃, i₄, h1, h2, h3, h4⟩ := D.exists_corner_tiles
  obtain ⟨g₁, K₁, hg₁, hs₁, hK₁, m₁, x₁, r₁⟩ := D.corner_data hy (j := 0) h1
  obtain ⟨g₂, K₂, hg₂, hs₂, hK₂, m₂, x₂, r₂⟩ := D.corner_data hy (j := 1) h2
  obtain ⟨g₃, K₃, hg₃, hs₃, hK₃, m₃, x₃, r₃⟩ := D.corner_data hy (j := 2) h3
  obtain ⟨g₄, K₄, hg₄, hs₄, hK₄, m₄, x₄, r₄⟩ := D.corner_data hy (j := 3) h4
  rw [corner_zero] at hK₁
  rw [corner_one] at hK₂
  rw [corner_two] at hK₃
  rw [corner_three] at hK₄
  have β₁ := D.colCount_corner hg₁ hs₁ hK₁
  have β₂ := D.colCount_corner hg₂ hs₂ hK₂
  have β₃ := D.colCount_corner hg₃ hs₃ hK₃
  have β₄ := D.colCount_corner hg₄ hs₄ hK₄
  have I₁ := D.rowInterval_corner hg₁ hs₁ hK₁ (Or.inl rfl)
  have I₂ := D.rowInterval_corner hg₂ hs₂ hK₂ (Or.inr rfl)
  have I₃ := D.rowInterval_corner hg₃ hs₃ hK₃ (Or.inr rfl)
  have I₄ := D.rowInterval_corner hg₄ hs₄ hK₄ (Or.inl rfl)
  obtain ⟨l₁, s₁⟩ := D.side_BL hy h1
  obtain ⟨l₂, s₂⟩ := D.side_BR hy h2
  obtain ⟨l₃, s₃⟩ := D.side_TR hy h3
  obtain ⟨l₄, s₄⟩ := D.side_TL hy h4
  simp only at β₁ β₂ β₃ β₄
  rw [β₁] at l₁ s₁
  rw [β₂] at l₂ s₂
  rw [β₃] at l₃ s₃
  rw [β₄] at l₄ s₄
  -- the half turn, once `K₁ = K₃` and `K₂ = K₄`
  have hturn : K₁ = K₃ → K₂ = K₄ →
      rowCount (t i₅) y₅ = rowCount (t i₅) (y₅ + height (t i₅) - 1) := by
    intro e13 e24
    subst e13
    subst e24
    refine D.rowCount_eq_of_halfTurn hy fun i hi => ?_
    rcases D.tile_cases i with rfl | (h | h) | h | h
    · exact (hi rfl).elim
    · rw [D.tiling.tile_unique h h1]
      exact ⟨i₃, D.ne_free (j := 2) h3, fun c hc => D.halfTurn_mem hg₁ hs₁ hK₁ hg₃ hs₃
        (by rw [hK₃, sub_zero, sub_zero]) (Or.inl rfl) (Or.inl rfl) hc⟩
    · rw [D.tiling.tile_unique h h2]
      exact ⟨i₄, D.ne_free (j := 3) h4, fun c hc => D.halfTurn_mem hg₂ hs₂ hK₂ hg₄ hs₄
        (by rw [hK₄, sub_zero, sub_self]) (Or.inr rfl) (Or.inl rfl) hc⟩
    · rw [D.tiling.tile_unique h h3]
      exact ⟨i₁, D.ne_free (j := 0) h1, fun c hc => D.halfTurn_mem hg₃ hs₃ hK₃ hg₁ hs₁
        (by rw [hK₁, sub_self, sub_self]) (Or.inr rfl) (Or.inr rfl) hc⟩
    · rw [D.tiling.tile_unique h h4]
      exact ⟨i₂, D.ne_free (j := 1) h2, fun c hc => D.halfTurn_mem hg₄ hs₄ hK₄ hg₂ hs₂
        (by rw [hK₂, sub_zero, sub_self]) (Or.inl rfl) (Or.inr rfl) hc⟩
  exact corner_cells_absurd m₁ m₂ m₃ m₄ x₁ x₂ x₃ x₄ r₁ r₂ r₃ r₄
    (D.not_both_ends hy r₁ I₁) (D.not_both_ends hy r₂ I₂) (D.not_both_ends hy r₃ I₃)
    (D.not_both_ends hy r₄ I₄) l₁ l₂ l₃ l₄ s₁ s₂ s₃ s₄ hturn
    fun x c₁ c₂ hlo hhi => D.not_same_full_column hy h1 h2 hg₁ hs₁ hK₁ hg₂ hs₂ hK₂ r₁ r₂ c₁ c₂
      hlo hhi

end PatternD

/-- Proposition 60 for both pairs of opposite sides: the free tile does not meet
two opposite sides. Proof idea: `PatternD.absurd` for the tiling and for its
transpose. -/
theorem free_tile_not_opposite (P : Finset Cell) (hP : IsPolyomino P)
    (hnr : ¬ IsRectangular P) (a b : ℤ) (t : Fin 5 → Finset Cell)
    (ht : IsTiling P a b t) (hI : CornersInDistinctTiles a b t) (i : Fin 5)
    (hi : ∀ j : Fin 4, corner a b j ∉ t i) (s : Fin 4) (hs : Meets (t i) (side a b s))
    (hs' : Meets (t i) (side a b (s + 2))) : False := by
  have hv : Meets (t i) (leftCol a b) → Meets (t i) (rightCol a b) → False := fun hl hr =>
    PatternD.absurd ⟨hP, hnr, ht, hI, hi, hl, hr⟩
  have hh : Meets (t i) (bottomRow a b) → Meets (t i) (topRow a b) → False := by
    rintro ⟨c, hc, hb⟩ ⟨d, hd, ht'⟩
    rw [mem_bottomRow] at hb
    rw [mem_topRow] at ht'
    have hcR := mem_R.1 hb.1
    have hdR := mem_R.1 ht'.1
    refine PatternD.absurd (i₅ := i) ⟨hP, hnr, ht.transpose, hI.transpose, ?_,
      ⟨GridIso.transpose.apply c, Finset.mem_image_of_mem _ hc, ?_⟩,
      ⟨GridIso.transpose.apply d, Finset.mem_image_of_mem _ hd, ?_⟩⟩
    · intro j hj
      obtain ⟨e, he, hej⟩ := Finset.mem_image.1 hj
      rw [GridIso.transpose_apply] at hej
      have hcor : ∃ j' : Fin 4, e = corner a b j' := by
        fin_cases j <;> simp [Prod.ext_iff] at hej
        · exact ⟨0, Prod.ext hej.2 hej.1⟩
        · exact ⟨3, Prod.ext hej.2 hej.1⟩
        · exact ⟨2, Prod.ext hej.2 hej.1⟩
        · exact ⟨1, Prod.ext hej.2 hej.1⟩
      obtain ⟨j', rfl⟩ := hcor
      exact hi j' he
    · rw [GridIso.transpose_apply, mem_leftCol, mem_R]
      simp only
      omega
    · rw [GridIso.transpose_apply, mem_rightCol, mem_R]
      simp only
      omega
  fin_cases s
  · exact hh hs hs'
  · exact hv hs' hs
  · exact hh hs' hs
  · exact hv hs hs'

/-- Corollary 59 with Proposition 60: the internal statement behind the frozen
`corollary59_proposition60_free_tile_one_side`, with the Spec's conclusion (no
two different sides are both met). Sources: `report-4.md`, Corollary 59
(line 542) and Proposition 60 (line 553). Two different sides are adjacent or
opposite. -/
theorem free_tile_one_side (P : Finset Cell)
    (hP : IsPolyomino P) (hnr : ¬ IsRectangular P) (a b : ℤ)
    (t : Fin 5 → Finset Cell) (ht : IsTiling P a b t)
    (hI : CornersInDistinctTiles a b t)
    (i : Fin 5) (hi : ∀ j : Fin 4, corner a b j ∉ t i) :
    ¬ ∃ s s' : Fin 4, s ≠ s' ∧ Meets (t i) (side a b s) ∧ Meets (t i) (side a b s') := by
  rintro ⟨s, s', hne, hs, hs'⟩
  have hadj := free_tile_not_adjacent P hP hnr a b t ht hI i hi
  have hopp := free_tile_not_opposite P hP hnr a b t ht hI i hi
  have key : s' = s + 1 ∨ s = s' + 1 ∨ s' = s + 2 := by
    revert hne
    fin_cases s <;> fin_cases s' <;> decide
  rcases key with h | h | h
  · exact hadj s hs (h ▸ hs')
  · exact hadj s' hs' (h ▸ hs)
  · exact hopp s hs (h ▸ hs')

end PolyominoOddOrder
