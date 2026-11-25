module

public import PolyominoOddOrder.Defs
public import Mathlib.Tactic

/-!
# Foundation 1: cells, adjacency, reach, components, counts (`Grid.lean`)

Blueprint unit F. Facts the reports treat as obvious: membership
in `R a b` and its sides, symmetry of adjacency, the reach relation behind
`EdgeConnected`, unions of connected sets, walks as lists, the discrete
intermediate-value property of a connected set, components of a cell set, and
the row and column counts `u[x]`, `v[y]` of the reports.

Sources: `report.md` section 1 (conventions) and the places in sections 2 of
`report.md` and 1 to 8 of `report-4.md` where a connected set "has a cell in
every row between" or "stays in one component". Commit `e5ca51d`.
-/

@[expose] public section

namespace PolyominoOddOrder

/-! ## Membership in the rectangle, its sides and corners -/

/-- Membership in `R a b`. (`report.md` section 1.) -/
theorem mem_R {a b : ℤ} {c : Cell} :
    c ∈ R a b ↔ (0 ≤ c.1 ∧ c.1 < a) ∧ 0 ≤ c.2 ∧ c.2 < b := by
  simp [R, Finset.mem_product, Finset.mem_Ico]

/-- `R a b` has `a * b` cells (truncated at 0). -/
theorem card_R (a b : ℤ) : (R a b).card = a.toNat * b.toNat := by
  simp [R, Finset.card_product, Int.card_Ico]

theorem mem_bottomRow {a b : ℤ} {c : Cell} : c ∈ bottomRow a b ↔ c ∈ R a b ∧ c.2 = 0 := by
  simp [bottomRow]

theorem mem_rightCol {a b : ℤ} {c : Cell} : c ∈ rightCol a b ↔ c ∈ R a b ∧ c.1 = a - 1 := by
  simp [rightCol]

theorem mem_topRow {a b : ℤ} {c : Cell} : c ∈ topRow a b ↔ c ∈ R a b ∧ c.2 = b - 1 := by
  simp [topRow]

theorem mem_leftCol {a b : ℤ} {c : Cell} : c ∈ leftCol a b ↔ c ∈ R a b ∧ c.1 = 0 := by
  simp [leftCol]

@[simp] theorem side_zero (a b : ℤ) : side a b 0 = bottomRow a b := rfl
@[simp] theorem side_one (a b : ℤ) : side a b 1 = rightCol a b := rfl
@[simp] theorem side_two (a b : ℤ) : side a b 2 = topRow a b := rfl
@[simp] theorem side_three (a b : ℤ) : side a b 3 = leftCol a b := rfl

@[simp] theorem corner_zero (a b : ℤ) : corner a b 0 = (0, 0) := rfl
@[simp] theorem corner_one (a b : ℤ) : corner a b 1 = (a - 1, 0) := rfl
@[simp] theorem corner_two (a b : ℤ) : corner a b 2 = (a - 1, b - 1) := rfl
@[simp] theorem corner_three (a b : ℤ) : corner a b 3 = (0, b - 1) := rfl

/-- `Meets` is symmetric. -/
theorem Meets.symm {S T : Finset Cell} (h : Meets S T) : Meets T S := by
  obtain ⟨c, hS, hT⟩ := h
  exact ⟨c, hT, hS⟩

/-- Two sets that meet are not disjoint. -/
theorem Meets.not_disjoint {S T : Finset Cell} (h : Meets S T) : ¬ Disjoint S T := by
  obtain ⟨c, hS, hT⟩ := h
  exact fun hd => Finset.disjoint_left.1 hd hS hT

/-! ## Adjacency -/

/-- `Adj` is symmetric. -/
theorem Adj.symm {c d : Cell} (h : Adj c d) : Adj d c := by
  unfold Adj at *
  omega

/-- Adjacent cells are different. -/
theorem Adj.ne {c d : Cell} (h : Adj c d) : c ≠ d := by
  rintro rfl
  unfold Adj at h
  omega

/-- Adjacent cells differ by one in one coordinate, written out. -/
theorem adj_iff {x y x' y' : ℤ} :
    Adj (x, y) (x', y') ↔
      (x = x' ∧ (y + 1 = y' ∨ y' + 1 = y)) ∨ (y = y' ∧ (x + 1 = x' ∨ x' + 1 = x)) :=
  Iff.rfl

/-! ## Reach and connectivity -/

/-- `d` is reached from `c` by a chain of cells of `S`: the relation behind
`EdgeConnected`. -/
def Reach (S : Finset Cell) (c d : Cell) : Prop :=
  Relation.ReflTransGen (fun x y : Cell => x ∈ S ∧ y ∈ S ∧ Adj x y) c d

theorem edgeConnected_iff {S : Finset Cell} :
    EdgeConnected S ↔ ∀ c ∈ S, ∀ d ∈ S, Reach S c d :=
  Iff.rfl

theorem Reach.refl (S : Finset Cell) (c : Cell) : Reach S c c :=
  Relation.ReflTransGen.refl

theorem Reach.trans {S : Finset Cell} {c d e : Cell} (h : Reach S c d) (h' : Reach S d e) :
    Reach S c e :=
  Relation.ReflTransGen.trans h h'

/-- One step of the reach relation. -/
theorem Reach.step {S : Finset Cell} {c d : Cell} (hc : c ∈ S) (hd : d ∈ S) (h : Adj c d) :
    Reach S c d :=
  Relation.ReflTransGen.single ⟨hc, hd, h⟩

/-- Reach is symmetric, because `Adj` is. -/
theorem Reach.symm {S : Finset Cell} {c d : Cell} (h : Reach S c d) : Reach S d c := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, hbc.2.2.symm⟩ ih

/-- Reach in a set is reach in every larger set. -/
theorem Reach.mono {S S' : Finset Cell} (hSS' : S ⊆ S') {c d : Cell} (h : Reach S c d) :
    Reach S' c d := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih ⟨hSS' hbc.1, hSS' hbc.2.1, hbc.2.2⟩

/-- A chain that starts in `S` ends in `S`. -/
theorem Reach.mem_right {S : Finset Cell} {c d : Cell} (hc : c ∈ S) (h : Reach S c d) :
    d ∈ S := by
  induction h with
  | refl => exact hc
  | tail _ hbc _ => exact hbc.2.1

/-- A set is edge-connected when every cell is reached from one hub cell. -/
theorem edgeConnected_of_hub {S : Finset Cell} (h : Cell) (hub : ∀ c ∈ S, Reach S h c) :
    EdgeConnected S := by
  intro c hc d hd
  exact Reach.trans (Reach.symm (hub c hc)) (hub d hd)

/-- The union of two connected sets that share a cell is connected. Used wherever
the reports enlarge a tile by full rows (`report.md`, Lemma 3 (ii)). -/
theorem EdgeConnected.union {S S' : Finset Cell} (hS : EdgeConnected S)
    (hS' : EdgeConnected S') (h : Meets S S') : EdgeConnected (S ∪ S') := by
  obtain ⟨m, hmS, hmS'⟩ := h
  refine edgeConnected_of_hub m ?_
  intro c hc
  rcases Finset.mem_union.1 hc with hcS | hcS'
  · exact Reach.mono Finset.subset_union_left (hS m hmS c hcS)
  · exact Reach.mono Finset.subset_union_right (hS' m hmS' c hcS')

/-- The union of two connected sets joined by an edge is connected. -/
theorem EdgeConnected.union_of_adj {S S' : Finset Cell} (hS : EdgeConnected S)
    (hS' : EdgeConnected S') {c d : Cell} (hc : c ∈ S) (hd : d ∈ S') (hcd : Adj c d) :
    EdgeConnected (S ∪ S') := by
  refine edgeConnected_of_hub c ?_
  intro e he
  rcases Finset.mem_union.1 he with heS | heS'
  · exact Reach.mono Finset.subset_union_left (hS c hc e heS)
  · exact Reach.trans
      (Reach.step (Finset.mem_union_left _ hc) (Finset.mem_union_right _ hd) hcd)
      (Reach.mono Finset.subset_union_right (hS' d hd e heS'))

/-- A chain in `S` as a list of cells: first cell `c`, last cell `d`, all in `S`,
consecutive cells adjacent. Source: the chain `p = s_0, ..., s_r = p'` in the proof
of `report.md`, Lemma 1. -/
theorem Reach.exists_walk {S : Finset Cell} {c d : Cell} (hc : c ∈ S) (h : Reach S c d) :
    ∃ l : List Cell, l.head? = some c ∧ l.getLast? = some d ∧ (∀ x ∈ l, x ∈ S) ∧
      l.IsChain Adj := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[d], rfl, rfl, by simpa using hc, List.isChain_singleton d⟩
  | head hbc _ ih =>
    obtain ⟨l, hhead, hlast, hmem, hchain⟩ := ih hbc.2.1
    obtain ⟨l', rfl⟩ := List.head?_eq_some_iff.1 hhead
    refine ⟨_ :: _ :: l', rfl, ?_, ?_, List.isChain_cons_cons.2 ⟨hbc.2.2, hchain⟩⟩
    · rw [List.getLast?_cons_cons]
      exact hlast
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hbc.1
      · exact hmem x hx

/-- A chain in `S` from row `c.2` to row `d.2` has a cell in every row between:
along a chain the row changes by at most 1. -/
theorem Reach.exists_in_row {S : Finset Cell} {c d : Cell} (hc : c ∈ S) (h : Reach S c d)
    {y : ℤ} (h1 : c.2 ≤ y) (h2 : y ≤ d.2) : ∃ x : ℤ, (x, y) ∈ S := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    obtain rfl : d.2 = y := le_antisymm h1 h2
    exact ⟨d.1, hc⟩
  | @head c e hce _ ih =>
    rcases eq_or_lt_of_le h1 with rfl | hlt
    · exact ⟨c.1, hc⟩
    · refine ih hce.2.1 ?_
      have hadj := hce.2.2
      unfold Adj at hadj
      omega

/-- A chain in `S` from column `c.1` to column `d.1` has a cell in every column
between. -/
theorem Reach.exists_in_col {S : Finset Cell} {c d : Cell} (hc : c ∈ S) (h : Reach S c d)
    {x : ℤ} (h1 : c.1 ≤ x) (h2 : x ≤ d.1) : ∃ y : ℤ, (x, y) ∈ S := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    obtain rfl : d.1 = x := le_antisymm h1 h2
    exact ⟨d.2, hc⟩
  | @head c e hce _ ih =>
    rcases eq_or_lt_of_le h1 with rfl | hlt
    · exact ⟨c.2, hc⟩
    · refine ih hce.2.1 ?_
      have hadj := hce.2.2
      unfold Adj at hadj
      omega

/-- Discrete intermediate value, rows: a connected set with a cell in row `y₁` and
a cell in row `y₃` has a cell in every row between. Source: `report.md`, proof of
Lemma 4 (c): "a connected set with cells both above and below a row has a cell in
that row". -/
theorem EdgeConnected.exists_in_row {S : Finset Cell} (hS : EdgeConnected S) {c d : Cell}
    (hc : c ∈ S) (hd : d ∈ S) {y : ℤ} (h1 : c.2 ≤ y) (h2 : y ≤ d.2) :
    ∃ x : ℤ, (x, y) ∈ S := by
  exact Reach.exists_in_row hc (hS c hc d hd) h1 h2

/-- Discrete intermediate value, columns. -/
theorem EdgeConnected.exists_in_col {S : Finset Cell} (hS : EdgeConnected S) {c d : Cell}
    (hc : c ∈ S) (hd : d ∈ S) {x : ℤ} (h1 : c.1 ≤ x) (h2 : x ≤ d.1) :
    ∃ y : ℤ, (x, y) ∈ S := by
  exact Reach.exists_in_col hc (hS c hc d hd) h1 h2

/-- A row segment `[x₁, x₂] × {y}` inside `S` joins its two ends in `S`. -/
theorem Reach.along_row {S : Finset Cell} {x₁ x₂ y : ℤ} (hx : x₁ ≤ x₂)
    (h : ∀ z, x₁ ≤ z → z ≤ x₂ → (z, y) ∈ S) : Reach S (x₁, y) (x₂, y) := by
  induction x₂, hx using Int.leInduction with
  | base => exact Reach.refl S _
  | succ n hn ih =>
    refine Reach.trans (ih fun z hz1 hz2 => h z hz1 (by omega)) ?_
    exact Reach.step (h n hn (by omega)) (h (n + 1) (by omega) le_rfl)
      (Or.inr ⟨rfl, Or.inl rfl⟩)

/-- A column segment `{x} × [y₁, y₂]` inside `S` joins its two ends in `S`. -/
theorem Reach.along_col {S : Finset Cell} {x y₁ y₂ : ℤ} (hy : y₁ ≤ y₂)
    (h : ∀ z, y₁ ≤ z → z ≤ y₂ → (x, z) ∈ S) : Reach S (x, y₁) (x, y₂) := by
  induction y₂, hy using Int.leInduction with
  | base => exact Reach.refl S _
  | succ n hn ih =>
    refine Reach.trans (ih fun z hz1 hz2 => h z hz1 (by omega)) ?_
    exact Reach.step (h n hn (by omega)) (h (n + 1) (by omega) le_rfl)
      (Or.inl ⟨rfl, Or.inl rfl⟩)

/-- A full row segment `[x₁, x₂] × {y}` is connected. Source: `report.md`, proof of
Lemma 3 (ii): "Full rows are connected to one another". -/
theorem edgeConnected_rowSegment (x₁ x₂ y : ℤ) :
    EdgeConnected (Finset.Icc x₁ x₂ ×ˢ ({y} : Finset ℤ)) := by
  refine edgeConnected_of_hub (x₁, y) ?_
  rintro ⟨x, y'⟩ hc
  simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton] at hc
  obtain ⟨⟨hx1, hx2⟩, rfl⟩ := hc
  refine Reach.along_row hx1 fun z hz1 hz2 => ?_
  simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton, and_true]
  exact ⟨hz1, hz2.trans hx2⟩

/-- A rectangle of cells is connected. -/
theorem edgeConnected_rect (x₁ x₂ y₁ y₂ : ℤ) :
    EdgeConnected (Finset.Ico x₁ x₂ ×ˢ Finset.Ico y₁ y₂) := by
  refine edgeConnected_of_hub (x₁, y₁) ?_
  rintro ⟨x, y⟩ hc
  simp only [Finset.mem_product, Finset.mem_Ico] at hc
  obtain ⟨⟨hx1, hx2⟩, hy1, hy2⟩ := hc
  refine Reach.trans (Reach.along_row (y := y₁) hx1 fun z hz1 hz2 => ?_)
    (Reach.along_col hy1 fun z hz1 hz2 => ?_)
  · simp only [Finset.mem_product, Finset.mem_Ico]
    omega
  · simp only [Finset.mem_product, Finset.mem_Ico]
    omega

/-! ## Components -/

open Classical in
/-- The component of `q` in the cell set `A`: the cells of `A` reached from `q`
inside `A`. Source: "the component of q in R minus gamma", `report-4.md` section 7,
Lemma 56 and the Remark after it. -/
noncomputable def component (A : Finset Cell) (q : Cell) : Finset Cell :=
  A.filter fun c => Reach A q c

theorem mem_component {A : Finset Cell} {q c : Cell} :
    c ∈ component A q ↔ c ∈ A ∧ Reach A q c := by
  classical
  simp [component]

/-- A component is closed under adjacency inside `A`. -/
theorem component_closed {A : Finset Cell} {q c d : Cell} (hc : c ∈ component A q)
    (hd : d ∈ A) (hcd : Adj c d) : d ∈ component A q := by
  rw [mem_component] at hc ⊢
  exact ⟨hd, Reach.trans hc.2 (Reach.step hc.1 hd hcd)⟩

/-- A component is connected. -/
theorem edgeConnected_component (A : Finset Cell) (q : Cell) :
    EdgeConnected (component A q) := by
  refine edgeConnected_of_hub q ?_
  intro c hc
  have hr : Reach A q c := (mem_component.1 hc).2
  clear hc
  induction hr with
  | refl => exact Reach.refl _ q
  | tail hqb hbc ih =>
    exact Reach.trans ih (Reach.step (mem_component.2 ⟨hbc.1, hqb⟩)
      (mem_component.2 ⟨hbc.2.1, Relation.ReflTransGen.tail hqb hbc⟩) hbc.2.2)

/-- A connected subset of `A` that meets a component lies in it. Source:
`report-4.md`, proof of Lemma 56: "T' is connected and does not meet gamma, so it
stays in one component". -/
theorem EdgeConnected.subset_component {A S : Finset Cell} {q : Cell}
    (hS : EdgeConnected S) (hSA : S ⊆ A) (h : Meets S (component A q)) :
    S ⊆ component A q := by
  obtain ⟨m, hmS, hmA⟩ := h
  intro c hc
  exact mem_component.2
    ⟨hSA hc, Reach.trans (mem_component.1 hmA).2 (Reach.mono hSA (hS m hmS c hc))⟩

/-! ## Row and column counts -/

/-- The number of cells of `S` in column `x`: `u[x]` of the reports when `S` is the
tile on row 0 (`report-4.md`, Lemma 24). Integer valued, for use with `omega`. -/
def colCount (S : Finset Cell) (x : ℤ) : ℤ :=
  ((S.filter fun c => c.1 = x).card : ℤ)

/-- The number of cells of `S` in row `y`: `v[y]` of the reports. -/
def rowCount (S : Finset Cell) (y : ℤ) : ℤ :=
  ((S.filter fun c => c.2 = y).card : ℤ)

theorem colCount_nonneg (S : Finset Cell) (x : ℤ) : 0 ≤ colCount S x :=
  Int.natCast_nonneg _

theorem rowCount_nonneg (S : Finset Cell) (y : ℤ) : 0 ≤ rowCount S y :=
  Int.natCast_nonneg _

/-- Counting the cells of `R a b` with a property over a family of pairwise
disjoint sets with union `R a b`. -/
theorem sum_card_filter_of_cover {k : ℕ} {a b : ℤ} (t : Fin k → Finset Cell)
    (hd : ∀ i j, i ≠ j → Disjoint (t i) (t j)) (hc : Finset.univ.biUnion t = R a b)
    (p : Cell → Prop) [DecidablePred p] :
    ∑ i, (((t i).filter p).card : ℤ) = (((R a b).filter p).card : ℤ) := by
  rw [← hc, Finset.filter_biUnion, Finset.card_biUnion, Nat.cast_sum]
  intro i _ j _ hij
  exact Finset.disjoint_filter_filter (hd i j hij)

/-- Counting a row of `R a b` over a family of pairwise disjoint sets with union
`R a b`: the row counts add up to `a`. Source: "Row r of R has a cells" in
`report-4.md`, Lemma 24 and Proposition 61 (2). -/
theorem sum_rowCount_of_cover {k : ℕ} {a b : ℤ} (t : Fin k → Finset Cell)
    (hd : ∀ i j, i ≠ j → Disjoint (t i) (t j)) (hc : Finset.univ.biUnion t = R a b)
    (ha : 0 ≤ a) {y : ℤ} (hy0 : 0 ≤ y) (hyb : y < b) :
    ∑ i, rowCount (t i) y = a := by
  have h := sum_card_filter_of_cover t hd hc fun c => c.2 = y
  have hrow : ((R a b).filter fun c => c.2 = y) = Finset.Ico 0 a ×ˢ ({y} : Finset ℤ) := by
    ext ⟨x, y'⟩
    simp only [Finset.mem_filter, mem_R, Finset.mem_product, Finset.mem_Ico,
      Finset.mem_singleton]
    omega
  rw [hrow, Finset.card_product, Finset.card_singleton, mul_one, Int.card_Ico] at h
  unfold rowCount
  rw [h]
  omega

/-- Counting a column of `R a b`: the column counts add up to `b`. -/
theorem sum_colCount_of_cover {k : ℕ} {a b : ℤ} (t : Fin k → Finset Cell)
    (hd : ∀ i j, i ≠ j → Disjoint (t i) (t j)) (hc : Finset.univ.biUnion t = R a b)
    (hb : 0 ≤ b) {x : ℤ} (hx0 : 0 ≤ x) (hxa : x < a) :
    ∑ i, colCount (t i) x = b := by
  have h := sum_card_filter_of_cover t hd hc fun c => c.1 = x
  have hcol : ((R a b).filter fun c => c.1 = x) = ({x} : Finset ℤ) ×ˢ Finset.Ico 0 b := by
    ext ⟨x', y⟩
    simp only [Finset.mem_filter, mem_R, Finset.mem_product, Finset.mem_Ico,
      Finset.mem_singleton]
    omega
  rw [hcol, Finset.card_product, Finset.card_singleton, one_mul, Int.card_Ico] at h
  unfold colCount
  rw [h]
  omega

end PolyominoOddOrder
