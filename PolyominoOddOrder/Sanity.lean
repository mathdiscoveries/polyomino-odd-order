module

public import PolyominoOddOrder.Main
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases

/-!
# Sanity witnesses and planted mutants for the frozen Spec (`Sanity.lean`)

Named, kernel-checked tests of the definitions in `PolyominoOddOrder/Spec.lean`
(no `sorry`, no `native_decide`; `decide` runs in the kernel):

* non-vacuity witnesses, one per Spec theorem: each has the type
  `∃ b₁ … bₙ, True` over every binder of that theorem, as `ourotrix check-lean`
  binds them;
* for every definition of the trusted surface, at least one affirmative test
  and one negative test (a planted mutant that the definition must reject).

The definitions `RowInterval`, `ColInterval` and `side` are outside the trusted
surface since the third increment (no frozen statement reaches them); their tests
are kept. This file imports the proved library `Main` and not the Spec: the two
declare the same names, so only one of them can be imported. The gate checks
that every definition reached here is the one in the Spec.

For Theorem 21 of `report-3.md` (the search families), the tests cover every
definition of section 1 (the maps `s_t`, placements, solutions, known cells,
proper solutions, the families `I`, `H1`, `H2`), with: Remark 1.1 (a) end to
end on the tiling `t34`; hits of `I(4)` and `H1(4)` from the 4-copy tilings
`t34` and `tiling26`; rectangular proper solutions of `I(5)`, `H1(5)`, `H2(5)`
and `H1(3)`; planted mutants that break one rule of a family each; and the
search hypothesis of Theorem 21 at `n = 3`, proved, which makes its
non-vacuity witness.

For Theorem A18 and Corollary A19 (`report-A2.md`) the tests are the two
non-vacuity witnesses, the equivalence of A18's frozen form with the form that
takes the two conditions as hypotheses, and planted mutants of the statements:
each drops or changes one hypothesis and is false, shown by an explicit
tiling. The frozen statements themselves are not used.

Attribution: AI research agents built and directed by Tyler B. Hughes.
-/

@[expose] public section

namespace PolyominoOddOrder.Sanity

open PolyominoOddOrder

/-! ## Sample cell sets -/

/-- The L-tromino `{(0, 0), (1, 0), (0, 1)}`, tile A of the tiling `tiling26`. -/
def ltromino : Finset Cell := {(0, 0), (1, 0), (0, 1)}

/-- Tile B of `tiling26`: the L-tromino turned by a half turn. -/
def tileB : Finset Cell := {(1, 1), (0, 2), (1, 2)}

/-- Tile C of `tiling26`: the L-tromino moved up 3 rows. -/
def tileC : Finset Cell := {(0, 3), (1, 3), (0, 4)}

/-- Tile D of `tiling26`: tile B moved up 3 rows. -/
def tileD : Finset Cell := {(1, 4), (0, 5), (1, 5)}

/-- The tiling of `R 2 6` by four L-trominoes that `report.md` names after
Theorem 6 (lines 260-261), rows from the bottom AA AB BB CC CD DD (the rows as
`report-2.md` writes them). -/
def tiling26 : Fin 4 → Finset Cell := ![ltromino, tileB, tileC, tileD]

/-- Two cells of one row with a gap: not edge-connected. -/
def gapRow : Finset Cell := {(0, 0), (2, 0)}

/-- Two cells of one column with a gap. -/
def gapCol : Finset Cell := {(0, 0), (0, 2)}

/-- The polyomino `{(1, 0), (0, 1), (1, 1)}` of `report.md`, Corollary 7. -/
def p7 : Finset Cell := {(1, 0), (0, 1), (1, 1)}

/-- Its tiling of `R 3 4` with four distinct corner tiles, rows from the bottom
ABB AAB CDD CCD (`report.md`, Corollary 7). -/
def t34 : Fin 4 → Finset Cell :=
  ![{(0, 0), (0, 1), (1, 1)}, {(1, 0), (2, 0), (2, 1)},
    {(0, 2), (0, 3), (1, 3)}, {(1, 2), (2, 2), (2, 3)}]

/-- The domino `{(0, 0), (1, 0)}`. -/
def domino : Finset Cell := {(0, 0), (1, 0)}

/-- A tiling of `R 2 5` by five dominoes whose four corner cells lie in four
distinct tiles: two vertical dominoes at the bottom, one horizontal, two
vertical at the top. -/
def dom5 : Fin 5 → Finset Cell :=
  ![{(0, 0), (0, 1)}, {(1, 0), (1, 1)}, {(0, 2), (1, 2)},
    {(0, 3), (0, 4)}, {(1, 3), (1, 4)}]

/-! ## Helpers -/

/-- `Adj` is symmetric. -/
theorem adj_symm {c d : Cell} (h : Adj c d) : Adj d c := by
  unfold Adj at *
  omega

/-- One step of the relation behind `EdgeConnected`. -/
theorem edge_step {S : Finset Cell} {x y : Cell} (hx : x ∈ S) (hy : y ∈ S)
    (h : Adj x y) :
    Relation.ReflTransGen (fun u v : Cell => u ∈ S ∧ v ∈ S ∧ Adj u v) x y :=
  Relation.ReflTransGen.single ⟨hx, hy, h⟩

/-- The relation behind `EdgeConnected` is symmetric, since `Adj` is. -/
theorem reach_symm {S : Finset Cell} {x y : Cell}
    (h : Relation.ReflTransGen (fun u v : Cell => u ∈ S ∧ v ∈ S ∧ Adj u v) x y) :
    Relation.ReflTransGen (fun u v : Cell => u ∈ S ∧ v ∈ S ∧ Adj u v) y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, adj_symm hbc.2.2⟩ ih

/-- A set is edge-connected when every cell is reached from one hub cell. -/
theorem edgeConnected_of_hub {S : Finset Cell} (h : Cell)
    (hub : ∀ c ∈ S,
      Relation.ReflTransGen (fun u v : Cell => u ∈ S ∧ v ∈ S ∧ Adj u v) h c) :
    EdgeConnected S := by
  intro c hc d hd
  exact (reach_symm (hub c hc)).trans (hub d hd)

/-- A row given by the image of its cells is an interval. -/
theorem rowInterval_of_image {S : Finset Cell} {y lo hi : ℤ}
    (h : (S.filter fun c => c.2 = y).image Prod.fst = Finset.Icc lo hi) :
    RowInterval S y := by
  intro x₁ x₂ x₃ h12 h23 h1 h3
  have m1 : x₁ ∈ Finset.Icc lo hi :=
    h ▸ Finset.mem_image.2 ⟨(x₁, y), Finset.mem_filter.2 ⟨h1, rfl⟩, rfl⟩
  have m3 : x₃ ∈ Finset.Icc lo hi :=
    h ▸ Finset.mem_image.2 ⟨(x₃, y), Finset.mem_filter.2 ⟨h3, rfl⟩, rfl⟩
  have m2 : x₂ ∈ Finset.Icc lo hi := by
    rw [Finset.mem_Icc] at m1 m3 ⊢
    omega
  rw [← h] at m2
  obtain ⟨c, hc, hcx⟩ := Finset.mem_image.1 m2
  obtain ⟨hcS, hcy⟩ := Finset.mem_filter.1 hc
  have hc' : c = (x₂, y) := Prod.ext hcx hcy
  exact hc' ▸ hcS

/-- A column given by the image of its cells is an interval. -/
theorem colInterval_of_image {S : Finset Cell} {x lo hi : ℤ}
    (h : (S.filter fun c => c.1 = x).image Prod.snd = Finset.Icc lo hi) :
    ColInterval S x := by
  intro y₁ y₂ y₃ h12 h23 h1 h3
  have m1 : y₁ ∈ Finset.Icc lo hi :=
    h ▸ Finset.mem_image.2 ⟨(x, y₁), Finset.mem_filter.2 ⟨h1, rfl⟩, rfl⟩
  have m3 : y₃ ∈ Finset.Icc lo hi :=
    h ▸ Finset.mem_image.2 ⟨(x, y₃), Finset.mem_filter.2 ⟨h3, rfl⟩, rfl⟩
  have m2 : y₂ ∈ Finset.Icc lo hi := by
    rw [Finset.mem_Icc] at m1 m3 ⊢
    omega
  rw [← h] at m2
  obtain ⟨c, hc, hcy⟩ := Finset.mem_image.1 m2
  obtain ⟨hcS, hcx⟩ := Finset.mem_filter.1 hc
  have hc' : c = (x, y₂) := Prod.ext hcx hcy
  exact hc' ▸ hcS

/-- `Meets` is a non-empty intersection, which `decide` can evaluate. -/
theorem meets_iff (S T : Finset Cell) : Meets S T ↔ (S ∩ T).Nonempty := by
  constructor
  · rintro ⟨c, hS, hT⟩
    exact ⟨c, Finset.mem_inter.2 ⟨hS, hT⟩⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, (Finset.mem_inter.1 hc).1, (Finset.mem_inter.1 hc).2⟩

/-! ## `Adj` -/

theorem adj_right : Adj (0, 0) (1, 0) := by
  unfold Adj
  decide

theorem not_adj_diagonal : ¬ Adj (0, 0) (1, 1) := by
  unfold Adj
  decide

theorem not_adj_self : ¬ Adj (0, 0) (0, 0) := by
  unfold Adj
  decide

/-! ## `EdgeConnected` and `IsPolyomino` -/

theorem ltromino_edgeConnected : EdgeConnected ltromino := by
  refine edgeConnected_of_hub (0, 0) ?_
  intro c hc
  simp only [ltromino, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact edge_step (by decide) (by decide) (by unfold Adj; decide)
  · exact edge_step (by decide) (by decide) (by unfold Adj; decide)

theorem ltromino_isPolyomino : IsPolyomino ltromino :=
  ⟨⟨(0, 0), by decide⟩, ltromino_edgeConnected⟩

theorem p7_isPolyomino : IsPolyomino p7 := by
  refine ⟨⟨(1, 1), by decide⟩, edgeConnected_of_hub (1, 1) ?_⟩
  intro c hc
  simp only [p7, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl
  · exact edge_step (by decide) (by decide) (by unfold Adj; decide)
  · exact edge_step (by decide) (by decide) (by unfold Adj; decide)
  · exact Relation.ReflTransGen.refl

theorem domino_isPolyomino : IsPolyomino domino := by
  refine ⟨⟨(0, 0), by decide⟩, edgeConnected_of_hub (0, 0) ?_⟩
  intro c hc
  simp only [domino, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact edge_step (by decide) (by decide) (by unfold Adj; decide)

/-- Mutant: a set with a gap is not edge-connected. -/
theorem gapRow_not_edgeConnected : ¬ EdgeConnected gapRow := by
  intro h
  have key : ∀ d, Relation.ReflTransGen
      (fun u v : Cell => u ∈ gapRow ∧ v ∈ gapRow ∧ Adj u v) (0, 0) d → d = (0, 0) := by
    intro d hd
    induction hd with
    | refl => rfl
    | tail _ hyz ih =>
      subst ih
      obtain ⟨-, hz, hadj⟩ := hyz
      simp only [gapRow, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · rfl
      · exact absurd hadj (by unfold Adj; decide)
  exact absurd (key _ (h (0, 0) (by decide) (2, 0) (by decide))) (by decide)

/-- Mutant: a disconnected set is not a polyomino. -/
theorem gapRow_not_isPolyomino : ¬ IsPolyomino gapRow :=
  fun h => gapRow_not_edgeConnected h.2

/-- Mutant: the empty set is not a polyomino. -/
theorem empty_not_isPolyomino : ¬ IsPolyomino ∅ :=
  fun h => Finset.not_nonempty_empty h.1

/-! ## `GridIso.apply` and `Congruent` -/

/-- The 8 settings of the three switches send the sample cell `(1, 2)` to its 8
images under the symmetries of the square. -/
theorem gridIso_eight_symmetries :
    (Finset.univ : Finset (Bool × Bool × Bool)).image
        (fun s => (GridIso.mk s.1 s.2.1 s.2.2 (0, 0)).apply (1, 2)) =
      {(1, 2), (-1, 2), (1, -2), (-1, -2), (2, 1), (-2, 1), (2, -1), (-2, -1)} := by
  decide

theorem gridIso_eight_distinct :
    ((Finset.univ : Finset (Bool × Bool × Bool)).image
        (fun s => (GridIso.mk s.1 s.2.1 s.2.2 (0, 0)).apply (1, 2))).card = 8 := by
  decide

theorem gridIso_apply_sample :
    (GridIso.mk true false true (3, 4)).apply (1, 2) = (5, 3) := by
  decide

/-- Mutant: the identity setting does not exchange the coordinates. -/
theorem gridIso_identity_not_swap :
    (GridIso.mk false false false (0, 0)).apply (1, 2) ≠ (2, 1) := by
  decide

theorem congruent_ltromino_tileB : Congruent ltromino tileB :=
  ⟨⟨false, true, true, (1, 2)⟩, by decide⟩

/-- Reflections are included: the S-tetromino is congruent to its mirror
image, the Z-tetromino. -/
theorem congruent_mirror :
    Congruent ({(1, 0), (2, 0), (0, 1), (1, 1)} : Finset Cell)
      {(0, 0), (1, 0), (1, 1), (2, 1)} :=
  ⟨⟨false, true, false, (2, 0)⟩, by decide⟩

/-- Mutant: a monomino is not congruent to a domino. -/
theorem not_congruent_monomino_domino :
    ¬ Congruent ({(0, 0)} : Finset Cell) domino := by
  rintro ⟨g, h⟩
  have hcard := congrArg Finset.card h
  rw [Finset.image_singleton, Finset.card_singleton] at hcard
  exact absurd hcard (by decide)

/-! ## `R`, the box and rectangularity -/

theorem mem_R_sample : (1, 5) ∈ R 2 6 := by
  decide

theorem not_mem_R_sample : (2, 0) ∉ R 2 6 := by
  decide

theorem R_card : (R 2 6).card = 12 := by
  decide

theorem xSpan_ltromino : xSpan ltromino = {0, 1} := by
  decide

theorem not_mem_xSpan : (2 : ℤ) ∉ xSpan ltromino := by
  decide

theorem ySpan_ltromino : ySpan ltromino = {0, 1} := by
  decide

theorem not_mem_ySpan : (-1 : ℤ) ∉ ySpan ltromino := by
  decide

theorem boundingBox_ltromino : boundingBox ltromino = R 2 2 := by
  decide

/-- Mutant: the box of the L-tromino is not the L-tromino. -/
theorem boundingBox_ltromino_ne : boundingBox ltromino ≠ ltromino := by
  decide

theorem R_isRectangular : IsRectangular (R 2 3) := by
  unfold IsRectangular
  decide

theorem domino_isRectangular : IsRectangular domino := by
  unfold IsRectangular
  decide

/-- Mutant: the L-tromino is not rectangular. -/
theorem ltromino_not_isRectangular : ¬ IsRectangular ltromino := by
  unfold IsRectangular
  decide

theorem p7_not_isRectangular : ¬ IsRectangular p7 := by
  unfold IsRectangular
  decide

/-! ## Sides and corners -/

theorem bottomRow_sample : bottomRow 2 6 = {(0, 0), (1, 0)} := by
  decide

theorem not_mem_bottomRow : (0, 1) ∉ bottomRow 2 6 := by
  decide

theorem topRow_sample : topRow 2 6 = {(0, 5), (1, 5)} := by
  decide

theorem not_mem_topRow : (0, 4) ∉ topRow 2 6 := by
  decide

theorem leftCol_sample : leftCol 3 2 = {(0, 0), (0, 1)} := by
  decide

theorem not_mem_leftCol : (1, 0) ∉ leftCol 3 2 := by
  decide

theorem rightCol_sample : rightCol 3 2 = {(2, 0), (2, 1)} := by
  decide

theorem not_mem_rightCol : (1, 1) ∉ rightCol 3 2 := by
  decide

theorem side_sample : side 3 2 1 = {(2, 0), (2, 1)} := by
  decide

/-- Mutant: the bottom and the top side of `R 2 6` differ. -/
theorem side_bottom_ne_top : side 2 6 0 ≠ side 2 6 2 := by
  decide

theorem corner_sample : corner 2 6 2 = (1, 5) := by
  decide

/-- Mutant: the first two corners of `R 2 6` are different cells. -/
theorem corner_ne : corner 2 6 0 ≠ corner 2 6 1 := by
  decide

/-- In a rectangle one column wide two corner labels name one cell. -/
theorem corner_thin : corner 1 6 0 = corner 1 6 1 := by
  decide

/-! ## `Meets`, `RowInterval`, `ColInterval` -/

theorem meets_bottom : Meets ltromino (bottomRow 2 6) := by
  rw [meets_iff]
  decide

/-- Mutant: the L-tromino at the bottom of `R 2 6` does not meet the top row. -/
theorem not_meets_top : ¬ Meets ltromino (topRow 2 6) := by
  rw [meets_iff]
  decide

theorem ltromino_rowInterval : RowInterval ltromino 0 :=
  rowInterval_of_image (lo := 0) (hi := 1) (by decide)

/-- Mutant: a row with a gap is not an interval. -/
theorem gapRow_not_rowInterval : ¬ RowInterval gapRow 0 := by
  intro h
  exact absurd (h 0 1 2 (by decide) (by decide) (by decide) (by decide)) (by decide)

theorem ltromino_colInterval : ColInterval ltromino 0 :=
  colInterval_of_image (lo := 0) (hi := 1) (by decide)

/-- Mutant: a column with a gap is not an interval. -/
theorem gapCol_not_colInterval : ¬ ColInterval gapCol 0 := by
  intro h
  exact absurd (h 0 1 2 (by decide) (by decide) (by decide) (by decide)) (by decide)

/-! ## Tilings and case (I) -/

/-- The tiling of `R 2 6` by four L-trominoes is a 4-copy tiling. -/
theorem tiling26_isTiling : IsTiling ltromino 2 6 tiling26 where
  congruent := by
    intro i
    fin_cases i
    · exact ⟨⟨false, false, false, (0, 0)⟩, by decide⟩
    · exact ⟨⟨false, true, true, (1, 2)⟩, by decide⟩
    · exact ⟨⟨false, false, false, (0, 3)⟩, by decide⟩
    · exact ⟨⟨false, true, true, (1, 5)⟩, by decide⟩
  disjoint := by decide
  cover := by decide

/-- Mutant: two overlapping copies are not a tiling. -/
theorem overlap_not_isTiling :
    ¬ IsTiling ltromino 2 6 ![ltromino, ltromino, tileC, tileD] := by
  intro h
  exact absurd (h.disjoint 0 1 (by decide)) (by decide)

/-- Mutant: the four tiles of `tiling26` do not tile a taller rectangle. -/
theorem short_cover_not_isTiling : ¬ IsTiling ltromino 2 7 tiling26 := by
  intro h
  exact absurd h.cover (by decide)

/-- Mutant: in `tiling26` the tile A holds the corners `(0, 0)` and `(1, 0)`, so
the corners are not in four distinct tiles. -/
theorem tiling26_not_cornersInDistinctTiles : ¬ CornersInDistinctTiles 2 6 tiling26 := by
  intro h
  exact absurd (h 0 0 1 (by decide) (by decide)) (by decide)

theorem t34_isTiling : IsTiling p7 3 4 t34 where
  congruent := by
    intro i
    fin_cases i
    · exact ⟨⟨false, true, false, (1, 0)⟩, by decide⟩
    · exact ⟨⟨false, false, true, (1, 1)⟩, by decide⟩
    · exact ⟨⟨false, true, false, (1, 2)⟩, by decide⟩
    · exact ⟨⟨false, false, true, (1, 3)⟩, by decide⟩
  disjoint := by decide
  cover := by decide

/-- Case (I) with a non-rectangular polyomino, at 4 copies. -/
theorem t34_cornersInDistinctTiles : CornersInDistinctTiles 3 4 t34 := by
  unfold CornersInDistinctTiles
  decide

theorem dom5_isTiling : IsTiling domino 2 5 dom5 where
  congruent := by
    intro i
    fin_cases i
    · exact ⟨⟨true, false, false, (0, 0)⟩, by decide⟩
    · exact ⟨⟨true, false, false, (1, 0)⟩, by decide⟩
    · exact ⟨⟨false, false, false, (0, 2)⟩, by decide⟩
    · exact ⟨⟨true, false, false, (0, 3)⟩, by decide⟩
    · exact ⟨⟨true, false, false, (1, 3)⟩, by decide⟩
  disjoint := by decide
  cover := by decide

/-- Case (I) at 5 copies, with a rectangular polyomino. -/
theorem dom5_cornersInDistinctTiles : CornersInDistinctTiles 2 5 dom5 := by
  unfold CornersInDistinctTiles
  decide

/-! ## Rectangles are edge-connected -/

/-- Along row 0 of `R p q`, from `(0, 0)` to `(x, 0)`. -/
theorem reach_row_R {p q : ℤ} (hq : 0 < q) :
    ∀ x : ℕ, (x : ℤ) < p →
      Relation.ReflTransGen (fun u v : Cell => u ∈ R p q ∧ v ∈ R p q ∧ Adj u v)
        (0, 0) ((x : ℤ), 0)
  | 0, _ => by
    rw [Nat.cast_zero]
  | x + 1, hx => by
    refine (reach_row_R hq x (by omega)).tail ⟨?_, ?_, ?_⟩
    · simp only [R, Finset.mem_product, Finset.mem_Ico]
      omega
    · simp only [R, Finset.mem_product, Finset.mem_Ico]
      omega
    · unfold Adj
      omega

/-- Up column `x` of `R p q`, from `(x, 0)` to `(x, y)`. -/
theorem reach_col_R {p q x : ℤ} (hx0 : 0 ≤ x) (hxp : x < p) :
    ∀ y : ℕ, (y : ℤ) < q →
      Relation.ReflTransGen (fun u v : Cell => u ∈ R p q ∧ v ∈ R p q ∧ Adj u v)
        (x, 0) (x, (y : ℤ))
  | 0, _ => by
    rw [Nat.cast_zero]
  | y + 1, hy => by
    refine (reach_col_R hx0 hxp y (by omega)).tail ⟨?_, ?_, ?_⟩
    · simp only [R, Finset.mem_product, Finset.mem_Ico]
      omega
    · simp only [R, Finset.mem_product, Finset.mem_Ico]
      omega
    · unfold Adj
      omega

/-- Every rectangle `R p q` is edge-connected. -/
theorem R_edgeConnected (p q : ℤ) : EdgeConnected (R p q) := by
  refine edgeConnected_of_hub (0, 0) ?_
  rintro ⟨x, y⟩ hc
  simp only [R, Finset.mem_product, Finset.mem_Ico] at hc
  obtain ⟨⟨hx0, hxp⟩, hy0, hyq⟩ := hc
  have hrow := reach_row_R (p := p) (by omega : 0 < q) x.toNat (by omega)
  have hcol := reach_col_R (q := q) hx0 hxp y.toNat (by omega)
  rw [Int.toNat_of_nonneg hx0] at hrow
  rw [Int.toNat_of_nonneg hy0] at hcol
  exact hrow.trans hcol

/-! ## Placements and the maps `s_t` (`report-3.md`, section 1) -/

/-- A sample numbering of placements, injective on placements with
`0 ≤ x < 16` and `0 ≤ y`: enough to order the free entries of the sample
tuples below. -/
def numS (p : Placement) : ℕ :=
  (p.t : ℕ) + 8 * (p.x.toNat + 16 * p.y.toNat)

/-- `Placement` is in bijection with `Fin 8 × ℤ × ℤ`. -/
def placementEquiv : Placement ≃ Fin 8 × ℤ × ℤ where
  toFun p := (p.t, p.x, p.y)
  invFun q := ⟨q.1, q.2.1, q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- An injective numbering of all placements. -/
def placementNum (p : Placement) : ℕ :=
  Encodable.encode (placementEquiv p)

theorem placementNum_injective : Function.Injective (placementNum : Placement → ℕ) :=
  Encodable.encode_injective.comp placementEquiv.injective

/-- The images of the cell `(0, 0)` under `s_0, ..., s_7` for the box `R 2 3`. -/
theorem boxSymm_origin_images :
    ∀ t : Fin 8, boxSymm 2 3 t (0, 0) =
      ![(0, 0), (1, 0), (0, 2), (1, 2), (0, 0), (2, 0), (0, 1), (2, 1)] t := by
  decide

/-- `s_t` maps `B = R 2 3` onto `R 2 3` for `t ≤ 3` and onto `R 3 2` for
`t ≥ 4` (`report-3.md`: "s_t(B) is R(w, h) for t <= 3 and R(h, w) for t >= 4"). -/
theorem boxSymm_image_box :
    ∀ t : Fin 8, (R 2 3).image (boxSymm 2 3 t) = if (t : ℕ) ≤ 3 then R 2 3 else R 3 2 := by
  decide

/-- Mutant: `s_1` is not the identity. -/
theorem boxSymm_one_ne_id : boxSymm 2 3 1 (0, 0) ≠ (0, 0) := by
  decide

/-- Mutant: `s_5` and `s_6` differ (they are the two quarter turns). -/
theorem boxSymm_five_ne_six : boxSymm 2 3 5 (0, 0) ≠ boxSymm 2 3 6 (0, 0) := by
  decide

/-- Each `s_t` is a grid isometry, for every box: it is `GridIso.apply` of an
explicit `GridIso`. -/
theorem boxSymm_isGridIso (w h : ℤ) (t : Fin 8) :
    ∃ g : GridIso, ∀ c, boxSymm w h t c = g.apply c := by
  fin_cases t
  · exact ⟨⟨false, false, false, (0, 0)⟩, fun c => by
      simp [boxSymm, GridIso.apply]⟩
  · exact ⟨⟨false, true, false, (w - 1, 0)⟩, fun c => by
      simp [boxSymm, GridIso.apply]; ring⟩
  · exact ⟨⟨false, false, true, (0, h - 1)⟩, fun c => by
      simp [boxSymm, GridIso.apply]; ring⟩
  · exact ⟨⟨false, true, true, (w - 1, h - 1)⟩, fun c => by
      simp [boxSymm, GridIso.apply]; constructor <;> ring⟩
  · exact ⟨⟨true, false, false, (0, 0)⟩, fun c => by
      simp [boxSymm, GridIso.apply]⟩
  · exact ⟨⟨true, true, false, (h - 1, 0)⟩, fun c => by
      simp [boxSymm, GridIso.apply]; ring⟩
  · exact ⟨⟨true, false, true, (0, w - 1)⟩, fun c => by
      simp [boxSymm, GridIso.apply]; ring⟩
  · exact ⟨⟨true, true, true, (h - 1, w - 1)⟩, fun c => by
      simp [boxSymm, GridIso.apply]; constructor <;> ring⟩

theorem placement_apply_sample : (⟨5, 1, 2⟩ : Placement).apply 2 3 (1, 0) = (3, 3) := by
  decide

/-- Mutant: the quarter turn `s_5` and the reflection `s_1` place the cell
`(1, 0)` differently. -/
theorem placement_apply_ne :
    (⟨5, 1, 2⟩ : Placement).apply 2 3 (1, 0) ≠ (⟨1, 1, 2⟩ : Placement).apply 2 3 (1, 0) := by
  decide

theorem isPlacement_sample : IsPlacement 3 5 2 2 ⟨0, 1, 3⟩ := by
  unfold IsPlacement
  decide

/-- A vertical placement of the box `R 3 4` occupies `R 4 3` shifted. -/
theorem isPlacement_vertical_sample : IsPlacement 4 10 3 4 ⟨4, 0, 4⟩ := by
  unfold IsPlacement
  decide

/-- Mutant: the image of the box leaves the rectangle on the right. -/
theorem not_isPlacement_right : ¬ IsPlacement 3 5 2 2 ⟨0, 2, 0⟩ := by
  unfold IsPlacement
  decide

/-- Mutant: the transposed box of a vertical placement leaves the rectangle. -/
theorem not_isPlacement_vertical : ¬ IsPlacement 4 10 3 4 ⟨4, 1, 4⟩ := by
  unfold IsPlacement
  decide

theorem isVertical_sample : (⟨4, 0, 0⟩ : Placement).IsVertical := by
  unfold Placement.IsVertical
  decide

/-- Mutant: `s_3` (the half turn) is not vertical. -/
theorem not_isVertical_three : ¬ (⟨3, 0, 0⟩ : Placement).IsVertical := by
  unfold Placement.IsVertical
  decide

theorem preimage_sample : (⟨3, 1, 0⟩ : Placement).preimage 2 2 (2, 0) = {(0, 1)} := by
  decide

/-- Mutant: `(0, 0)` is not sent to `(2, 0)` by the placement `(3, 1, 0)`. -/
theorem not_mem_preimage : (0, 0) ∉ (⟨3, 1, 0⟩ : Placement).preimage 2 2 (2, 0) := by
  decide

/-! ## Remark 1.1 (a) on a concrete tiling, and a hit of `I(4)`

`t34` is the tiling of `R 3 4` by four copies of `p7` (`report.md`,
Corollary 7). `box(p7) = R 2 2` has lower-left cell `(0, 0)`. -/

/-- The isometries `f_i` of `t34_isTiling`. -/
def isos34 : Fin 4 → GridIso :=
  ![⟨false, true, false, (1, 0)⟩, ⟨false, false, true, (1, 1)⟩,
    ⟨false, true, false, (1, 2)⟩, ⟨false, false, true, (1, 3)⟩]

/-- The tuple Remark 1.1 (a) assigns to `t34`: `s_{t_i}` has the linear part of
`f_i` and `(x_i, y_i)` is the lower-left cell of `box(T_i)`. -/
def g34 : Fin 4 → Placement :=
  ![⟨1, 0, 0⟩, ⟨2, 1, 0⟩, ⟨1, 0, 2⟩, ⟨2, 1, 2⟩]

/-- Remark 1.1 (a), end to end on `t34`: `box(p7) = R 2 2`; on `B` each `f_i`
equals the placement `g_i`; `f_i(B) = box(T_i)` lies in `R 3 4`; `T_i = g_i(p7)`;
and `p7` is a solution of the tuple. -/
theorem remark11a_t34 :
    boundingBox p7 = R 2 2 ∧
      (∀ i, ∀ c ∈ R 2 2, (g34 i).apply 2 2 c = (isos34 i).apply c) ∧
      (∀ i, (R 2 2).image ((g34 i).apply 2 2) = boundingBox (t34 i)) ∧
      (∀ i, IsPlacement 3 4 2 2 (g34 i)) ∧
      (∀ i, p7.image ((g34 i).apply 2 2) = t34 i) ∧
      IsSolution 3 4 2 2 g34 p7 := by
  refine ⟨by decide, by decide, by decide, ?_, by decide, ⟨by decide, by decide, by decide⟩⟩
  unfold IsPlacement
  decide

/-- Mutant: moving the last placement one column left breaks the partition. -/
theorem not_isSolution_shifted :
    ¬ IsSolution 3 4 2 2 ![⟨1, 0, 0⟩, ⟨2, 1, 0⟩, ⟨1, 0, 2⟩, ⟨2, 0, 2⟩] p7 := by
  intro h
  exact absurd h.cover (by decide)

/-- The tile of `t34` on the corner `(0, 0)`. -/
def tile34 : Finset Cell := {(0, 0), (0, 1), (1, 1)}

/-- Lemma 15 (a) on `t34`: with `P` replaced by the corner tile, the tuple of
`I(4)` (`g_2`, `g_3`, `g_4` on the corners `(2, 0)`, `(2, 3)`, `(0, 3)`). -/
def g34I : Fin 4 → Placement :=
  ![⟨0, 0, 0⟩, ⟨3, 1, 0⟩, ⟨3, 1, 2⟩, ⟨0, 0, 2⟩]

theorem tile34_edgeConnected : EdgeConnected tile34 := by
  refine edgeConnected_of_hub (0, 1) ?_
  intro c hc
  simp only [tile34, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl
  · exact edge_step (by decide) (by decide) (by unfold Adj; decide)
  · exact Relation.ReflTransGen.refl
  · exact edge_step (by decide) (by decide) (by unfold Adj; decide)

theorem familyI_t34 : FamilyI 4 numS 3 3 4 2 2 g34I := by
  unfold FamilyI IsPlacement
  decide

theorem knownI_t34 : knownI 3 4 2 2 g34I = {(0, 0), (0, 1)} := by
  decide

/-- Mutant: `(1, 1)` is not a known cell of this tuple. -/
theorem not_mem_knownI_t34 : (1, 1) ∉ knownI 3 4 2 2 g34I := by
  decide

theorem preimageAt_t34 : preimageAt 2 2 g34I 1 (corner 3 4 1) = {(0, 1)} := by
  decide

/-- Mutant: the entry of Lean index 2 does not send `(0, 1)` to `(2, 0)`. -/
theorem not_mem_preimageAt_t34 : (0, 1) ∉ preimageAt 2 2 g34I 2 (corner 3 4 1) := by
  decide

/-- The corner tile of `t34` is a proper solution of a tuple of `I(4)` that is
not a rectangle: the families find the 4-copy tiling `t34`. -/
theorem properI_t34 :
    IsProperSolution 3 4 2 2 g34I (knownI 3 4 2 2 g34I) tile34 ∧ ¬ IsRectangular tile34 := by
  refine ⟨⟨⟨by decide, by decide, by decide⟩, tile34_edgeConnected, by decide⟩, ?_⟩
  unfold IsRectangular
  decide

/-- Mutant: a solution that misses a known cell is not proper. -/
theorem not_properI_missing_known :
    ¬ IsProperSolution 3 4 2 2 g34I {(1, 0)} tile34 := by
  rintro ⟨-, -, hK⟩
  exact absurd (hK (Finset.mem_singleton_self (1, 0))) (by decide)

/-! ## The families `I`, `H1`, `H2`: sample tuples and planted mutants -/

-- The family predicates are long conjunctions; their `Decidable` instances
-- exceed the default size bound of instance synthesis.
set_option synthInstance.maxSize 4096

/-- The origin placement `(0, 0, 0)`. -/
def o : Placement := ⟨0, 0, 0⟩

/-- A tuple of `I(5)` at `n = 3` on `R 3 5` with the box `R 2 2`. -/
def gI5 : Fin 5 → Placement := ![o, ⟨0, 1, 0⟩, ⟨0, 1, 3⟩, ⟨0, 0, 3⟩, ⟨0, 0, 1⟩]

theorem familyI_gI5 : FamilyI 5 numS 3 3 5 2 2 gI5 := by
  unfold FamilyI IsPlacement
  decide

/-- Mutant: `g_1` is not `(0, 0, 0)`. -/
theorem not_familyI_g1 :
    ¬ FamilyI 5 numS 3 3 5 2 2 ![⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 1, 3⟩, ⟨0, 0, 3⟩, ⟨0, 0, 1⟩] := by
  unfold FamilyI IsPlacement
  decide

/-- Mutant: the image of the box under `g_2` misses the corner `(2, 0)`. -/
theorem not_familyI_corner :
    ¬ FamilyI 5 numS 3 3 5 2 2 ![o, ⟨0, 0, 1⟩, ⟨0, 1, 3⟩, ⟨0, 0, 3⟩, ⟨0, 0, 1⟩] := by
  unfold FamilyI IsPlacement
  decide

/-- Mutant: the box `R 3 1` has `w h = n` (the box of a rectangle). -/
theorem not_familyI_box :
    ¬ FamilyI 5 numS 3 3 5 3 1 ![o, o, ⟨0, 0, 4⟩, ⟨0, 0, 4⟩, ⟨0, 0, 2⟩] := by
  unfold FamilyI IsPlacement
  decide

/-- Mutant: `g_5` is not a placement (its box leaves the rectangle). -/
theorem not_familyI_outside :
    ¬ FamilyI 5 numS 3 3 5 2 2 ![o, ⟨0, 1, 0⟩, ⟨0, 1, 3⟩, ⟨0, 0, 3⟩, ⟨0, 2, 0⟩] := by
  unfold FamilyI IsPlacement
  decide

/-- Mutant: the rectangle `R 5 3` has `a > b`. -/
theorem not_familyI_transposed :
    ¬ FamilyI 5 numS 3 5 3 2 2 ![o, ⟨0, 3, 0⟩, ⟨0, 3, 1⟩, ⟨0, 0, 1⟩, ⟨0, 1, 0⟩] := by
  unfold FamilyI IsPlacement
  decide

/-- Mutant: `I(k)` needs `k ≥ 4`; this 3-tuple meets every other rule. -/
theorem not_familyI_three :
    ¬ FamilyI 3 numS 3 3 3 2 2 ![o, ⟨0, 1, 0⟩, ⟨0, 1, 1⟩] := by
  unfold FamilyI IsPlacement
  decide

/-- Lemma 15 (b) on `tiling26` (four L-trominoes on `R 2 6`): the tile on row 0
with every other tile vertical, a tuple of `H1(4)`. -/
def g26 : Fin 4 → Placement := ![o, ⟨7, 0, 4⟩, ⟨7, 0, 1⟩, ⟨4, 0, 3⟩]

theorem familyH1_g26 : FamilyH1 4 numS 3 2 6 2 2 g26 := by
  unfold FamilyH1 IsPlacement Placement.IsVertical
  decide

theorem knownH1_g26 : knownH1 2 6 2 2 g26 = {(0, 0), (1, 0), (0, 1)} := by
  decide

/-- Mutant: `(1, 1)` is not a known cell of this tuple. -/
theorem not_mem_knownH1_g26 : (1, 1) ∉ knownH1 2 6 2 2 g26 := by
  decide

/-- The L-tromino is a proper solution of this tuple of `H1(4)` that is not a
rectangle: the families find the 4-copy tiling `tiling26`. -/
theorem properH1_g26 :
    IsProperSolution 2 6 2 2 g26 (knownH1 2 6 2 2 g26) ltromino ∧ ¬ IsRectangular ltromino :=
  ⟨⟨⟨by decide, by decide, by decide⟩, ltromino_edgeConnected, by decide⟩,
    ltromino_not_isRectangular⟩

/-- Mutant: the remaining placements are not in increasing order. -/
theorem not_familyH1_order : ¬ FamilyH1 4 numS 3 2 6 2 2 ![o, ⟨7, 0, 4⟩, ⟨4, 0, 3⟩, ⟨7, 0, 1⟩] := by
  unfold FamilyH1 IsPlacement Placement.IsVertical
  decide

/-- Mutant: an entry after `g_1` is not vertical. -/
theorem not_familyH1_vertical :
    ¬ FamilyH1 4 numS 3 2 6 2 2 ![o, ⟨7, 0, 4⟩, ⟨7, 0, 1⟩, ⟨0, 0, 3⟩] := by
  unfold FamilyH1 IsPlacement Placement.IsVertical
  decide

/-- Mutant: `g_2` is not at `(0, b - a)`. -/
theorem not_familyH1_g2 :
    ¬ FamilyH1 4 numS 3 2 6 2 2 ![o, ⟨7, 0, 3⟩, ⟨7, 0, 1⟩, ⟨4, 0, 4⟩] := by
  unfold FamilyH1 IsPlacement Placement.IsVertical
  decide

/-- A tuple of `H1(3)` with `d < a`: `R 4 6`, box `R 4 3`, `n = 8`. -/
def gH13 : Fin 3 → Placement := ![o, ⟨4, 0, 2⟩, ⟨5, 1, 2⟩]

theorem familyH1_gH13 : FamilyH1 3 numS 8 4 6 4 3 gH13 := by
  unfold FamilyH1 IsPlacement Placement.IsVertical
  decide

/-- Mutant: with `d < a`, `g_3` must be at `(a - d, b - a)`. -/
theorem not_familyH1_g3 : ¬ FamilyH1 3 numS 8 4 6 4 3 ![o, ⟨4, 0, 2⟩, ⟨5, 0, 2⟩] := by
  unfold FamilyH1 IsPlacement Placement.IsVertical
  decide

/-- A tuple of `H2(3)`: `R 4 6`, box `R 4 3`, `n = 8`. -/
def gH23 : Fin 3 → Placement := ![o, ⟨2, 0, 3⟩, ⟨4, 0, 1⟩]

theorem familyH2_gH23 : FamilyH2 3 numS 8 4 6 4 3 gH23 := by
  unfold FamilyH2 IsPlacement Placement.IsVertical
  decide

/-- Mutant: `g_2` must use `s_2` or `s_3`. -/
theorem not_familyH2_t : ¬ FamilyH2 3 numS 8 4 6 4 3 ![o, ⟨0, 0, 3⟩, ⟨4, 0, 1⟩] := by
  unfold FamilyH2 IsPlacement Placement.IsVertical
  decide

/-- Mutant: a vertical entry must meet neither row 0 nor row `b - 1`
(`y ≤ b - a - 1`). -/
theorem not_familyH2_y : ¬ FamilyH2 3 numS 8 4 6 4 3 ![o, ⟨2, 0, 3⟩, ⟨4, 0, 2⟩] := by
  unfold FamilyH2 IsPlacement Placement.IsVertical
  decide

theorem knownH2_sample : knownH2 4 3 = {(0, 0), (1, 0), (2, 0), (3, 0)} := by
  decide

/-- Mutant: `(0, 1)` is not a known cell of `H2`. -/
theorem not_mem_knownH2 : (0, 1) ∉ knownH2 4 3 := by
  decide

/-! ## Rectangular proper solutions in the families of Theorem 21

Each family used by Theorem 21 except `H2(3)` has a proper solution at some `n`:
here a rectangle (a solution the search prints as `RECT`, not a hit). `H2(3)` has
none: three rectangles cannot fill its middle. -/

/-- `I(5)`: five copies of `R 2 4` tile `R 4 10` (two at the bottom corners, one
across the middle, two at the top corners), box `R 3 4`, `n = 8`. -/
def gI5r : Fin 5 → Placement := ![o, ⟨1, 1, 0⟩, ⟨3, 1, 6⟩, ⟨0, 0, 6⟩, ⟨4, 0, 4⟩]

/-- `H1(5)`: `R 4 2` at the bottom of `R 4 10` and four vertical copies above,
box `R 4 3`, `n = 8`. -/
def gH1r : Fin 5 → Placement := ![o, ⟨4, 0, 6⟩, ⟨5, 1, 6⟩, ⟨4, 0, 2⟩, ⟨5, 1, 2⟩]

/-- `H2(5)`: `R 6 2` at the bottom and the top of `R 6 10` and three vertical
copies between, box `R 6 3`, `n = 12`. -/
def gH2r : Fin 5 → Placement := ![o, ⟨2, 0, 7⟩, ⟨4, 0, 2⟩, ⟨4, 2, 2⟩, ⟨5, 3, 2⟩]

theorem searchSolution_I5 : IsSearchSolution numS 8 4 10 3 4 (R 2 4) := by
  refine Or.inl ⟨gI5r, ?_, ⟨by decide, by decide +kernel, by decide +kernel⟩, R_edgeConnected 2 4, by decide⟩
  unfold FamilyI IsPlacement
  decide

theorem searchSolution_H1_5 : IsSearchSolution numS 8 4 10 4 3 (R 4 2) := by
  refine Or.inr (Or.inl ⟨gH1r, ?_, ⟨by decide, by decide +kernel, by decide +kernel⟩, R_edgeConnected 4 2,
    by decide⟩)
  unfold FamilyH1 IsPlacement Placement.IsVertical
  decide

theorem searchSolution_H2_5 : IsSearchSolution numS 12 6 10 6 3 (R 6 2) := by
  refine Or.inr (Or.inr (Or.inl ⟨gH2r, ?_, ⟨by decide, by decide +kernel, by decide +kernel⟩,
    R_edgeConnected 6 2, by decide⟩))
  unfold FamilyH2 IsPlacement Placement.IsVertical
  decide

theorem searchSolution_H1_3 : IsSearchSolution numS 8 4 6 4 3 (R 4 2) := by
  refine Or.inr (Or.inr (Or.inr (Or.inl ⟨gH13, familyH1_gH13, ⟨by decide, by decide +kernel, by decide +kernel⟩,
    R_edgeConnected 4 2, by decide⟩)))

/-! ## The search hypothesis of Theorem 21 at `n = 3`

At `n = 3` the only family with a box is `I(5)` on `R 3 5` with the box
`R 2 2`, and no tuple of it has a solution: the cells `(0, 2)` and `(2, 2)` lie
in none of the boxes of `g_1`, ..., `g_4`, and the box of `g_5` is too narrow to
hold both. So the hypothesis of Theorem 21 holds at `n = 3`, for every
numbering. -/

/-- `s_t` maps `R 2 2` into itself. -/
theorem boxSymm_R22 : ∀ t : Fin 8, ∀ u ∈ R 2 2, boxSymm 2 2 t u ∈ R 2 2 := by
  decide

/-- A placement of the box `R 2 2` sends the box into `[x, x + 1] × [y, y + 1]`. -/
theorem apply22_bounds (p : Placement) (u : Cell) (hu : u ∈ R 2 2) :
    p.x ≤ (p.apply 2 2 u).1 ∧ (p.apply 2 2 u).1 ≤ p.x + 1 ∧
      p.y ≤ (p.apply 2 2 u).2 ∧ (p.apply 2 2 u).2 ≤ p.y + 1 := by
  have h := boxSymm_R22 p.t u hu
  simp only [R, Finset.mem_product, Finset.mem_Ico] at h
  simp only [Placement.apply]
  omega

/-- The cell `c` of `R 3 5` is the image of a cell of `B = R 2 2` under some
entry of a solution's tuple. -/
theorem cover_cell {g : Fin 5 → Placement} {X : Finset Cell}
    (hS : IsSolution 3 5 2 2 g X) (c : Cell) (hc : c ∈ R 3 5) :
    ∃ i, ∃ u ∈ R 2 2, (g i).apply 2 2 u = c := by
  rw [← hS.cover] at hc
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hc
  obtain ⟨u, hu, he⟩ := Finset.mem_image.1 hi
  exact ⟨i, u, hS.sub hu, he⟩

/-- No tuple of `I(5)` on `R 3 5` with the box `R 2 2` has a solution. -/
theorem no_solution_I5_R35 (num : Placement → ℕ) (g : Fin 5 → Placement) (X : Finset Cell)
    (hF : FamilyI 5 num 3 3 5 2 2 g) (hS : IsSolution 3 5 2 2 g X) : False := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h0, h1, h2, h3, -⟩ := hF
  -- the corner conditions bound the boxes of g_2, g_3, g_4
  have k1 : ∀ i : Fin 5, (i : ℕ) = 1 → 1 ≤ (g i).x ∧ (g i).y ≤ 0 := by
    intro i hi
    obtain ⟨v, hv, e⟩ := Finset.mem_image.1 (h1 i hi)
    have b := apply22_bounds (g i) v hv
    rw [e] at b
    simp only [corner] at b
    norm_num at b
    omega
  have k2 : ∀ i : Fin 5, (i : ℕ) = 2 → 3 ≤ (g i).y := by
    intro i hi
    obtain ⟨v, hv, e⟩ := Finset.mem_image.1 (h2 i hi)
    have b := apply22_bounds (g i) v hv
    rw [e] at b
    simp only [corner] at b
    norm_num at b
    omega
  have k3 : ∀ i : Fin 5, (i : ℕ) = 3 → 3 ≤ (g i).y := by
    intro i hi
    obtain ⟨v, hv, e⟩ := Finset.mem_image.1 (h3 i hi)
    have b := apply22_bounds (g i) v hv
    rw [e] at b
    simp only [corner] at b
    norm_num at b
    omega
  have k0 : ∀ i : Fin 5, (i : ℕ) = 0 → (g i).x = 0 ∧ (g i).y = 0 := by
    intro i hi
    rw [h0 i hi]
    exact ⟨rfl, rfl⟩
  obtain ⟨i, u, hu, eu⟩ := cover_cell hS (0, 2) (by decide)
  obtain ⟨i', u', hu', eu'⟩ := cover_cell hS (2, 2) (by decide)
  have bu := apply22_bounds (g i) u hu
  have bu' := apply22_bounds (g i') u' hu'
  rw [eu] at bu
  rw [eu'] at bu'
  have same : (i : ℕ) = i' → (g i).x = (g i').x := fun e => by rw [Fin.ext e]
  have := k0 i
  have := k0 i'
  have := k1 i
  have := k1 i'
  have := k2 i
  have := k2 i'
  have := k3 i
  have := k3 i'
  have := i.isLt
  have := i'.isLt
  simp only at bu bu'
  omega

/-- The hypothesis of Theorem 21 at `n = 3`, for every numbering. -/
theorem search_hypothesis_three (num : Placement → ℕ) :
    ¬ ∃ (a b w h : ℤ) (X : Finset Cell), IsSearchSolution num 3 a b w h X ∧ ¬ IsRectangular X := by
  rintro ⟨a, b, w, h, X, hX, -⟩
  rcases hX with ⟨g, hF, hP⟩ | ⟨g, hF, -⟩ | ⟨g, hF, -⟩ | ⟨g, hF, -⟩ | ⟨g, hF, -⟩
  · obtain ⟨-, -, hab, ha2, hab', -, -, hwh, hwh', -⟩ := id hF
    have h00 : ((0 : ℤ), (0 : ℤ)) ∈ R w h := hP.1.sub (hP.2.2 (by simp [knownI]))
    simp only [R, Finset.mem_product, Finset.mem_Ico] at h00
    obtain ⟨⟨-, hw0⟩, -, hh0⟩ := h00
    push_cast at hab hwh hwh'
    have ha3 : a ≤ 3 := by nlinarith
    have ha : a = 3 := by
      interval_cases a
      · omega
      · rfl
    subst ha
    have hb : b = 5 := by omega
    subst hb
    have hw : w = 2 := by
      have : w ≤ 3 := by omega
      have : h ≤ 3 := by omega
      interval_cases w <;> interval_cases h <;> omega
    have hh : h = 2 := by
      subst hw
      omega
    subst hw hh
    exact no_solution_I5_R35 num g X hF hP.1
  · obtain ⟨-, -, hab, ha2, -, hw, hh2, hha, -, hah, -⟩ := hF
    push_cast at hab hah
    have ha : a = 2 := by omega
    subst ha
    omega
  · obtain ⟨-, -, hab, ha2, hw, hh2, -, hah, -⟩ := hF
    push_cast at hab hah
    have ha : a = 2 := by omega
    subst ha
    omega
  · obtain ⟨-, -, hab, ha2, -, hw, hh2, hha, -, hah, -⟩ := hF
    push_cast at hab hah
    have ha : a = 2 := by omega
    subst ha
    omega
  · obtain ⟨-, -, hab, ha2, hw, hh2, -, hah, -⟩ := hF
    push_cast at hab hah
    have ha : a = 2 := by omega
    subst ha
    omega

/-! ## Non-vacuity witnesses -/

theorem corollary1a_crossing_nonvacuous :
    ∃ (a : ℤ) (b : ℤ) (_ : 2 ≤ a) (_ : 2 ≤ b) (S : Finset Cell) (S' : Finset Cell)
      (_ : S ⊆ R a b) (_ : EdgeConnected S) (_ : Meets S (leftCol a b))
      (_ : Meets S (rightCol a b)) (_ : S' ⊆ R a b) (_ : EdgeConnected S')
      (_ : Meets S' (bottomRow a b)) (_ : Meets S' (topRow a b)), True :=
  ⟨2, 2, le_refl _, le_refl _, domino, {(0, 0), (0, 1)}, by decide,
    domino_isPolyomino.2, (meets_iff _ _).2 (by decide), (meets_iff _ _).2 (by decide),
    by decide,
    edgeConnected_of_hub (0, 0) (by
      intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact Relation.ReflTransGen.refl
      · exact edge_step (by decide) (by decide) (by unfold Adj; decide)),
    (meets_iff _ _).2 (by decide), (meets_iff _ _).2 (by decide), trivial⟩

theorem lemma2_no_opposite_corners_nonvacuous :
    ∃ (P : Finset Cell) (_ : IsPolyomino P) (k : ℕ) (_ : 2 ≤ k) (a : ℤ) (b : ℤ)
      (t : Fin k → Finset Cell) (_ : IsTiling P a b t) (_i : Fin k), True :=
  ⟨ltromino, ltromino_isPolyomino, 4, by decide, 2, 6, tiling26, tiling26_isTiling, 0,
    trivial⟩

theorem lemma3_adjacent_corners_full_row_nonvacuous :
    ∃ (P : Finset Cell) (_ : IsPolyomino P) (k : ℕ) (_ : 2 ≤ k) (a : ℤ) (b : ℤ)
      (t : Fin k → Finset Cell) (_ : IsTiling P a b t) (i : Fin k) (_ : (0, 0) ∈ t i)
      (_ : (a - 1, 0) ∈ t i) (x : ℤ) (_ : 0 ≤ x) (_ : x < a), True :=
  ⟨ltromino, ltromino_isPolyomino, 4, by decide, 2, 6, tiling26, tiling26_isTiling, 0,
    by decide, by decide, 0, le_refl _, by decide, trivial⟩

/-- Theorem 21's hypotheses are met at `n = 3`: the search hypothesis holds there
(`search_hypothesis_three`) and the L-tromino is a non-rectangular polyomino
with 3 cells. -/
theorem theorem21_search_bridge_nonvacuous :
    ∃ (num : Placement → ℕ) (_ : Function.Injective num) (n : ℕ)
      (_ : ¬ ∃ (a b w h : ℤ) (X : Finset Cell),
        IsSearchSolution num n a b w h X ∧ ¬ IsRectangular X)
      (P : Finset Cell) (_ : IsPolyomino P) (_ : ¬ IsRectangular P) (_ : P.card = n), True :=
  ⟨placementNum, placementNum_injective, 3, search_hypothesis_three placementNum, ltromino,
    ltromino_isPolyomino, ltromino_not_isRectangular, by decide, trivial⟩

theorem theorem62_no_three_copy_tiling_nonvacuous :
    ∃ (P : Finset Cell) (_ : IsPolyomino P) (_ : ¬ IsRectangular P) (_a : ℤ) (_b : ℤ)
      (_t : Fin 3 → Finset Cell), True :=
  ⟨ltromino, ltromino_isPolyomino, ltromino_not_isRectangular, 0, 0, fun _ => ∅, trivial⟩

/-- The binders of Theorem A18 end at `t`: both conditions on `t` are inside the
negation. The mutants below show that each hypothesis and each condition is
used. -/
theorem theoremA18_no_case_one_tiling_nonvacuous :
    ∃ (P : Finset Cell) (_ : IsPolyomino P) (_ : ¬ IsRectangular P) (_a : ℤ) (_b : ℤ)
      (_t : Fin 5 → Finset Cell), True :=
  ⟨ltromino, ltromino_isPolyomino, ltromino_not_isRectangular, 0, 0, fun _ => ∅, trivial⟩

theorem corollaryA19_no_five_copy_tiling_nonvacuous :
    ∃ (P : Finset Cell) (_ : IsPolyomino P) (_ : ¬ IsRectangular P) (_a : ℤ) (_b : ℤ)
      (_t : Fin 5 → Finset Cell), True :=
  ⟨ltromino, ltromino_isPolyomino, ltromino_not_isRectangular, 0, 0, fun _ => ∅, trivial⟩

/-! ## Theorem A18 and Corollary A19: the form, and planted mutants

A mutant is the statement of A18 (or A19) with one hypothesis or condition
dropped or changed; each is refuted by an explicit family of five, four, six or
two sets. Case (I) and non-rectangularity are kept wherever they are not the
part that is changed. -/

/-- A18 as frozen (both conditions inside the negation) and as a statement with
the tiling as a hypothesis are equivalent, each as a full proposition. -/
theorem theoremA18_form_iff :
    (∀ (P : Finset Cell) (_ : IsPolyomino P) (_ : ¬ IsRectangular P) (a b : ℤ)
        (t : Fin 5 → Finset Cell), ¬ (IsTiling P a b t ∧ CornersInDistinctTiles a b t)) ↔
      (∀ (P : Finset Cell) (_ : IsPolyomino P) (_ : ¬ IsRectangular P) (a b : ℤ)
        (t : Fin 5 → Finset Cell) (_ : IsTiling P a b t), ¬ CornersInDistinctTiles a b t) :=
  ⟨fun h P hP hnr a b t ht hI => h P hP hnr a b t ⟨ht, hI⟩,
    fun h P hP hnr a b t hh => h P hP hnr a b t hh.1 hh.2⟩

/-- Mutant: A18 for all polyominoes, rectangles included, is false (five dominoes
in case (I)). -/
theorem mutantA18_rectangular_allowed :
    ¬ ∀ (P : Finset Cell) (_ : IsPolyomino P) (a b : ℤ) (t : Fin 5 → Finset Cell),
      ¬ (IsTiling P a b t ∧ CornersInDistinctTiles a b t) :=
  fun h => h domino domino_isPolyomino 2 5 dom5 ⟨dom5_isTiling, dom5_cornersInDistinctTiles⟩

/-- Mutant: A19 for all polyominoes, rectangles included, is false. -/
theorem mutantA19_rectangular_allowed :
    ¬ ∀ (P : Finset Cell) (_ : IsPolyomino P) (a b : ℤ) (t : Fin 5 → Finset Cell),
      ¬ IsTiling P a b t :=
  fun h => h domino domino_isPolyomino 2 5 dom5 dom5_isTiling

/-- Mutant: A18 for four copies is false (`t34`). -/
theorem mutantA18_four_copies :
    ¬ ∀ (P : Finset Cell) (_ : IsPolyomino P) (_ : ¬ IsRectangular P) (a b : ℤ)
      (t : Fin 4 → Finset Cell), ¬ (IsTiling P a b t ∧ CornersInDistinctTiles a b t) :=
  fun h => h p7 p7_isPolyomino p7_not_isRectangular 3 4 t34
    ⟨t34_isTiling, t34_cornersInDistinctTiles⟩

/-- Mutant: A19 for four copies is false (`t34`). -/
theorem mutantA19_four_copies :
    ¬ ∀ (P : Finset Cell) (_ : IsPolyomino P) (_ : ¬ IsRectangular P) (a b : ℤ)
      (t : Fin 4 → Finset Cell), ¬ IsTiling P a b t :=
  fun h => h p7 p7_isPolyomino p7_not_isRectangular 3 4 t34 t34_isTiling

/-- Two L-trominoes tile `R 2 3`. -/
theorem tiling23_isTiling : IsTiling ltromino 2 3 ![ltromino, tileB] where
  congruent := by
    intro i
    fin_cases i
    · exact ⟨⟨false, false, false, (0, 0)⟩, by decide⟩
    · exact ⟨⟨false, true, true, (1, 2)⟩, by decide⟩
  disjoint := by decide
  cover := by decide

/-- Mutant: A19 for two copies is false. -/
theorem mutantA19_two_copies :
    ¬ ∀ (P : Finset Cell) (_ : IsPolyomino P) (_ : ¬ IsRectangular P) (a b : ℤ)
      (t : Fin 2 → Finset Cell), ¬ IsTiling P a b t :=
  fun h => h ltromino ltromino_isPolyomino ltromino_not_isRectangular 2 3 _ tiling23_isTiling

/-- The tiling `t34` with two more L-trominoes on top: a tiling of `R 3 6` by six
copies of `p7`, the corners in four distinct tiles. -/
def t36 : Fin 6 → Finset Cell :=
  ![{(0, 0), (0, 1), (1, 1)}, {(1, 0), (2, 0), (2, 1)},
    {(0, 2), (0, 3), (1, 3)}, {(1, 2), (2, 2), (2, 3)},
    {(0, 4), (0, 5), (1, 5)}, {(1, 4), (2, 4), (2, 5)}]

theorem t36_isTiling : IsTiling p7 3 6 t36 where
  congruent := by
    intro i
    fin_cases i
    · exact ⟨⟨false, true, false, (1, 0)⟩, by decide⟩
    · exact ⟨⟨false, false, true, (1, 1)⟩, by decide⟩
    · exact ⟨⟨false, true, false, (1, 2)⟩, by decide⟩
    · exact ⟨⟨false, false, true, (1, 3)⟩, by decide⟩
    · exact ⟨⟨false, true, false, (1, 4)⟩, by decide⟩
    · exact ⟨⟨false, false, true, (1, 5)⟩, by decide⟩
  disjoint := by decide
  cover := by decide

theorem t36_cornersInDistinctTiles : CornersInDistinctTiles 3 6 t36 := by
  unfold CornersInDistinctTiles
  decide

/-- Mutant: A18 for six copies is false. -/
theorem mutantA18_six_copies :
    ¬ ∀ (P : Finset Cell) (_ : IsPolyomino P) (_ : ¬ IsRectangular P) (a b : ℤ)
      (t : Fin 6 → Finset Cell), ¬ (IsTiling P a b t ∧ CornersInDistinctTiles a b t) :=
  fun h => h p7 p7_isPolyomino p7_not_isRectangular 3 6 t36
    ⟨t36_isTiling, t36_cornersInDistinctTiles⟩

/-- Mutant: A19 for six copies is false. -/
theorem mutantA19_six_copies :
    ¬ ∀ (P : Finset Cell) (_ : IsPolyomino P) (_ : ¬ IsRectangular P) (a b : ℤ)
      (t : Fin 6 → Finset Cell), ¬ IsTiling P a b t :=
  fun h => h p7 p7_isPolyomino p7_not_isRectangular 3 6 t36 t36_isTiling

/-- Six cells, not edge-connected: rows 0, 1 and 3 of the columns 0 and 3. -/
def scattered : Finset Cell := {(0, 0), (0, 1), (0, 3), (3, 0), (3, 1), (3, 3)}

/-- Five copies of `scattered` that tile `R 5 6`, the corners in four distinct
tiles. -/
def scat5 : Fin 5 → Finset Cell :=
  ![scattered, {(0, 2), (0, 4), (0, 5), (3, 2), (3, 4), (3, 5)},
    {(1, 0), (1, 3), (2, 0), (2, 3), (4, 0), (4, 3)},
    {(1, 1), (1, 4), (2, 1), (2, 4), (4, 1), (4, 4)},
    {(1, 2), (1, 5), (2, 2), (2, 5), (4, 2), (4, 5)}]

theorem scattered_not_isRectangular : ¬ IsRectangular scattered := by
  unfold IsRectangular
  decide

theorem scat5_isTiling : IsTiling scattered 5 6 scat5 where
  congruent := by
    intro i
    fin_cases i
    · exact ⟨⟨false, false, false, (0, 0)⟩, by decide⟩
    · exact ⟨⟨false, false, true, (0, 5)⟩, by decide⟩
    · exact ⟨⟨true, false, false, (1, 0)⟩, by decide⟩
    · exact ⟨⟨true, false, false, (1, 1)⟩, by decide⟩
    · exact ⟨⟨true, false, false, (1, 2)⟩, by decide⟩
  disjoint := by decide
  cover := by decide

theorem scat5_cornersInDistinctTiles : CornersInDistinctTiles 5 6 scat5 := by
  unfold CornersInDistinctTiles
  decide

/-- Mutant: A18 without connectedness (`P` only non-empty) is false. -/
theorem mutantA18_not_connected :
    ¬ ∀ (P : Finset Cell) (_ : P.Nonempty) (_ : ¬ IsRectangular P) (a b : ℤ)
      (t : Fin 5 → Finset Cell), ¬ (IsTiling P a b t ∧ CornersInDistinctTiles a b t) :=
  fun h => h scattered ⟨(0, 0), by decide⟩ scattered_not_isRectangular 5 6 scat5
    ⟨scat5_isTiling, scat5_cornersInDistinctTiles⟩

/-- Mutant: A19 without connectedness is false. -/
theorem mutantA19_not_connected :
    ¬ ∀ (P : Finset Cell) (_ : P.Nonempty) (_ : ¬ IsRectangular P) (a b : ℤ)
      (t : Fin 5 → Finset Cell), ¬ IsTiling P a b t :=
  fun h => h scattered ⟨(0, 0), by decide⟩ scattered_not_isRectangular 5 6 scat5
    scat5_isTiling

/-- Mutant: `CornersInDistinctTiles` in A18 is not the empty condition: `dom5`
meets it and the horizontal rows of five dominoes do not. -/
theorem rows5_not_cornersInDistinctTiles :
    ¬ CornersInDistinctTiles 2 5 (![{(0, 0), (1, 0)}, {(0, 1), (1, 1)}, {(0, 2), (1, 2)},
      {(0, 3), (1, 3)}, {(0, 4), (1, 4)}] : Fin 5 → Finset Cell) := by
  intro h
  exact absurd (h 0 0 1 (by decide) (by decide)) (by decide)

/-- Mutant: A18 with tiles that may overlap (the copies only cover `R a b`) is
false: `t34` with its third tile listed twice. -/
theorem mutantA18_overlap_allowed :
    ¬ ∀ (P : Finset Cell) (_ : IsPolyomino P) (_ : ¬ IsRectangular P) (a b : ℤ)
      (t : Fin 5 → Finset Cell), ¬ (((∀ i, Congruent P (t i)) ∧
        Finset.univ.biUnion t = R a b) ∧ CornersInDistinctTiles a b t) := by
  intro h
  refine h p7 p7_isPolyomino p7_not_isRectangular 3 4
    ![t34 0, t34 1, t34 2, t34 3, t34 2] ⟨⟨?_, by decide⟩, ?_⟩
  · intro i
    fin_cases i
    · exact t34_isTiling.congruent 0
    · exact t34_isTiling.congruent 1
    · exact t34_isTiling.congruent 2
    · exact t34_isTiling.congruent 3
    · exact t34_isTiling.congruent 2
  · unfold CornersInDistinctTiles
    decide

/-- Mutant: A18 with copies that only pack `R a b` (disjoint, inside, not
covering, all four corner cells covered) is false: five of the six tiles of
`t36`. -/
theorem mutantA18_packing :
    ¬ ∀ (P : Finset Cell) (_ : IsPolyomino P) (_ : ¬ IsRectangular P) (a b : ℤ)
      (t : Fin 5 → Finset Cell), ¬ (((∀ i, Congruent P (t i)) ∧
        (∀ i j, i ≠ j → Disjoint (t i) (t j)) ∧ (∀ i, t i ⊆ R a b) ∧
        ∀ j : Fin 4, ∃ i, corner a b j ∈ t i) ∧ CornersInDistinctTiles a b t) := by
  intro h
  refine h p7 p7_isPolyomino p7_not_isRectangular 3 6
    ![t36 0, t36 1, t36 2, t36 4, t36 5] ⟨⟨?_, by decide, by decide, by decide⟩, ?_⟩
  · intro i
    fin_cases i
    · exact t36_isTiling.congruent 0
    · exact t36_isTiling.congruent 1
    · exact t36_isTiling.congruent 2
    · exact t36_isTiling.congruent 4
    · exact t36_isTiling.congruent 5
  · unfold CornersInDistinctTiles
    decide

/-- `t36` with its third and fifth tile united: five non-rectangular polyominoes,
not all congruent, that partition `R 3 6`. -/
def mixed5 : Fin 5 → Finset Cell :=
  ![{(0, 0), (0, 1), (1, 1)}, {(1, 0), (2, 0), (2, 1)},
    {(0, 2), (0, 3), (1, 3), (0, 4), (0, 5), (1, 5)},
    {(1, 2), (2, 2), (2, 3)}, {(1, 4), (2, 4), (2, 5)}]

/-- The tiles of `mixed5` are polyominoes. -/
theorem mixed5_isPolyomino (i : Fin 5) : IsPolyomino (mixed5 i) := by
  fin_cases i
  · exact ⟨⟨(0, 0), by decide⟩, tile34_edgeConnected⟩
  · refine ⟨⟨(2, 0), by decide⟩, edgeConnected_of_hub (2, 0) ?_⟩
    intro c hc
    have hc' : c ∈ ({(1, 0), (2, 0), (2, 1)} : Finset Cell) := hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with rfl | rfl | rfl
    · exact edge_step (by decide) (by decide) (by unfold Adj; decide)
    · exact Relation.ReflTransGen.refl
    · exact edge_step (by decide) (by decide) (by unfold Adj; decide)
  · refine ⟨⟨(0, 3), by decide⟩, edgeConnected_of_hub (0, 3) ?_⟩
    intro c hc
    have hc' : c ∈ ({(0, 2), (0, 3), (1, 3), (0, 4), (0, 5), (1, 5)} : Finset Cell) := hc
    have h4 : Relation.ReflTransGen (fun u v : Cell => u ∈ mixed5 2 ∧ v ∈ mixed5 2 ∧ Adj u v)
        (0, 3) (0, 4) := edge_step (by decide) (by decide) (by unfold Adj; decide)
    have h5 : Relation.ReflTransGen (fun u v : Cell => u ∈ mixed5 2 ∧ v ∈ mixed5 2 ∧ Adj u v)
        (0, 3) (0, 5) := h4.tail ⟨by decide, by decide, by unfold Adj; decide⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl
    · exact edge_step (by decide) (by decide) (by unfold Adj; decide)
    · exact Relation.ReflTransGen.refl
    · exact edge_step (by decide) (by decide) (by unfold Adj; decide)
    · exact h4
    · exact h5
    · exact h5.tail ⟨by decide, by decide, by unfold Adj; decide⟩
  · refine ⟨⟨(2, 2), by decide⟩, edgeConnected_of_hub (2, 2) ?_⟩
    intro c hc
    have hc' : c ∈ ({(1, 2), (2, 2), (2, 3)} : Finset Cell) := hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with rfl | rfl | rfl
    · exact edge_step (by decide) (by decide) (by unfold Adj; decide)
    · exact Relation.ReflTransGen.refl
    · exact edge_step (by decide) (by decide) (by unfold Adj; decide)
  · refine ⟨⟨(2, 4), by decide⟩, edgeConnected_of_hub (2, 4) ?_⟩
    intro c hc
    have hc' : c ∈ ({(1, 4), (2, 4), (2, 5)} : Finset Cell) := hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with rfl | rfl | rfl
    · exact edge_step (by decide) (by decide) (by unfold Adj; decide)
    · exact Relation.ReflTransGen.refl
    · exact edge_step (by decide) (by decide) (by unfold Adj; decide)

/-- Mutant: A18 with five non-rectangular polyominoes that need not be congruent
is false. -/
theorem mutantA18_not_congruent :
    ¬ ∀ (a b : ℤ) (t : Fin 5 → Finset Cell), ¬ (((∀ i, IsPolyomino (t i)) ∧
        (∀ i, ¬ IsRectangular (t i)) ∧ (∀ i j, i ≠ j → Disjoint (t i) (t j)) ∧
        Finset.univ.biUnion t = R a b) ∧ CornersInDistinctTiles a b t) := by
  intro h
  refine h 3 6 mixed5 ⟨⟨mixed5_isPolyomino, ?_, by decide, by decide⟩, ?_⟩
  · unfold IsRectangular
    decide
  · unfold CornersInDistinctTiles
    decide

/-- Mutant: A19 with five non-rectangular polyominoes that need not be congruent
is false. -/
theorem mutantA19_not_congruent :
    ¬ ∀ (a b : ℤ) (t : Fin 5 → Finset Cell), ¬ ((∀ i, IsPolyomino (t i)) ∧
        (∀ i, ¬ IsRectangular (t i)) ∧ (∀ i j, i ≠ j → Disjoint (t i) (t j)) ∧
        Finset.univ.biUnion t = R a b) := by
  intro h
  refine h 3 6 mixed5 ⟨mixed5_isPolyomino, ?_, by decide, by decide⟩
  unfold IsRectangular
  decide

end PolyominoOddOrder.Sanity
