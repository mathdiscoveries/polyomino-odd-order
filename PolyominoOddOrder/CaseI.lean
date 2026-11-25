module

public import PolyominoOddOrder.Crossing

/-!
# Case (I): how the tiles meet the sides (`CaseI.lean`)

Blueprint unit I1. `report-4.md`, section 7: Lemma 56 (enclosure), Proposition 57
(a), (b) (the sides in case (I)) and the part of Corollary 59 about two adjacent
sides. This file needs only the crossing argument (`Crossing.lean`), not the
spines. Two opposite sides (Propositions 58 and 60) are `CaseIOpposite.lean`.

Lemma 56 is stated for the whole tile `T` in place of a path `gamma` in `T`: the
component of a cell in `R` minus `T` lies in its component in `R` minus `gamma`, so
condition (i) of the lemma passes to it, and the proof is the same. No list of
cells is then needed.

The binding statements of this file are `sides_are_intervals` and
`corner_tile_sides`, the internal forms of the frozen statements (f), and
`free_tile_not_adjacent`. The last two are corollaries of
`corner_mem_of_adjacent_sides`: in any tiling by a polyomino, a tile that meets two
adjacent sides holds the corner cell between them (no case (I), any number of
tiles). It is the argument of Proposition 57 (b) and of Corollary 59, which the
report gives twice.

Not on the path and not stated: Proposition 57 (c) (the fifth tile does not meet
all four sides; Corollary 59 covers it).

Commit `e5ca51d`.
-/

@[expose] public section

namespace PolyominoOddOrder

/-! ## Rows and columns of a cut-off region -/

/-- If the right end of the row of a cell of a component of `R a b` minus `S` is
not in the component, `S` has a cell strictly to the right of it in that row.
Source: `report-4.md`, Remark after Lemma 56 (line 503): "the cells from c to the
end are consecutive neighbours; if none were on gamma all would lie in the
component of c". -/
theorem exists_right_of_component {a b : ℤ} {S : Finset Cell} {q c : Cell}
    (hc : c ∈ component (R a b \ S) q) (hend : (a - 1, c.2) ∉ component (R a b \ S) q) :
    ∃ x : ℤ, c.1 < x ∧ (x, c.2) ∈ S := by
  by_contra hno
  push Not at hno
  obtain ⟨hcA, hqc⟩ := mem_component.1 hc
  obtain ⟨hcR, hcS⟩ := Finset.mem_sdiff.1 hcA
  have hcR' := mem_R.1 hcR
  have hseg : ∀ z, c.1 ≤ z → z ≤ a - 1 → (z, c.2) ∈ R a b \ S := by
    intro z h1 h2
    refine Finset.mem_sdiff.2 ⟨mem_R.2 ⟨⟨by dsimp only; omega, by dsimp only; omega⟩, hcR'.2⟩,
      fun hz => ?_⟩
    rcases eq_or_lt_of_le h1 with rfl | hlt
    · exact hcS hz
    · exact hno z hlt hz
  exact hend (mem_component.2 ⟨hseg _ (by omega) le_rfl,
    hqc.trans (Reach.along_row (by omega) hseg)⟩)

/-- The same to the left. -/
theorem exists_left_of_component {a b : ℤ} {S : Finset Cell} {q c : Cell}
    (hc : c ∈ component (R a b \ S) q) (hend : (0, c.2) ∉ component (R a b \ S) q) :
    ∃ x : ℤ, x < c.1 ∧ (x, c.2) ∈ S := by
  by_contra hno
  push Not at hno
  obtain ⟨hcA, hqc⟩ := mem_component.1 hc
  obtain ⟨hcR, hcS⟩ := Finset.mem_sdiff.1 hcA
  have hcR' := mem_R.1 hcR
  have hseg : ∀ z, 0 ≤ z → z ≤ c.1 → (z, c.2) ∈ R a b \ S := by
    intro z h1 h2
    refine Finset.mem_sdiff.2 ⟨mem_R.2 ⟨⟨by dsimp only; omega, by dsimp only; omega⟩, hcR'.2⟩,
      fun hz => ?_⟩
    rcases eq_or_lt_of_le h2 with rfl | hlt
    · exact hcS hz
    · exact hno z hlt hz
  exact hend (mem_component.2 ⟨hseg _ le_rfl (by omega),
    hqc.trans (Reach.along_row (by omega) hseg).symm⟩)

/-- The same upwards. -/
theorem exists_above_of_component {a b : ℤ} {S : Finset Cell} {q c : Cell}
    (hc : c ∈ component (R a b \ S) q) (hend : (c.1, b - 1) ∉ component (R a b \ S) q) :
    ∃ y : ℤ, c.2 < y ∧ (c.1, y) ∈ S := by
  by_contra hno
  push Not at hno
  obtain ⟨hcA, hqc⟩ := mem_component.1 hc
  obtain ⟨hcR, hcS⟩ := Finset.mem_sdiff.1 hcA
  have hcR' := mem_R.1 hcR
  have hseg : ∀ z, c.2 ≤ z → z ≤ b - 1 → (c.1, z) ∈ R a b \ S := by
    intro z h1 h2
    refine Finset.mem_sdiff.2 ⟨mem_R.2 ⟨hcR'.1, by dsimp only; omega, by dsimp only; omega⟩,
      fun hz => ?_⟩
    rcases eq_or_lt_of_le h1 with rfl | hlt
    · exact hcS hz
    · exact hno z hlt hz
  exact hend (mem_component.2 ⟨hseg _ (by omega) le_rfl,
    hqc.trans (Reach.along_col (by omega) hseg)⟩)

/-- The same downwards. -/
theorem exists_below_of_component {a b : ℤ} {S : Finset Cell} {q c : Cell}
    (hc : c ∈ component (R a b \ S) q) (hend : (c.1, 0) ∉ component (R a b \ S) q) :
    ∃ y : ℤ, y < c.2 ∧ (c.1, y) ∈ S := by
  by_contra hno
  push Not at hno
  obtain ⟨hcA, hqc⟩ := mem_component.1 hc
  obtain ⟨hcR, hcS⟩ := Finset.mem_sdiff.1 hcA
  have hcR' := mem_R.1 hcR
  have hseg : ∀ z, 0 ≤ z → z ≤ c.2 → (c.1, z) ∈ R a b \ S := by
    intro z h1 h2
    refine Finset.mem_sdiff.2 ⟨mem_R.2 ⟨hcR'.1, by dsimp only; omega, by dsimp only; omega⟩,
      fun hz => ?_⟩
    rcases eq_or_lt_of_le h2 with rfl | hlt
    · exact hcS hz
    · exact hno z hlt hz
  exact hend (mem_component.2 ⟨hseg _ le_rfl (by omega),
    hqc.trans (Reach.along_col (by omega) hseg).symm⟩)

/-! ## Lemma 56 -/

/-- Lemma 56 (enclosure), directions `e` = right and `f` = up. Source:
`report-4.md`, section 7, Lemma 56 (lines 489-493):

> Let T, T' be different tiles, let a cell path gamma in T join two cells on the
> boundary of R, and let Omega be a union of connected components of R minus gamma.
> Fix one horizontal direction e (left or right) and one vertical direction f (up or
> down), the same for all cells. Suppose
> (i) every cell of Omega has a cell of gamma strictly beyond it in direction e in its
> row, and one strictly beyond it in direction f in its column;
> (ii) if Omega has a cell on the side of R opposite to e, then T has a cell on that
> side; likewise for f.
> If T' has a cell in Omega, then T' lies in Omega, both sides of box(T') are shorter
> than the parallel sides of box(T), and T, T' are not congruent.

Here `Omega` is the component of a cell `q` of `T'` in `R a b` minus `T`. The other
three pairs of directions are the images of this one under `GridIso.flipX` and
`GridIso.flipY`. -/
theorem enclosure {a b : ℤ} {T T' : Finset Cell} (hTR : T ⊆ R a b) (hT'R : T' ⊆ R a b)
    (hT' : EdgeConnected T') (hdisj : Disjoint T T') {q : Cell} (hq : q ∈ T')
    (hi : ∀ c ∈ component (R a b \ T) q,
      (∃ x : ℤ, c.1 < x ∧ (x, c.2) ∈ T) ∧ ∃ y : ℤ, c.2 < y ∧ (c.1, y) ∈ T)
    (hii₁ : (∃ c ∈ component (R a b \ T) q, c.1 = 0) → ∃ y : ℤ, (0, y) ∈ T)
    (hii₂ : (∃ c ∈ component (R a b \ T) q, c.2 = 0) → ∃ x : ℤ, (x, 0) ∈ T) :
    width T' < width T ∧ height T' < height T := by
  have _ := hTR -- not needed: the region lies in `R a b` by definition
  have hT'A : T' ⊆ R a b \ T := fun c hc =>
    Finset.mem_sdiff.2 ⟨hT'R hc, fun h => Finset.disjoint_left.1 hdisj h hc⟩
  have hqO : q ∈ component (R a b \ T) q := mem_component.2 ⟨hT'A hq, Reach.refl _ _⟩
  have hsub : T' ⊆ component (R a b \ T) q := hT'.subset_component hT'A ⟨q, hq, hqO⟩
  constructor
  · obtain ⟨lo, hi', hle, hspan, ⟨y, hy⟩, y', hy'⟩ := xSpan_eq_Icc ⟨q, hq⟩
    obtain ⟨⟨x, hx, hxT⟩, -⟩ := hi _ (hsub hy')
    dsimp only at hx hxT
    obtain ⟨d, hdT, hdlo⟩ : ∃ d ∈ T, d.1 ≤ lo := by
      obtain ⟨c, hc, hmin⟩ := Finset.exists_min_image (component (R a b \ T) q)
        (fun c => c.1) ⟨q, hqO⟩
      have hclo : c.1 ≤ lo := hmin _ (hsub hy)
      have hcR := mem_R.1 (Finset.mem_sdiff.1 (mem_component.1 hc).1).1
      by_cases h0 : c.1 = 0
      · obtain ⟨z, hz⟩ := hii₁ ⟨c, hc, h0⟩
        exact ⟨_, hz, by dsimp only; omega⟩
      · by_cases hcT : ((c.1 - 1, c.2) : Cell) ∈ T
        · exact ⟨_, hcT, by dsimp only; omega⟩
        · have hR : ((c.1 - 1, c.2) : Cell) ∈ R a b :=
            mem_R.2 ⟨⟨by dsimp only; omega, by dsimp only; omega⟩, hcR.2⟩
          have hadj : Adj c (c.1 - 1, c.2) := Or.inr ⟨rfl, Or.inr (by dsimp only; omega)⟩
          have := hmin _ (component_closed hc (Finset.mem_sdiff.2 ⟨hR, hcT⟩) hadj)
          dsimp only at this
          omega
    have hsubset : Finset.Icc lo x ⊆ xSpan T := by
      intro v hv
      rw [Finset.mem_Icc] at hv
      exact mem_xSpan.2 ⟨d, hdT, (x, y'), hxT, hdlo.trans hv.1, hv.2⟩
    have hcard := Finset.card_le_card hsubset
    rw [Int.card_Icc] at hcard
    unfold width
    rw [hspan, Int.card_Icc]
    omega
  · obtain ⟨lo, hi', hle, hspan, ⟨x, hx⟩, x', hx'⟩ := ySpan_eq_Icc ⟨q, hq⟩
    obtain ⟨-, y, hy, hyT⟩ := hi _ (hsub hx')
    dsimp only at hy hyT
    obtain ⟨d, hdT, hdlo⟩ : ∃ d ∈ T, d.2 ≤ lo := by
      obtain ⟨c, hc, hmin⟩ := Finset.exists_min_image (component (R a b \ T) q)
        (fun c => c.2) ⟨q, hqO⟩
      have hclo : c.2 ≤ lo := hmin _ (hsub hx)
      have hcR := mem_R.1 (Finset.mem_sdiff.1 (mem_component.1 hc).1).1
      by_cases h0 : c.2 = 0
      · obtain ⟨z, hz⟩ := hii₂ ⟨c, hc, h0⟩
        exact ⟨_, hz, by dsimp only; omega⟩
      · by_cases hcT : ((c.1, c.2 - 1) : Cell) ∈ T
        · exact ⟨_, hcT, by dsimp only; omega⟩
        · have hR : ((c.1, c.2 - 1) : Cell) ∈ R a b :=
            mem_R.2 ⟨hcR.1, by dsimp only; omega, by dsimp only; omega⟩
          have hadj : Adj c (c.1, c.2 - 1) := Or.inl ⟨rfl, Or.inr (by dsimp only; omega)⟩
          have := hmin _ (component_closed hc (Finset.mem_sdiff.2 ⟨hR, hcT⟩) hadj)
          dsimp only at this
          omega
    have hsubset : Finset.Icc lo y ⊆ ySpan T := by
      intro v hv
      rw [Finset.mem_Icc] at hv
      exact mem_ySpan.2 ⟨d, hdT, (x', y), hyT, hdlo.trans hv.1, hv.2⟩
    have hcard := Finset.card_le_card hsubset
    rw [Int.card_Icc] at hcard
    unfold height
    rw [hspan, Int.card_Icc]
    omega

/-- Lemma 56, conclusion: the two tiles are not congruent. -/
theorem enclosure_not_congruent {a b : ℤ} {T T' : Finset Cell} (hTR : T ⊆ R a b)
    (hT'R : T' ⊆ R a b) (hT' : EdgeConnected T') (hdisj : Disjoint T T') {q : Cell}
    (hq : q ∈ T')
    (hi : ∀ c ∈ component (R a b \ T) q,
      (∃ x : ℤ, c.1 < x ∧ (x, c.2) ∈ T) ∧ ∃ y : ℤ, c.2 < y ∧ (c.1, y) ∈ T)
    (hii₁ : (∃ c ∈ component (R a b \ T) q, c.1 = 0) → ∃ y : ℤ, (0, y) ∈ T)
    (hii₂ : (∃ c ∈ component (R a b \ T) q, c.2 = 0) → ∃ x : ℤ, (x, 0) ∈ T) :
    ¬ Congruent T T' := by
  obtain ⟨hw, hh⟩ := enclosure hTR hT'R hT' hdisj hq hi hii₁ hii₂
  exact not_congruent_of_smaller hw hh

/-! ## Case (I) under the symmetries of the rectangle -/

/-- Membership in the mirror image of a set. -/
theorem CaseI.mem_image_flipX {a : ℤ} {S : Finset Cell} {c : Cell} :
    c ∈ S.image (GridIso.flipX a).apply ↔ (a - 1 - c.1, c.2) ∈ S := by
  have h : (GridIso.flipX a).inv.apply c = (a - 1 - c.1, c.2) := by
    apply (GridIso.flipX a).apply_injective
    rw [GridIso.apply_inv_apply, GridIso.flipX_apply]
    simp
  rw [GridIso.mem_image_iff, h]

/-- Membership in the image of a set under the reflection `F`. -/
theorem CaseI.mem_image_flipY {b : ℤ} {S : Finset Cell} {c : Cell} :
    c ∈ S.image (GridIso.flipY b).apply ↔ (c.1, b - 1 - c.2) ∈ S := by
  have h : (GridIso.flipY b).inv.apply c = (c.1, b - 1 - c.2) := by
    apply (GridIso.flipY b).apply_injective
    rw [GridIso.apply_inv_apply, GridIso.flipY_apply]
    simp
  rw [GridIso.mem_image_iff, h]

/-- Membership in the half turn of a set. -/
theorem CaseI.mem_image_halfTurn {a b : ℤ} {S : Finset Cell} {c : Cell} :
    c ∈ S.image (GridIso.halfTurn a b).apply ↔ (a - 1 - c.1, b - 1 - c.2) ∈ S := by
  have h : (GridIso.halfTurn a b).inv.apply c = (a - 1 - c.1, b - 1 - c.2) := by
    apply (GridIso.halfTurn a b).apply_injective
    rw [GridIso.apply_inv_apply, GridIso.halfTurn_apply]
    simp
  rw [GridIso.mem_image_iff, h]

/-- Membership in the transpose of a set. -/
theorem CaseI.mem_image_transpose {S : Finset Cell} {c : Cell} :
    c ∈ S.image GridIso.transpose.apply ↔ (c.2, c.1) ∈ S := by
  have h : GridIso.transpose.inv.apply c = (c.2, c.1) := by
    apply GridIso.transpose.apply_injective
    rw [GridIso.apply_inv_apply, GridIso.transpose_apply]
  rw [GridIso.mem_image_iff, h]

/-- The mirror image permutes the corners as `0 ↔ 1`, `2 ↔ 3`. -/
theorem CaseI.corner_mem_image_flipX {a b : ℤ} {S : Finset Cell} {j : Fin 4} :
    corner a b j ∈ S.image (GridIso.flipX a).apply ↔
      corner a b ((![1, 0, 3, 2] : Fin 4 → Fin 4) j) ∈ S := by
  rw [CaseI.mem_image_flipX]
  fin_cases j <;> simp

/-- The reflection `F` permutes the corners as `0 ↔ 3`, `1 ↔ 2`. -/
theorem CaseI.corner_mem_image_flipY {a b : ℤ} {S : Finset Cell} {j : Fin 4} :
    corner a b j ∈ S.image (GridIso.flipY b).apply ↔
      corner a b ((![3, 2, 1, 0] : Fin 4 → Fin 4) j) ∈ S := by
  rw [CaseI.mem_image_flipY]
  fin_cases j <;> simp

/-- The transposition carries the corners of `R b a` to those of `R a b` and
exchanges the numbers `1` and `3`. -/
theorem CaseI.corner_mem_image_transpose {a b : ℤ} {S : Finset Cell} {j : Fin 4} :
    corner b a j ∈ S.image GridIso.transpose.apply ↔
      corner a b ((![0, 3, 2, 1] : Fin 4 → Fin 4) j) ∈ S := by
  rw [CaseI.mem_image_transpose]
  fin_cases j <;> simp

/-- Case (I) is kept by the mirror image. -/
theorem CornersInDistinctTiles.flipX {a b : ℤ} {k : ℕ} {t : Fin k → Finset Cell}
    (h : CornersInDistinctTiles a b t) :
    CornersInDistinctTiles a b fun i => (t i).image (GridIso.flipX a).apply := by
  intro i j j' hj hj'
  have inj : Function.Injective (![1, 0, 3, 2] : Fin 4 → Fin 4) := by decide
  exact inj (h i _ _ (CaseI.corner_mem_image_flipX.1 hj)
    (CaseI.corner_mem_image_flipX.1 hj'))

/-- Case (I) is kept by the reflection `F`. -/
theorem CornersInDistinctTiles.flipY {a b : ℤ} {k : ℕ} {t : Fin k → Finset Cell}
    (h : CornersInDistinctTiles a b t) :
    CornersInDistinctTiles a b fun i => (t i).image (GridIso.flipY b).apply := by
  intro i j j' hj hj'
  have inj : Function.Injective (![3, 2, 1, 0] : Fin 4 → Fin 4) := by decide
  exact inj (h i _ _ (CaseI.corner_mem_image_flipY.1 hj)
    (CaseI.corner_mem_image_flipY.1 hj'))

/-- Case (I) is kept by the transposition. -/
theorem CornersInDistinctTiles.transpose {a b : ℤ} {k : ℕ} {t : Fin k → Finset Cell}
    (h : CornersInDistinctTiles a b t) :
    CornersInDistinctTiles b a fun i => (t i).image GridIso.transpose.apply := by
  intro i j j' hj hj'
  have inj : Function.Injective (![0, 3, 2, 1] : Fin 4 → Fin 4) := by decide
  exact inj (h i _ _ (CaseI.corner_mem_image_transpose.1 hj)
    (CaseI.corner_mem_image_transpose.1 hj'))

/-! ## Proposition 57 -/

/-- The position of a cell of the bottom row. -/
theorem CaseI.bpos_bottom (a b x : ℤ) : bpos a b (x, 0) = x := by
  simp [bpos]

/-- The positions of the right column, from the corner `(a - 1, 0)` up. -/
theorem CaseI.bpos_right {a b y : ℤ} (hy0 : 0 ≤ y) (hyb : y < b) :
    a - 1 ≤ bpos a b (a - 1, y) ∧ bpos a b (a - 1, y) ≤ (a - 1) + (b - 1) := by
  simp only [bpos]
  split_ifs <;> constructor <;> omega

/-- The positions of the top row. -/
theorem CaseI.bpos_top {a b x : ℤ} (hb : 2 ≤ b) (hx0 : 0 ≤ x) (hxa : x < a) :
    (a - 1) + (b - 1) ≤ bpos a b (x, b - 1) ∧
      bpos a b (x, b - 1) ≤ 2 * (a - 1) + (b - 1) := by
  simp only [bpos]
  split_ifs <;> constructor <;> omega

/-- The positions of the left column above the corner `(0, 0)`. -/
theorem CaseI.bpos_left {a b y : ℤ} (ha : 2 ≤ a) (hy0 : 0 < y) (hyb : y < b) :
    2 * (a - 1) + (b - 1) ≤ bpos a b (0, y) := by
  simp only [bpos]
  split_ifs <;> omega

/-- The right end of the row of a cell of `R a b` is a boundary cell. -/
theorem CaseI.onBoundary_right {a b : ℤ} {c : Cell} (hc : c ∈ R a b) :
    OnBoundary a b (a - 1, c.2) := by
  have h := mem_R.1 hc
  exact ⟨mem_R.2 ⟨⟨by dsimp only; omega, by dsimp only; omega⟩, h.2⟩, Or.inr (Or.inl rfl)⟩

/-- The top end of the column of a cell of `R a b` is a boundary cell. -/
theorem CaseI.onBoundary_top {a b : ℤ} {c : Cell} (hc : c ∈ R a b) :
    OnBoundary a b (c.1, b - 1) := by
  have h := mem_R.1 hc
  exact ⟨mem_R.2 ⟨h.1, by dsimp only; omega, by dsimp only; omega⟩,
    Or.inr (Or.inr (Or.inr rfl))⟩

/-- A component of `R a b` minus `S` lies in `R a b`. -/
theorem CaseI.component_subset_R {a b : ℤ} {S : Finset Cell} {q c : Cell}
    (hc : c ∈ component (R a b \ S) q) : c ∈ R a b :=
  (Finset.mem_sdiff.1 (mem_component.1 hc).1).1

/-- Proposition 57 (a) on the bottom side, for any number of tiles. Source:
`report-4.md`, Proposition 57 (a) (line 507) and its proof in full (line 517).
Proof idea: for `b = 1` use `EdgeConnected.exists_in_col`; otherwise
`component_boundary`, `exists_right_of_component`, `exists_left_of_component`,
`exists_above_of_component`, then `enclosure_not_congruent`. Neither case (I) nor
"not rectangular" is used. -/
theorem bottom_is_interval (P : Finset Cell) (hP : IsPolyomino P) (k : ℕ) (a b : ℤ)
    (t : Fin k → Finset Cell) (ht : IsTiling P a b t) (i : Fin k) :
    RowInterval (t i) 0 := by
  intro x₁ x₂ x₃ h12 h23 h1 h3
  by_contra h2
  have hlt12 : x₁ < x₂ := lt_of_le_of_ne h12 (by rintro rfl; exact h2 h1)
  have hlt23 : x₂ < x₃ := lt_of_le_of_ne h23 (by rintro rfl; exact h2 h3)
  have hT := ht.tile_isPolyomino hP i
  have hR := ht.subset_R i
  have h1R := mem_R.1 (hR h1)
  have h3R := mem_R.1 (hR h3)
  dsimp only at h1R h3R
  have ha : 2 ≤ a := by omega
  have h2R : ((x₂, 0) : Cell) ∈ R a b :=
    mem_R.2 ⟨⟨by dsimp only; omega, by dsimp only; omega⟩, h1R.2⟩
  by_cases hb1 : b = 1
  · obtain ⟨y, hy⟩ := hT.2.exists_in_col h1 h3 h12 h23
    have hyR := mem_R.1 (hR hy)
    obtain rfl : y = 0 := by dsimp only at hyR; omega
    exact h2 hy
  have hb : 2 ≤ b := by omega
  obtain ⟨j, hj⟩ := ht.exists_tile h2R
  have hij : i ≠ j := by
    rintro rfl
    exact h2 hj
  have hbd : ∀ c ∈ component (R a b \ t i) (x₂, 0), OnBoundary a b c →
      x₁ < bpos a b c ∧ bpos a b c < x₃ := by
    intro c hc hcb
    have := component_boundary (p := (x₁, 0)) (p' := (x₃, 0)) (q := (x₂, 0)) ha hb hR hT.2
      ⟨hR h1, Or.inr (Or.inr (Or.inl rfl))⟩ ⟨hR h3, Or.inr (Or.inr (Or.inl rfl))⟩ h1 h3
      ⟨h2R, Or.inr (Or.inr (Or.inl rfl))⟩ h2 (by simpa [CaseI.bpos_bottom])
      (by simpa [CaseI.bpos_bottom]) hcb hc
    simpa only [CaseI.bpos_bottom] using this
  refine enclosure_not_congruent hR (ht.subset_R j) (ht.tile_isPolyomino hP j).2
    (ht.disjoint i j hij) hj ?_ ?_ (fun _ => ⟨x₁, h1⟩) (ht.tiles_congruent i j)
  · intro c hc
    have hcR := CaseI.component_subset_R hc
    have hcR' := mem_R.1 hcR
    refine ⟨exists_right_of_component hc fun hend => ?_,
      exists_above_of_component hc fun hend => ?_⟩
    · have h := hbd _ hend (CaseI.onBoundary_right hcR)
      have h' := CaseI.bpos_right (a := a) hcR'.2.1 hcR'.2.2
      omega
    · have h := hbd _ hend (CaseI.onBoundary_top hcR)
      have h' := CaseI.bpos_top hb hcR'.1.1 hcR'.1.2
      omega
  · rintro ⟨⟨x, y⟩, hc, hx⟩
    dsimp only at hx
    subst hx
    have hcR := CaseI.component_subset_R hc
    have hcR' := mem_R.1 hcR
    dsimp only at hcR'
    have h := hbd _ hc ⟨hcR, Or.inl rfl⟩
    exfalso
    rcases eq_or_lt_of_le hcR'.2.1 with h0 | h0
    · rw [← h0, CaseI.bpos_bottom] at h
      omega
    · have h' := CaseI.bpos_left ha h0 hcR'.2.2
      omega

/-- Proposition 57 (a): the internal statement behind the frozen
`proposition57a_sides_are_intervals`, for any number of tiles. Source:
`report-4.md`, Proposition 57 (a) (line 507): "Every tile meets every side of R in
an interval of cells (possibly empty)." Proof idea: `bottom_is_interval` for the
tilings `IsTiling.flipY`, `IsTiling.transpose` and both. -/
theorem sides_are_intervals (P : Finset Cell) (hP : IsPolyomino P) (k : ℕ) (a b : ℤ)
    (t : Fin k → Finset Cell) (ht : IsTiling P a b t) (i : Fin k) :
    RowInterval (t i) 0 ∧ RowInterval (t i) (b - 1) ∧
      ColInterval (t i) 0 ∧ ColInterval (t i) (a - 1) := by
  have hmir := bottom_is_interval P hP k a b _ ht.flipY i
  have htr := bottom_is_interval P hP k b a _ ht.transpose i
  have hmt := bottom_is_interval P hP k b a _ ht.flipX.transpose i
  refine ⟨bottom_is_interval P hP k a b t ht i, ?_, ?_, ?_⟩
  · intro x₁ x₂ x₃ h12 h23 h1 h3
    have h := hmir x₁ x₂ x₃ h12 h23 (CaseI.mem_image_flipY.2 (by simpa using h1))
      (CaseI.mem_image_flipY.2 (by simpa using h3))
    simpa using CaseI.mem_image_flipY.1 h
  · intro y₁ y₂ y₃ h12 h23 h1 h3
    exact CaseI.mem_image_transpose.1 (htr y₁ y₂ y₃ h12 h23
      (CaseI.mem_image_transpose.2 h1) (CaseI.mem_image_transpose.2 h3))
  · intro y₁ y₂ y₃ h12 h23 h1 h3
    have h := hmt y₁ y₂ y₃ h12 h23
      (CaseI.mem_image_transpose.2 (CaseI.mem_image_flipX.2 (by simpa using h1)))
      (CaseI.mem_image_transpose.2 (CaseI.mem_image_flipX.2 (by simpa using h3)))
    simpa using CaseI.mem_image_flipX.1 (CaseI.mem_image_transpose.1 h)

/-- A tile that meets the bottom and the left side holds the corner cell `(0, 0)`
between them, for any number of tiles. This is the common step of Proposition 57
(b) and Corollary 59 (`report-4.md`, lines 519 and 544): the tile cuts off the
corner, and the tile on the corner would be smaller in both directions. Case (I)
is not used. -/
theorem corner_mem_of_bottom_left {P : Finset Cell} (hP : IsPolyomino P) {k : ℕ} {a b : ℤ}
    {t : Fin k → Finset Cell} (ht : IsTiling P a b t) {i : Fin k} {x y : ℤ}
    (hx : (x, 0) ∈ t i) (hy : (0, y) ∈ t i) : ((0, 0) : Cell) ∈ t i := by
  by_contra h0
  have hT := ht.tile_isPolyomino hP i
  have hR := ht.subset_R i
  have hxR := mem_R.1 (hR hx)
  have hyR := mem_R.1 (hR hy)
  dsimp only at hxR hyR
  have hx0 : 0 < x := lt_of_le_of_ne hxR.1.1 (by rintro rfl; exact h0 hx)
  have hy0 : 0 < y := lt_of_le_of_ne hyR.2.1 (by rintro rfl; exact h0 hy)
  have ha : 2 ≤ a := by omega
  have hb : 2 ≤ b := by omega
  have h0R : ((0, 0) : Cell) ∈ R a b :=
    mem_R.2 ⟨⟨le_rfl, by dsimp only; omega⟩, le_rfl, by dsimp only; omega⟩
  obtain ⟨j, hj⟩ := ht.exists_tile h0R
  have hij : i ≠ j := by
    rintro rfl
    exact h0 hj
  have hleft := CaseI.bpos_left ha hy0 hyR.2.2
  have hbd : ∀ c ∈ component (R a b \ t i) (0, 0), OnBoundary a b c →
      bpos a b c < x ∨ bpos a b (0, y) < bpos a b c := by
    intro c hc hcb
    have := component_boundary_outer (p := (x, 0)) (p' := (0, y)) (q := (0, 0)) ha hb hR hT.2
      ⟨hR hx, Or.inr (Or.inr (Or.inl rfl))⟩ ⟨hR hy, Or.inl rfl⟩ hx hy
      (by rw [CaseI.bpos_bottom]; omega) ⟨h0R, Or.inl rfl⟩ h0
      (Or.inl (by rw [CaseI.bpos_bottom, CaseI.bpos_bottom]; exact hx0)) hcb hc
    rwa [CaseI.bpos_bottom] at this
  refine enclosure_not_congruent hR (ht.subset_R j) (ht.tile_isPolyomino hP j).2
    (ht.disjoint i j hij) hj ?_ (fun _ => ⟨y, hy⟩) (fun _ => ⟨x, hx⟩) (ht.tiles_congruent i j)
  intro c hc
  have hcR := CaseI.component_subset_R hc
  have hcR' := mem_R.1 hcR
  refine ⟨exists_right_of_component hc fun hend => ?_,
    exists_above_of_component hc fun hend => ?_⟩
  · have h := hbd _ hend (CaseI.onBoundary_right hcR)
    have h' := CaseI.bpos_right (a := a) hcR'.2.1 hcR'.2.2
    omega
  · have h := hbd _ hend (CaseI.onBoundary_top hcR)
    have h' := CaseI.bpos_top hb hcR'.1.1 hcR'.1.2
    omega

/-- A tile that meets two adjacent sides holds the corner cell between them, for
any number of tiles and without case (I): `corner_mem_of_bottom_left` for the
images of the tiling under the symmetries of the rectangle. -/
theorem corner_mem_of_adjacent_sides {P : Finset Cell} (hP : IsPolyomino P) {k : ℕ} {a b : ℤ}
    {t : Fin k → Finset Cell} (ht : IsTiling P a b t) {i : Fin k} (s : Fin 4)
    (hs : Meets (t i) (side a b s)) (hs' : Meets (t i) (side a b (s + 1))) :
    corner a b (s + 1) ∈ t i := by
  obtain ⟨⟨x, y⟩, hc, hcs⟩ := hs
  obtain ⟨⟨x', y'⟩, hd, hds⟩ := hs'
  fin_cases s
  · obtain rfl : y = 0 := (mem_bottomRow.1 hcs).2
    obtain rfl : x' = a - 1 := (mem_rightCol.1 hds).2
    have h := corner_mem_of_bottom_left hP ht.flipX (i := i) (x := a - 1 - x) (y := y')
      (CaseI.mem_image_flipX.2 (by simpa using hc))
      (CaseI.mem_image_flipX.2 (by simpa using hd))
    simpa using CaseI.mem_image_flipX.1 h
  · obtain rfl : x = a - 1 := (mem_rightCol.1 hcs).2
    obtain rfl : y' = b - 1 := (mem_topRow.1 hds).2
    have h := corner_mem_of_bottom_left hP ht.halfTurn (i := i) (x := a - 1 - x')
      (y := b - 1 - y)
      (CaseI.mem_image_halfTurn.2 (by simpa using hd))
      (CaseI.mem_image_halfTurn.2 (by simpa using hc))
    simpa using CaseI.mem_image_halfTurn.1 h
  · obtain rfl : y = b - 1 := (mem_topRow.1 hcs).2
    obtain rfl : x' = 0 := (mem_leftCol.1 hds).2
    have h := corner_mem_of_bottom_left hP ht.flipY (i := i) (x := x) (y := b - 1 - y')
      (CaseI.mem_image_flipY.2 (by simpa using hc))
      (CaseI.mem_image_flipY.2 (by simpa using hd))
    simpa using CaseI.mem_image_flipY.1 h
  · obtain rfl : x = 0 := (mem_leftCol.1 hcs).2
    obtain rfl : y' = 0 := (mem_bottomRow.1 hds).2
    exact corner_mem_of_bottom_left hP ht hd hc

/-- Proposition 57 (b), one case of eight: the tile holding the corner `(a - 1, 0)`
has no cell in the left column. Source: `report-4.md`, Proposition 57 (b) (line
508) and its proof in full (line 519); this is the mirror image of the case "T_1
has a cell p' = (a - 1, y)" there, chosen because its directions are those of
`enclosure` (`e` = right, `f` = up): the cut-off region holds `(0, 0)`. Proof:
`corner_mem_of_bottom_left` puts the corner `(0, 0)` in the same tile. -/
theorem corner_tile_avoids_far_column (P : Finset Cell) (hP : IsPolyomino P)
    (hnr : ¬ IsRectangular P) (a b : ℤ) (t : Fin 5 → Finset Cell)
    (ht : IsTiling P a b t) (hI : CornersInDistinctTiles a b t) (i : Fin 5)
    (hi : (a - 1, 0) ∈ t i) (y : ℤ) : (0, y) ∉ t i := by
  intro hy
  have h0 := corner_mem_of_bottom_left hP ht hi hy
  have _ := hnr -- not needed: the corner tiles are distinct by case (I)
  exact absurd (hI i 0 1 h0 hi) (by decide)

/-- The corner `j` lies on the sides `j - 1` and `j`. -/
theorem CaseI.corner_mem_sides {a b : ℤ} {j : Fin 4} (h : corner a b j ∈ R a b) :
    corner a b j ∈ side a b j ∧ corner a b j ∈ side a b (j - 1) := by
  fin_cases j
  · exact ⟨mem_bottomRow.2 ⟨h, rfl⟩, mem_leftCol.2 ⟨h, rfl⟩⟩
  · exact ⟨mem_rightCol.2 ⟨h, rfl⟩, mem_bottomRow.2 ⟨h, rfl⟩⟩
  · exact ⟨mem_topRow.2 ⟨h, rfl⟩, mem_rightCol.2 ⟨h, rfl⟩⟩
  · exact ⟨mem_leftCol.2 ⟨h, rfl⟩, mem_topRow.2 ⟨h, rfl⟩⟩

/-- Proposition 57 (b): the internal statement behind the frozen
`proposition57b_corner_tile_sides`. Source: `report-4.md`, Proposition 57 (b)
(line 508): "A corner tile meets only the two sides at its corner." Proof: a side
not at the corner `j` is adjacent to one that is, so `corner_mem_of_adjacent_sides`
puts a second corner cell in the tile. -/
theorem corner_tile_sides (P : Finset Cell) (hP : IsPolyomino P)
    (hnr : ¬ IsRectangular P) (a b : ℤ) (t : Fin 5 → Finset Cell)
    (ht : IsTiling P a b t) (hI : CornersInDistinctTiles a b t)
    (i : Fin 5) (j : Fin 4) (hj : corner a b j ∈ t i)
    (s : Fin 4) (hs : Meets (t i) (side a b s)) :
    corner a b j ∈ side a b s := by
  have _ := hnr -- not needed
  obtain ⟨hjs, hjs'⟩ := CaseI.corner_mem_sides (ht.subset_R i hj)
  have key : s = j ∨ s = j - 1 ∨ s = j + 1 ∨ s + 1 = j - 1 := by
    clear * -
    revert s j
    decide
  rcases key with rfl | rfl | rfl | h
  · exact hjs
  · exact hjs'
  · have h := hI i _ _ hj (corner_mem_of_adjacent_sides hP ht j ⟨_, hj, hjs⟩ hs)
    exact absurd h (by clear * -; revert j; decide)
  · have h' := hI i _ _ hj (corner_mem_of_adjacent_sides hP ht s hs (h ▸ ⟨_, hj, hjs'⟩))
    rw [h] at h'
    exact absurd h' (by clear * -; revert j; decide)

/-! ## Corollary 59: two adjacent sides -/

/-- Corollary 59, one case of four: the free tile does not meet both the left and
the bottom side. Source: `report-4.md`, Corollary 59 (lines 542-544): "A path in
T_5 from one to the other cuts off the corner (0, 0), so T_1 (Lemma 56) ... each
passes a cell of the path: the cell has a path cell strictly to its right and one
strictly above. T_5 has a cell in column 0 and one in row 0". -/
theorem free_tile_not_left_and_bottom (P : Finset Cell) (hP : IsPolyomino P)
    (hnr : ¬ IsRectangular P) (a b : ℤ) (t : Fin 5 → Finset Cell)
    (ht : IsTiling P a b t) (hI : CornersInDistinctTiles a b t) (i : Fin 5)
    (hi : ∀ j : Fin 4, corner a b j ∉ t i) (hl : Meets (t i) (leftCol a b))
    (hb : Meets (t i) (bottomRow a b)) : False := by
  have _ := hnr -- not needed, and neither is case (I)
  have _ := hI
  exact hi 0 (corner_mem_of_adjacent_sides hP ht 3 hl hb)

/-- Corollary 59, two adjacent sides: the free tile does not meet two adjacent
sides. Proof: `corner_mem_of_adjacent_sides`. -/
theorem free_tile_not_adjacent (P : Finset Cell) (hP : IsPolyomino P)
    (hnr : ¬ IsRectangular P) (a b : ℤ) (t : Fin 5 → Finset Cell)
    (ht : IsTiling P a b t) (hI : CornersInDistinctTiles a b t) (i : Fin 5)
    (hi : ∀ j : Fin 4, corner a b j ∉ t i) (s : Fin 4) (hs : Meets (t i) (side a b s))
    (hs' : Meets (t i) (side a b (s + 1))) : False := by
  have _ := hnr -- not needed, and neither is case (I)
  have _ := hI
  exact hi (s + 1) (corner_mem_of_adjacent_sides hP ht s hs hs')

end PolyominoOddOrder
