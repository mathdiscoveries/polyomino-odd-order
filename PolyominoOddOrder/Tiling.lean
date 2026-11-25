module

public import PolyominoOddOrder.Box

/-!
# Foundation 4: tilings (`Tiling.lean`)

Blueprint unit F. What `IsTiling` gives at once (tiles lie in the
rectangle, every cell is in exactly one tile, tiles are congruent polyominoes
with the same box dimensions up to order, `a, b >= 2` for a non-rectangular
tile), how a tiling is carried by a symmetry of the rectangle or by a
transposition (the reports' "after an isometry", "by symmetry", "mirror
image", "reflect"), and how a tiling splits along a clean line (case (II.1)).

Sources: `report.md` section 1 and the proofs of Lemmas 2 to 5 and Theorem 6;
`report-4.md` Corollary 63. Commit `e5ca51d`.
-/

@[expose] public section

namespace PolyominoOddOrder

/-! ## Corners and sides -/

/-- For `a, b >= 1` the four corner cells lie in `R a b`. -/
theorem corner_mem_R {a b : ℤ} (ha : 0 < a) (hb : 0 < b) (j : Fin 4) : corner a b j ∈ R a b := by
  fin_cases j <;> simp [mem_R] <;> omega

/-- For `a, b >= 2` the four corner cells are four different cells. -/
theorem corner_injective {a b : ℤ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    Function.Injective (corner a b) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega

namespace IsTiling

variable {P : Finset Cell} {a b : ℤ} {k : ℕ} {t : Fin k → Finset Cell}

/-- Every tile lies in the rectangle. -/
theorem subset_R (ht : IsTiling P a b t) (i : Fin k) : t i ⊆ R a b := by
  rw [← ht.cover]
  exact Finset.subset_biUnion_of_mem t (Finset.mem_univ i)

/-- Every cell of the rectangle is in a tile. -/
theorem exists_tile (ht : IsTiling P a b t) {c : Cell} (hc : c ∈ R a b) : ∃ i, c ∈ t i := by
  rw [← ht.cover] at hc
  simpa using hc

/-- A cell is in at most one tile. -/
theorem tile_unique (ht : IsTiling P a b t) {c : Cell} {i j : Fin k} (hi : c ∈ t i)
    (hj : c ∈ t j) : i = j := by
  by_contra h
  exact Finset.disjoint_left.1 (ht.disjoint i j h) hi hj

/-- Every tile is a polyomino. -/
theorem tile_isPolyomino (ht : IsTiling P a b t) (hP : IsPolyomino P) (i : Fin k) :
    IsPolyomino (t i) :=
  (ht.congruent i).isPolyomino hP

/-- Any two tiles are congruent. -/
theorem tiles_congruent (ht : IsTiling P a b t) (i j : Fin k) : Congruent (t i) (t j) :=
  (ht.congruent i).symm.trans (ht.congruent j)

/-- No tile of a non-rectangular polyomino is rectangular. -/
theorem tile_not_isRectangular (ht : IsTiling P a b t) (hnr : ¬ IsRectangular P) (i : Fin k) :
    ¬ IsRectangular (t i) :=
  fun h => hnr ((ht.congruent i).isRectangular_iff.1 h)

/-- A tiling by `P` is a tiling by any one of its tiles ("replace P by the
congruent polyomino T_1", `report.md`, Corollary 7). -/
theorem of_tile (ht : IsTiling P a b t) (i₀ : Fin k) : IsTiling (t i₀) a b t :=
  ⟨fun i => ht.tiles_congruent i₀ i, ht.disjoint, ht.cover⟩

/-- A tiling by a polyomino with at least one tile has `a, b >= 1`. -/
theorem pos (ht : IsTiling P a b t) (hP : IsPolyomino P) (hk : 0 < k) : 0 < a ∧ 0 < b := by
  obtain ⟨c, hc⟩ := (ht.tile_isPolyomino hP ⟨0, hk⟩).1
  have hcR := mem_R.1 (ht.subset_R _ hc)
  omega

/-- The area count `k |P| = a b`. -/
theorem card_mul (ht : IsTiling P a b t) : k * P.card = a.toNat * b.toNat := by
  rw [← card_R, ← ht.cover, Finset.card_biUnion fun i _ j _ hij => ht.disjoint i j hij,
    Finset.sum_congr rfl fun i _ => (ht.congruent i).card_eq]
  simp

/-- A non-rectangular polyomino tiles only rectangles with `a, b >= 2`
(`report.md` section 1, remark "Thin rectangles"). -/
theorem two_le (ht : IsTiling P a b t) (hP : IsPolyomino P) (hnr : ¬ IsRectangular P)
    (hk : 0 < k) : 2 ≤ a ∧ 2 ≤ b := by
  obtain ⟨ha, hb⟩ := ht.pos hP hk
  have hthin : ¬ (a = 1 ∨ b = 1) := fun h =>
    ht.tile_not_isRectangular hnr ⟨0, hk⟩
      ((ht.tile_isPolyomino hP ⟨0, hk⟩).2.isRectangular_of_thin (ht.subset_R _) h)
  omega

/-- All tiles have the box dimensions of the first one, up to order (`report.md`
section 1, remark "Boxes"). -/
theorem dims (ht : IsTiling P a b t) (i j : Fin k) :
    (width (t j) = width (t i) ∧ height (t j) = height (t i)) ∨
      (width (t j) = height (t i) ∧ height (t j) = width (t i)) :=
  (ht.tiles_congruent i j).dims

/-- A tiling is carried by any isometry that maps the rectangle onto a rectangle
`R a' b'`. -/
theorem map (ht : IsTiling P a b t) (g : GridIso) {a' b' : ℤ}
    (hg : (R a b).image g.apply = R a' b') :
    IsTiling P a' b' fun i => (t i).image g.apply := by
  refine ⟨fun i => ?_, fun i j hij => ?_, ?_⟩
  · exact (ht.congruent i).trans ⟨g, rfl⟩
  · exact (Finset.disjoint_image g.apply_injective).2 (ht.disjoint i j hij)
  · rw [← hg, ← ht.cover, Finset.biUnion_image]

/-- The mirror image of a tiling of `R a b`. -/
theorem flipX (ht : IsTiling P a b t) :
    IsTiling P a b fun i => (t i).image (GridIso.flipX a).apply :=
  ht.map _ (GridIso.image_R_flipX a b)

/-- The image of a tiling of `R a b` under the reflection `F`. -/
theorem flipY (ht : IsTiling P a b t) :
    IsTiling P a b fun i => (t i).image (GridIso.flipY b).apply :=
  ht.map _ (GridIso.image_R_flipY a b)

/-- The image of a tiling of `R a b` under the half turn. -/
theorem halfTurn (ht : IsTiling P a b t) :
    IsTiling P a b fun i => (t i).image (GridIso.halfTurn a b).apply :=
  ht.map _ (GridIso.image_R_halfTurn a b)

/-- The transposed tiling, of `R b a`. -/
theorem transpose (ht : IsTiling P a b t) :
    IsTiling P b a fun i => (t i).image GridIso.transpose.apply :=
  ht.map _ (GridIso.image_R_transpose a b)

/-- Renaming the tiles. -/
theorem reindex (ht : IsTiling P a b t) {k' : ℕ} (e : Fin k' ≃ Fin k) :
    IsTiling P a b fun i => t (e i) := by
  refine ⟨fun i => ht.congruent (e i), fun i j hij => ht.disjoint _ _ (e.injective.ne hij), ?_⟩
  rw [← ht.cover]
  ext c
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact e.exists_congr_left.trans (by simp)

/-- Case (II.1), lower part: if the tiles named by an injective `e : Fin m -> Fin k`
are exactly the tiles lying below the line `y = c`, and no tile crosses that line,
they tile `R a c`. Source: `report.md`, Theorem 6 (II.1) ("a horizontal grid line
splits R(a, b) into two rectangles, one tiled by 2 of the five tiles and the other
by 3") and `report-4.md`, Corollary 63 ("In (II.1) a rectangle is tiled by exactly
3 of the tiles"). -/
theorem lower_part (ht : IsTiling P a b t) {m : ℕ} (e : Fin m → Fin k)
    (he : Function.Injective e) {c : ℤ} (hc0 : 0 ≤ c) (hcb : c ≤ b)
    (hbelow : ∀ j, ∀ p ∈ t (e j), p.2 < c)
    (hrest : ∀ i, (∀ j, e j ≠ i) → ∀ p ∈ t i, c ≤ p.2) :
    IsTiling P a c fun j => t (e j) := by
  have _ := hc0 -- not needed: for `c < 0` there is nothing below the line
  refine ⟨fun j => ht.congruent (e j), fun i j hij => ht.disjoint _ _ (he.ne hij), ?_⟩
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    have hpR := mem_R.1 (ht.subset_R _ hj)
    exact mem_R.2 ⟨hpR.1, hpR.2.1, hbelow j p hj⟩
  · intro hp
    have hpR := mem_R.1 hp
    obtain ⟨i, hi⟩ := ht.exists_tile (mem_R.2 ⟨hpR.1, hpR.2.1, hpR.2.2.trans_le hcb⟩)
    by_cases h : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := h
      exact ⟨j, hi⟩
    · have := hrest i (fun j hj => h ⟨j, hj⟩) p hi
      omega

/-- Case (II.1), upper part: the tiles lying at or above the line `y = c`, moved
down by `c`, tile `R a (b - c)`. -/
theorem upper_part (ht : IsTiling P a b t) {m : ℕ} (e : Fin m → Fin k)
    (he : Function.Injective e) {c : ℤ} (hc0 : 0 ≤ c) (hcb : c ≤ b)
    (habove : ∀ j, ∀ p ∈ t (e j), c ≤ p.2)
    (hrest : ∀ i, (∀ j, e j ≠ i) → ∀ p ∈ t i, p.2 < c) :
    IsTiling P a (b - c) fun j => (t (e j)).image (GridIso.translate (0, -c)).apply := by
  have _ := hcb -- not needed: for `b < c` there is nothing above the line
  refine ⟨fun j => (ht.congruent (e j)).trans ⟨_, rfl⟩, fun i j hij => ?_, ?_⟩
  · exact (Finset.disjoint_image (GridIso.apply_injective _)).2
      (ht.disjoint _ _ (he.ne hij))
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    GridIso.translate_apply]
  constructor
  · rintro ⟨j, q, hq, rfl⟩
    have hqR := mem_R.1 (ht.subset_R _ hq)
    have hcq := habove j q hq
    rw [mem_R]
    dsimp only
    omega
  · intro hp
    have hpR := mem_R.1 hp
    have hmem : ((p.1, p.2 + c) : Cell) ∈ R a b := by
      rw [mem_R]
      dsimp only
      omega
    obtain ⟨i, hi⟩ := ht.exists_tile hmem
    by_cases h : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := h
      exact ⟨j, _, hi, by simp⟩
    · have hlt := hrest i (fun j hj => h ⟨j, hj⟩) _ hi
      dsimp only at hlt
      omega

end IsTiling

end PolyominoOddOrder
