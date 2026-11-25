module

public import PolyominoOddOrder.CaseII

/-!
# The bridge from the search families to tilings (`SearchBridge.lean`)

Blueprint unit B. Theorem 21 of `report-3.md` section 2: if no tuple of the
five search families has a proper solution that is not a rectangle, then no
rectangle is tiled by exactly 3 or exactly 5 congruent copies of a
non-rectangular polyomino with `n` cells.

The report proves Theorem 21 before case (II) is closed, so it needs all five
families. This library has Theorem 62 (`three_copy`) and Corollary 63
(`corners_in_distinct_tiles`) as statements of its own, and with them only
family `I(5)` is needed: 3 copies are excluded outright, and a 5-copy tiling is
in case (I), where Lemma 15 (a) makes the tile on the corner cell `(0, 0)` a
proper solution of a tuple of `I(5)`. The hypothesis about `H1(5)`, `H2(5)`,
`H1(3)`, `H2(3)` and the injectivity of the numbering are then not used.
`BLUEPRINT.md` describes the report's own route (Lemmas 13, 14 and 15 (b), (c))
as the second choice, should case (II) not close.

Sources: `report-3.md`, section 1 (placements, solutions, family I; lines
30-63), section 2, Lemma 15 (a) and its proof (lines 80-106), Theorem 21 (lines
162-173). Commit `e5ca51d`.
-/

@[expose] public section

namespace PolyominoOddOrder

/-! ## Placements and isometries -/

/-- The placement of the box `R w h` that is the same map as the isometry `g`:
the switches of `g` choose `s_t`, and the translation absorbs the constants
`w - 1`, `h - 1` in the formulas of `boxSymm`. Source: `report-3.md`, section 1
(lines 33-41), the list of `s_0, ..., s_7`. -/
def GridIso.toPlacement (g : GridIso) (w h : ℤ) : Placement :=
  ⟨match g.swap, g.negX, g.negY with
    | false, false, false => 0
    | false, true, false => 1
    | false, false, true => 2
    | false, true, true => 3
    | true, false, false => 4
    | true, true, false => 5
    | true, false, true => 6
    | true, true, true => 7,
    g.shift.1 - (if g.negX then (if g.swap then h else w) - 1 else 0),
    g.shift.2 - (if g.negY then (if g.swap then w else h) - 1 else 0)⟩

/-- `g.toPlacement w h` and `g` are the same map of cells. -/
theorem GridIso.toPlacement_apply (g : GridIso) (w h : ℤ) (c : Cell) :
    (g.toPlacement w h).apply w h c = g.apply c := by
  obtain ⟨sw, nx, ny, s⟩ := g
  cases sw <;> cases nx <;> cases ny <;> refine Prod.ext ?_ ?_ <;>
    simp [GridIso.toPlacement, Placement.apply, boxSymm, GridIso.apply] <;> ring

/-- A placement is an injective map of cells ("it stands for the injective map
g(u) = s_t(u) + (x, y)", `report-3.md`, section 1, line 42). -/
theorem Placement.apply_injective (p : Placement) (w h : ℤ) :
    Function.Injective (p.apply w h) := by
  obtain ⟨t, x, y⟩ := p
  intro u v huv
  have h1 := congrArg Prod.fst huv
  have h2 := congrArg Prod.snd huv
  fin_cases t <;> simp [Placement.apply, boxSymm] at h1 h2 <;>
    exact Prod.ext (by omega) (by omega)

/-- The cell `g_m^{-1}(c)` of a solution is in the solution: if `c` is in the
image of `X` under the entry of index `j` and `X` lies in the box, then
`preimageAt w h g j c` is inside `X`. Source: `report-3.md`, proof of Lemma 15
(a) (lines 105-106): "g_i^{-1} of the corner cell of T_i is in P because that
corner cell is in T_i = g_i(P)". -/
theorem preimageAt_subset {w h : ℤ} {k : ℕ} (g : Fin k → Placement) (i : Fin k)
    {X : Finset Cell} {c : Cell} (hc : c ∈ X.image ((g i).apply w h)) :
    preimageAt w h g (i : ℕ) c ⊆ X := by
  intro u hu
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
  simp only [preimageAt, Finset.mem_biUnion, Finset.mem_univ, true_and] at hu
  obtain ⟨i', hu⟩ := hu
  by_cases hi : (i' : ℕ) = (i : ℕ)
  · obtain rfl : i' = i := Fin.ext hi
    simp only [↓reduceIte] at hu
    have hux := (Finset.mem_filter.1 hu).2
    rwa [(g i').apply_injective w h hux]
  · simp only [hi, ↓reduceIte] at hu
    exact absurd hu (Finset.notMem_empty u)

/-! ## The two inequalities of the boxes -/

/-- A non-empty set that is not rectangular has fewer cells than its box
("P is not B, so w h > n", `report-3.md`, proof of Lemma 15 (a), line 101). -/
theorem card_lt_of_not_isRectangular {S : Finset Cell} (hS : S.Nonempty)
    (h : ¬ IsRectangular S) : (S.card : ℤ) < width S * height S := by
  have hle : (S.card : ℤ) ≤ width S * height S := by
    have hc := Finset.card_le_card (subset_boundingBox S)
    rw [boundingBox, Finset.card_product] at hc
    simp only [width, height]
    exact_mod_cast hc
  exact lt_of_le_of_ne hle fun he => h ((isRectangular_iff_card hS).2 he)

/-- "A connected set with box R(w, h) has at least w + h - 1 cells"
(`report-3.md`, proof of Lemma 15 (a), line 102). The report gives no proof. One
that works on the grid: list the cells so that each one after the first is next
to an earlier one; a new cell shares its row or its column with that neighbour,
so it adds at most one to (number of columns) + (number of rows). -/
theorem EdgeConnected.width_add_height_le_card {S : Finset Cell} (hS : EdgeConnected S)
    (hne : S.Nonempty) : width S + height S - 1 ≤ (S.card : ℤ) := by
  have hx : xSpan S = S.image Prod.fst := by
    ext x
    rw [mem_xSpan, Finset.mem_image]
    constructor
    · rintro ⟨c, hc, d, hd, h1, h2⟩
      obtain ⟨y, hy⟩ := hS.exists_in_col hc hd h1 h2
      exact ⟨(x, y), hy, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, c, hc, le_rfl, le_rfl⟩
  have hy : ySpan S = S.image Prod.snd := by
    ext y
    rw [mem_ySpan, Finset.mem_image]
    constructor
    · rintro ⟨c, hc, d, hd, h1, h2⟩
      obtain ⟨x, hx⟩ := hS.exists_in_row hc hd h1 h2
      exact ⟨(x, y), hx, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, c, hc, le_rfl, le_rfl⟩
  -- A largest subset with the bound is all of `S`: a cell next to it could be added.
  have hw : (S.image Prod.fst).card + (S.image Prod.snd).card ≤ S.card + 1 := by
    obtain ⟨c₀, hc₀⟩ := hne
    obtain ⟨A, hA, hmax⟩ := Finset.exists_max_image
      (S.powerset.filter fun A => A.Nonempty ∧
        (A.image Prod.fst).card + (A.image Prod.snd).card ≤ A.card + 1)
      Finset.card ⟨{c₀}, by simp [hc₀]⟩
    obtain ⟨hAS, ⟨c, hc⟩, hAc⟩ : A ⊆ S ∧ A.Nonempty ∧
        (A.image Prod.fst).card + (A.image Prod.snd).card ≤ A.card + 1 := by
      simpa using hA
    have hstep : ∀ x ∈ A, ∀ y ∈ S, Adj x y → y ∈ A := by
      intro x hxA y hyS hxy
      by_contra hyA
      have hcard := Finset.card_insert_of_notMem hyA
      have hb : ((insert y A).image Prod.fst).card + ((insert y A).image Prod.snd).card
          ≤ (insert y A).card + 1 := by
        rw [Finset.image_insert, Finset.image_insert, hcard]
        have h1 := Finset.card_insert_le y.1 (A.image Prod.fst)
        have h2 := Finset.card_insert_le y.2 (A.image Prod.snd)
        rcases hxy with ⟨h, -⟩ | ⟨h, -⟩
        · have hm : y.1 ∈ A.image Prod.fst := h ▸ Finset.mem_image_of_mem Prod.fst hxA
          rw [Finset.insert_eq_of_mem hm]
          omega
        · have hm : y.2 ∈ A.image Prod.snd := h ▸ Finset.mem_image_of_mem Prod.snd hxA
          rw [Finset.insert_eq_of_mem hm]
          omega
      have := hmax (insert y A) (Finset.mem_filter.2
        ⟨Finset.mem_powerset.2 (Finset.insert_subset hyS hAS), Finset.insert_nonempty y A, hb⟩)
      omega
    have hSA : S ⊆ A := by
      intro d hd
      have hr := hS c (hAS hc) d hd
      induction hr with
      | refl => exact hc
      | tail _ hyz ih => exact hstep _ (ih hyz.1) _ hyz.2.1 hyz.2.2
    rwa [Finset.Subset.antisymm hAS hSA] at hAc
  simp only [width, height, hx, hy]
  omega

/-! ## A tile as a solution (Remark 1.1 (a) and Lemma 15 (a)) -/

/-- The tile on the corner cell `(0, 0)` lies in the box `R w h` of its own
dimensions ("(0, 0) is in P and ... it is the lower-left cell of B = box(P)",
`report-3.md`, proof of Lemma 15 (a), lines 99-100). -/
theorem IsTiling.corner_tile_subset_box {P : Finset Cell} {a b : ℤ} {k : ℕ}
    {t : Fin k → Finset Cell} (ht : IsTiling P a b t) {i₀ : Fin k}
    (h0 : (0, 0) ∈ t i₀) :
    boundingBox (t i₀) = R (width (t i₀)) (height (t i₀)) := by
  have hne : (t i₀).Nonempty := ⟨_, h0⟩
  obtain ⟨lo, hi, hlh, hx, ⟨y, hy⟩, -⟩ := xSpan_eq_Icc hne
  obtain ⟨lo', hi', hlh', hx', ⟨x, hx2⟩, -⟩ := ySpan_eq_Icc hne
  have h1 := (mem_R.1 (ht.subset_R i₀ hy)).1.1
  have h2 := (mem_R.1 (ht.subset_R i₀ hx2)).2.1
  have h3 : (0 : ℤ) ∈ xSpan (t i₀) := mem_xSpan.2 ⟨_, h0, _, h0, le_rfl, le_rfl⟩
  have h4 : (0 : ℤ) ∈ ySpan (t i₀) := mem_ySpan.2 ⟨_, h0, _, h0, le_rfl, le_rfl⟩
  rw [hx, Finset.mem_Icc] at h3
  rw [hx', Finset.mem_Icc] at h4
  simp only at h1 h2
  ext c
  rw [mem_boundingBox, mem_R, width, height, hx, hx', Finset.mem_Icc, Finset.mem_Icc,
    Int.card_Icc, Int.card_Icc]
  omega

/-- Every tile is the image of the tile on `(0, 0)` under a placement of its
box, and the tile on `(0, 0)` under the placement `(0, 0, 0)`. Source:
`report-3.md`, Remark 1.1 (a) as used in the proof of Lemma 15 (a) (lines
102-104): "P is a solution of a tuple with g_1 = (0, 0, 0)". The placement of
`t i` is `GridIso.toPlacement` of an isometry carrying `t i₀` onto `t i`; its
image of the box is `box(t i)`, inside `R a b`. -/
theorem IsTiling.exists_placements {P : Finset Cell} {a b : ℤ} {k : ℕ}
    {t : Fin k → Finset Cell} (ht : IsTiling P a b t) {i₀ : Fin k}
    (h0 : (0, 0) ∈ t i₀) :
    ∃ g : Fin k → Placement, g i₀ = ⟨0, 0, 0⟩ ∧
      (∀ i, (t i₀).image ((g i).apply (width (t i₀)) (height (t i₀))) = t i) ∧
      ∀ i, IsPlacement a b (width (t i₀)) (height (t i₀)) (g i) := by
  have hκ : ∀ i, ∃ κ : GridIso, (i = i₀ → κ = GridIso.one) ∧
      (t i₀).image κ.apply = t i := by
    intro i
    by_cases hi : i = i₀
    · refine ⟨GridIso.one, fun _ => rfl, ?_⟩
      subst hi
      ext c
      simp
    · obtain ⟨κ, h⟩ := ht.tiles_congruent i₀ i
      exact ⟨κ, fun h' => absurd h' hi, h⟩
  choose κ hκ0 hκ using hκ
  have hap : ∀ i, ((κ i).toPlacement (width (t i₀)) (height (t i₀))).apply (width (t i₀))
      (height (t i₀)) = (κ i).apply := fun i =>
    funext fun c => GridIso.toPlacement_apply (κ i) _ _ c
  refine ⟨fun i => (κ i).toPlacement (width (t i₀)) (height (t i₀)), ?_, ?_, ?_⟩
  · simp [hκ0 i₀ rfl, GridIso.toPlacement, GridIso.one]
  · intro i
    rw [hap, hκ]
  · intro i
    rw [IsPlacement, hap, ← ht.corner_tile_subset_box h0, ← boundingBox_image, hκ]
    exact boundingBox_subset_R (ht.subset_R i)

/-- In case (I) the tiles can be named so that the tile of index `j` holds the
corner cell `corner a b j`, for `j = 0, 1, 2, 3` ("Name the tiles so that T_1
contains (0, 0) and T_2, T_3, T_4 the corner cells (a - 1, 0), (a - 1, b - 1),
(0, b - 1)", `report-3.md`, proof of Lemma 15 (a), lines 97-98). -/
theorem IsTiling.exists_corner_order {P : Finset Cell} {a b : ℤ}
    {t : Fin 5 → Finset Cell} (ht : IsTiling P a b t) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hI : CornersInDistinctTiles a b t) :
    ∃ e : Fin 5 ≃ Fin 5, ∀ j : Fin 4, corner a b j ∈ t (e j.castSucc) := by
  have hf : ∀ j : Fin 4, ∃ i, corner a b j ∈ t i := fun j =>
    ht.exists_tile (corner_mem_R (by omega) (by omega) j)
  choose f hf using hf
  have hinj : Function.Injective f := fun j j' hjj' => hI (f j) j j' (hf j) (hjj' ▸ hf j')
  obtain ⟨m, hm⟩ : ∃ m, ∀ j, f j ≠ m := by
    by_contra hcon
    push Not at hcon
    have := Fintype.card_le_of_surjective f hcon
    simp at this
  have hsn : Function.Injective (Fin.snoc f m : Fin 5 → Fin 5) := by
    intro x y
    refine Fin.lastCases ?_ (fun x => ?_) x <;> refine Fin.lastCases ?_ (fun y => ?_) y
    · exact fun _ => rfl
    · rw [Fin.snoc_last, Fin.snoc_castSucc]
      exact fun h => absurd h.symm (hm y)
    · rw [Fin.snoc_last, Fin.snoc_castSucc]
      exact fun h => absurd h (hm x)
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact fun h => congrArg _ (hinj h)
  refine ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hsn), fun j => ?_⟩
  simpa using hf j

/-- Lemma 15 (a) for `k = 5`, with `a <= b` already arranged. Source:
`report-3.md`, Lemma 15 (a) (lines 85-87):

> (a) Suppose k >= 4 and the four corner cells lie in four distinct tiles. Then, after
> transposing the rectangle if necessary, the rectangle is R(a, b) with 2 <= a <= b and
> the tile on the corner cell (0, 0), a polyomino congruent to P, is a proper solution of a tuple of I(k).

The solution `X` is the tile on `(0, 0)`, so it is not rectangular; with five
tiles the condition on the order of `g_5, ..., g_k` is empty. -/
theorem familyI_of_corners (num : Placement → ℕ) (P : Finset Cell) (hP : IsPolyomino P)
    (hnr : ¬ IsRectangular P) (a b : ℤ) (hab : a ≤ b) (t : Fin 5 → Finset Cell)
    (ht : IsTiling P a b t) (hI : CornersInDistinctTiles a b t) :
    ∃ (w h : ℤ) (X : Finset Cell) (g : Fin 5 → Placement),
      FamilyI 5 num P.card a b w h g ∧
        IsProperSolution a b w h g (knownI a b w h g) X ∧ ¬ IsRectangular X := by
  obtain ⟨ha, hb⟩ := ht.two_le hP hnr (by norm_num)
  obtain ⟨e, he⟩ := ht.exists_corner_order ha hb hI
  have ht' := ht.reindex e
  set t' : Fin 5 → Finset Cell := fun i => t (e i) with ht'def
  have h0 : (0, 0) ∈ t' 0 := he 0
  have h1 : corner a b 1 ∈ t' 1 := he 1
  have h2 : corner a b 2 ∈ t' 2 := he 2
  have h3 : corner a b 3 ∈ t' 3 := he 3
  have hpoly := ht'.tile_isPolyomino hP 0
  have hnr' := ht'.tile_not_isRectangular hnr 0
  have hcard : (t' 0).card = P.card := (ht'.congruent 0).card_eq
  obtain ⟨g, hg0, hgt, hgp⟩ := ht'.exists_placements h0
  have hsub : t' 0 ⊆ R (width (t' 0)) (height (t' 0)) := by
    rw [← ht'.corner_tile_subset_box h0]
    exact subset_boundingBox _
  have hmem : ∀ (i : Fin 5) (c : Cell), c ∈ t' i →
      c ∈ (t' 0).image ((g i).apply (width (t' 0)) (height (t' 0))) := by
    intro i c hc
    rwa [hgt i]
  have hbox : ∀ (i : Fin 5) (c : Cell), c ∈ t' i →
      c ∈ (R (width (t' 0)) (height (t' 0))).image
        ((g i).apply (width (t' 0)) (height (t' 0))) := fun i c hc =>
    Finset.image_subset_image hsub (hmem i c hc)
  refine ⟨width (t' 0), height (t' 0), t' 0, g, ⟨by norm_num, ?_, ?_, ha, hab, ?_, ?_, ?_, ?_,
    hgp, ?_, ?_, ?_, ?_, ?_⟩, ⟨⟨hsub, ?_, ?_⟩, hpoly.2, ?_⟩, hnr'⟩
  · exact hP.1.card_pos
  · have hm : ((5 * P.card : ℕ) : ℤ) = ((a.toNat * b.toNat : ℕ) : ℤ) :=
      congrArg _ ht.card_mul
    push_cast at hm
    rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)] at hm
    push_cast
    exact hm.symm
  · exact width_le_of_subset_R (ht'.subset_R 0) (by omega)
  · exact height_le_of_subset_R (ht'.subset_R 0) (by omega)
  · rw [← hcard]
    exact card_lt_of_not_isRectangular hpoly.1 hnr'
  · rw [← hcard]
    exact hpoly.2.width_add_height_le_card hpoly.1
  · intro i hi
    obtain rfl : i = 0 := Fin.ext hi
    exact hg0
  · intro i hi
    obtain rfl : i = 1 := Fin.ext hi
    exact hbox 1 _ h1
  · intro i hi
    obtain rfl : i = 2 := Fin.ext hi
    exact hbox 2 _ h2
  · intro i hi
    obtain rfl : i = 3 := Fin.ext hi
    exact hbox 3 _ h3
  · intro i j hi hij
    have := j.isLt
    have : (i : ℕ) < j := hij
    omega
  · intro i j hij
    rw [hgt i, hgt j]
    exact ht'.disjoint i j hij
  · simp only [hgt]
    exact ht'.cover
  · have k1 := preimageAt_subset g 1 (hmem 1 _ h1)
    have k2 := preimageAt_subset g 2 (hmem 2 _ h2)
    have k3 := preimageAt_subset g 3 (hmem 3 _ h3)
    exact Finset.union_subset (Finset.union_subset (Finset.union_subset
      (Finset.singleton_subset_iff.2 h0) k1) k2) k3

/-! ## Theorem 21 -/

/-- Theorem 21: the internal statement behind the frozen
`theorem21_search_bridge`. Source: `report-3.md`, section 2, Theorem 21 (lines
164-167). Three copies: Theorem 62. Five copies: transpose if `a > b`; the
tiling is in case (I) by Corollary 63, and Lemma 15 (a) gives a proper solution
of a tuple of `I(5)` that is not a rectangle. -/
theorem search_bridge (num : Placement → ℕ) (_hnum : Function.Injective num) (n : ℕ)
    (hsearch : ¬ ∃ (a b w h : ℤ) (X : Finset Cell),
      IsSearchSolution num n a b w h X ∧ ¬ IsRectangular X)
    (P : Finset Cell) (hP : IsPolyomino P) (hnr : ¬ IsRectangular P) (hn : P.card = n) :
    (∀ (a b : ℤ) (t : Fin 3 → Finset Cell), ¬ IsTiling P a b t) ∧
      (∀ (a b : ℤ) (t : Fin 5 → Finset Cell), ¬ IsTiling P a b t) := by
  refine ⟨fun a b t => three_copy P hP hnr a b t, fun a b t ht => hsearch ?_⟩
  obtain ⟨a', b', t', ht', hab⟩ :
      ∃ (a' b' : ℤ) (t' : Fin 5 → Finset Cell), IsTiling P a' b' t' ∧ a' ≤ b' := by
    rcases le_total a b with h | h
    · exact ⟨a, b, t, ht, h⟩
    · exact ⟨b, a, _, ht.transpose, h⟩
  have hI := corners_in_distinct_tiles P hP hnr a' b' t' ht'
  obtain ⟨w, h, X, g, hF, hS, hX⟩ := familyI_of_corners num P hP hnr a' b' hab t' ht' hI
  exact ⟨a', b', w, h, X, Or.inl ⟨g, hn ▸ hF, hS⟩, hX⟩

end PolyominoOddOrder
