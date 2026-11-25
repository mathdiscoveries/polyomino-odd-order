module

public import PolyominoOddOrder.CaseII3Square

/-!
# Case (II.3) does not occur for five tiles (`CaseII3.lean`)

Blueprint unit II3b. Type H2 with five tiles and `d < a`: `report-4.md`,
Corollary 42 and sections 5e (Lemma 43, Proposition 44), 5f (Lemma 45, the wall
states), 5g (Lemma 48) and 5h (Lemma 52, Propositions 53 and 54, Theorem 55). The
square box `d = a` is `CaseII3Square.lean`.

The binding statement of this file is `theorem55`. Its proof below is complete
given `theorem41` (`CaseII3Square.lean`), `counts_bottom_top`, `proposition53` and
`proposition54`.
Everything else is marked PROVISIONAL: the reports' intermediate lemma in the
coordinates of `Spine.lean`, stated in the parts that later steps use; the owner
of the file may restate it.

Not on the path to Theorem 55 and not stated here (`report-4.md`, line 476: "For
G = H section 5g is a second route to the same exclusion (Corollary 51); the wall
states of 5f are not needed for G = F"): Lemma 46, Proposition 47,
Propositions 49 and 50, Corollary 51.

Notation: `T = t i₀` on row 0, `T' = t i₁` with spine row `b - 1`; `h = b - a`;
`u_0 = colCount (t i₀) 0`, `u_1 = colCount (t i₀) (a - 1)`,
`t = rowCount (t i₀) (d - 1)`; `G = F` when `(κ i₁).negX = false` and `G = H` when
it is `true` (`TypeH2.mirror_form`). A vertical tile is a *bottom tile* when its
box starts at row `s` and a *top tile* when it starts at row `h - s`, where `s` is
the number of full bottom rows of `T`.

Commit `e5ca51d`.
-/

@[expose] public section

namespace PolyominoOddOrder

variable {a b d : ℤ} {t : Fin 5 → Finset Cell} {i₀ i₁ : Fin 5} {κ : Fin 5 → GridIso}

/-! ## Corollary 42 -/

/-! ### Working lemmas of the first half (Corollary 42 to Proposition 44) -/

/-- Coordinates of a cell of a tile. -/
private theorem low_in_R (H : TypeH2 a b d t i₀ i₁ κ) {i : Fin 5} {x y : ℤ}
    (hc : (x, y) ∈ t i) : (0 ≤ x ∧ x < a) ∧ 0 ≤ y ∧ y < b :=
  mem_R.1 (H.frame.isTiling.subset_R i hc)

/-- The cells of `T` lie in the rows `[0, d)`. -/
private theorem low_row_T (H : TypeH2 a b d t i₀ i₁ κ) {x y : ℤ} (hc : (x, y) ∈ t i₀) :
    0 ≤ y ∧ y < d := by
  have h : y ∈ ySpan (t i₀) := mem_ySpan.2 ⟨_, hc, _, hc, le_rfl, le_rfl⟩
  rwa [H.frame.rows, Finset.mem_Ico] at h

/-- The cells of `T'` lie in the rows `[b - d, b)`. -/
private theorem low_row_T' (H : TypeH2 a b d t i₀ i₁ κ) {x y : ℤ} (hc : (x, y) ∈ t i₁) :
    b - d ≤ y ∧ y < b := by
  have h := low_row_T H ((H.top_mem x y).1 hc)
  omega

/-- A vertical tile lies in its box. -/
private theorem low_box (H : TypeH2 a b d t i₀ i₁ κ) {v : Fin 5} (hv₀ : v ≠ i₀) (hv₁ : v ≠ i₁)
    {x y : ℤ} (hc : (x, y) ∈ t v) :
    ((κ v).boxX d ≤ x ∧ x < (κ v).boxX d + d) ∧
      (κ v).boxY a ≤ y ∧ y < (κ v).boxY a + a := by
  obtain ⟨-, hx, hy, -, -⟩ := H.frame.vertical_spine (H.vert v hv₀ hv₁)
  have h1 : x ∈ xSpan (t v) := mem_xSpan.2 ⟨_, hc, _, hc, le_rfl, le_rfl⟩
  have h2 : y ∈ ySpan (t v) := mem_ySpan.2 ⟨_, hc, _, hc, le_rfl, le_rfl⟩
  rw [hx, Finset.mem_Ico] at h1
  rw [hy, Finset.mem_Ico] at h2
  exact ⟨h1, h2⟩

/-- The spine of a vertical tile. -/
private theorem low_spine (H : TypeH2 a b d t i₀ i₁ κ) {v : Fin 5} (hv₀ : v ≠ i₀)
    (hv₁ : v ≠ i₁) {y : ℤ} (h1 : (κ v).boxY a ≤ y) (h2 : y < (κ v).boxY a + a) :
    ((κ v).shift.1, y) ∈ t v :=
  (H.frame.vertical_spine (H.vert v hv₀ hv₁)).1 y h1 h2

/-- Two tiles that share a cell are the same tile. -/
private theorem low_same (H : TypeH2 a b d t i₀ i₁ κ) {i j : Fin 5} {c : Cell} (hi : c ∈ t i)
    (hj : c ∈ t j) : i = j :=
  H.frame.isTiling.tile_unique hi hj

/-- Every cell of `R a b` is in `T`, in `T'` or in a vertical tile. -/
private theorem low_cases (H : TypeH2 a b d t i₀ i₁ κ) {x y : ℤ} (hx : 0 ≤ x ∧ x < a)
    (hy : 0 ≤ y ∧ y < b) :
    (x, y) ∈ t i₀ ∨ (x, y) ∈ t i₁ ∨ ∃ v, v ≠ i₀ ∧ v ≠ i₁ ∧ (x, y) ∈ t v := by
  obtain ⟨j, hj⟩ := H.frame.isTiling.exists_tile (c := (x, y)) (mem_R.2 ⟨hx, hy⟩)
  by_cases h0 : j = i₀
  · exact Or.inl (h0 ▸ hj)
  by_cases h1 : j = i₁
  · exact Or.inr (Or.inl (h1 ▸ hj))
  · exact Or.inr (Or.inr ⟨j, h0, h1, hj⟩)

/-- The box of a vertical tile is inside `R a b`, its spine is the first or the last
column of the box. -/
private theorem low_range (H : TypeH2 a b d t i₀ i₁ κ) {v : Fin 5} (hv₀ : v ≠ i₀)
    (hv₁ : v ≠ i₁) :
    (0 ≤ (κ v).boxX d ∧ (κ v).boxX d + d ≤ a) ∧
      ((κ v).negX = false → (κ v).shift.1 = (κ v).boxX d) ∧
      ((κ v).negX = true → (κ v).shift.1 = (κ v).boxX d + (d - 1)) := by
  obtain ⟨-, -, -, hx, -⟩ := H.frame.vertical_spine (H.vert v hv₀ hv₁)
  refine ⟨hx, fun h => ?_, fun h => ?_⟩
  · simp [GridIso.boxX, h]
  · simp [GridIso.boxX, h]

/-- The parts of `FullRows`: a non-negative `s`, the full rows below it, and a hole in
row `s`. -/
private theorem low_fullRows {T : Finset Cell} {s : ℤ} (hs : FullRows T a s) :
    0 ≤ s ∧ (∀ x y : ℤ, 0 ≤ x → x < a → 0 ≤ y → y < s → (x, y) ∈ T) ∧
      ∃ x : ℤ, 0 ≤ x ∧ x < a ∧ (x, s) ∉ T :=
  hs

/-- `1 <= s < d`. -/
private theorem low_s (H : TypeH2 a b d t i₀ i₁ κ) {s : ℤ} (hs : FullRows (t i₀) a s) :
    1 ≤ s ∧ s < d := by
  obtain ⟨hs0, hfull, x, hx0, hxa, hx⟩ := low_fullRows hs
  constructor
  · by_contra hlt
    obtain rfl : s = 0 := by omega
    exact hx (H.frame.row0 x hx0 hxa)
  · by_contra hlt
    obtain ⟨s', hs'1, hs'd, hs'⟩ := H.frame.exists_fullRows
    obtain ⟨-, -, z, hz0, hza, hz⟩ := low_fullRows hs'
    exact hz (hfull z s' hz0 hza (by omega) (by omega))

/-- With two vertical tiles there is a third, and no other. -/
private theorem low_third (H : TypeH2 a b d t i₀ i₁ κ) {v w : Fin 5} (hv₀ : v ≠ i₀)
    (hv₁ : v ≠ i₁) (hw₀ : w ≠ i₀) (hw₁ : w ≠ i₁) (hvw : v ≠ w) :
    ∃ u, u ≠ i₀ ∧ u ≠ i₁ ∧ u ≠ v ∧ u ≠ w ∧
      ∀ j, j = u ∨ j = i₀ ∨ j = i₁ ∨ j = v ∨ j = w := by
  have h4 : ({i₀, i₁, v, w} : Finset (Fin 5)).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hvw]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hv₁.symm, hw₁.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨H.ne.symm, hv₀.symm, hw₀.symm⟩
  obtain ⟨u, hu⟩ : ∃ u : Fin 5, u ∉ ({i₀, i₁, v, w} : Finset (Fin 5)) := by
    by_contra h
    push Not at h
    have h1 := Finset.card_le_card fun j (_ : j ∈ Finset.univ) => h j
    rw [Finset.card_univ, Fintype.card_fin] at h1
    omega
  have huniv := Finset.eq_univ_of_card (insert u ({i₀, i₁, v, w} : Finset (Fin 5)))
    (by rw [Finset.card_insert_of_notMem hu, h4, Fintype.card_fin])
  have hall : ∀ j, j = u ∨ j = i₀ ∨ j = i₁ ∨ j = v ∨ j = w := by
    intro j
    have hj : j ∈ insert u ({i₀, i₁, v, w} : Finset (Fin 5)) := huniv ▸ Finset.mem_univ j
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hj
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu
  exact ⟨u, hu.1, hu.2.1, hu.2.2.1, hu.2.2.2, hall⟩

/-- The three vertical tiles. -/
private theorem low_vertical (H : TypeH2 a b d t i₀ i₁ κ) :
    ∃ p q r : Fin 5, (p ≠ i₀ ∧ p ≠ i₁) ∧ (q ≠ i₀ ∧ q ≠ i₁) ∧ (r ≠ i₀ ∧ r ≠ i₁) ∧
      (p ≠ q ∧ p ≠ r ∧ q ≠ r) ∧ ∀ j, j ≠ i₀ → j ≠ i₁ → j = p ∨ j = q ∨ j = r := by
  obtain ⟨p, hp₀, hp₁⟩ := exists_vertical5 i₀ i₁
  obtain ⟨q, hq⟩ : ∃ q : Fin 5, q ∉ ({i₀, i₁, p} : Finset (Fin 5)) := by
    by_contra h
    push Not at h
    have h1 := Finset.card_le_card fun j (_ : j ∈ Finset.univ) => h j
    have h2 : ({i₀, i₁, p} : Finset (Fin 5)).card ≤ 3 := Finset.card_le_three
    rw [Finset.card_univ, Fintype.card_fin] at h1
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq
  obtain ⟨r, hr₀, hr₁, hrp, hrq, hall⟩ := low_third H hp₀ hp₁ hq.1 hq.2.1 (Ne.symm hq.2.2)
  refine ⟨p, q, r, ⟨hp₀, hp₁⟩, ⟨hq.1, hq.2.1⟩, ⟨hr₀, hr₁⟩, ⟨Ne.symm hq.2.2, hrp.symm, hrq.symm⟩,
    fun j h0 h1 => ?_⟩
  rcases hall j with h | h | h | h | h
  · exact Or.inr (Or.inr h)
  · exact absurd h h0
  · exact absurd h h1
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- A row between `T` and `T'` is covered by the boxes of the vertical tiles. -/
private theorem low_middle (H : TypeH2 a b d t i₀ i₁ κ) {x y : ℤ} (hx : 0 ≤ x ∧ x < a)
    (hy : d ≤ y ∧ y < b - d) : ∃ v, v ≠ i₀ ∧ v ≠ i₁ ∧ (x, y) ∈ t v := by
  have hd := H.frame.two_le_d
  rcases low_cases H hx (y := y) (by omega) with h | h | h
  · have := low_row_T H h
    omega
  · have := low_row_T' H h
    omega
  · exact h

/-- Corollary 42. PROVISIONAL (not used by Theorem 55 beyond `d < a`). Source:
`report-4.md`, Corollary 42 (line 335): "In case (II.3): 2 <= d < a <= min(3d, b - 2),
and every vertical tile has s <= y_i <= h - s". -/
theorem corollary42 (H : TypeH2 a b d t i₀ i₁ κ) {s : ℤ} (hs : FullRows (t i₀) a s) :
    (2 ≤ d ∧ d < a ∧ a ≤ 3 * d ∧ a ≤ b - 2) ∧
      ∀ v, v ≠ i₀ → v ≠ i₁ → s ≤ (κ v).boxY a ∧ (κ v).boxY a ≤ b - a - s := by
  obtain ⟨p, q, r, hp, hq, hr, -, hall⟩ := low_vertical H
  have hb := H.bounds hp.1 hp.2
  refine ⟨⟨hb.1, ?_, ?_, hb.2.2⟩, fun v hv₀ hv₁ => ?_⟩
  · by_contra h
    exact theorem41 H (by omega)
  · by_contra hlt
    have cov : ∀ x : ℤ, 0 ≤ x → x < a →
        ((κ p).boxX d ≤ x ∧ x < (κ p).boxX d + d) ∨
          ((κ q).boxX d ≤ x ∧ x < (κ q).boxX d + d) ∨
          ((κ r).boxX d ≤ x ∧ x < (κ r).boxX d + d) := by
      intro x hx0 hxa
      obtain ⟨v, hv₀, hv₁, hv⟩ := low_middle H (y := d) ⟨hx0, hxa⟩ (by omega)
      have hbox := (low_box H hv₀ hv₁ hv).1
      rcases hall v hv₀ hv₁ with rfl | rfl | rfl
      · exact Or.inl hbox
      · exact Or.inr (Or.inl hbox)
      · exact Or.inr (Or.inr hbox)
    have c0 := cov 0 (by omega) (by omega)
    have c1 := cov d (by omega) (by omega)
    have c2 := cov (2 * d) (by omega) (by omega)
    have c3 := cov (3 * d) (by omega) (by omega)
    omega
  · have hc := low_spine H hv₀ hv₁ (y := (κ v).boxY a) le_rfl (by omega)
    have hc' := low_spine H hv₀ hv₁ (y := (κ v).boxY a + a - 1) (by omega) (by omega)
    have hR := low_in_R H hc
    have hR' := low_in_R H hc'
    constructor
    · by_contra hlt
      exact hv₀ (low_same H hc ((low_fullRows hs).2.1 _ _ hR.1.1 hR.1.2 hR.2.1 (by omega)))
    · by_contra hlt
      refine hv₁ (low_same H hc' ((H.top_mem _ _).2
        ((low_fullRows hs).2.1 _ _ ?_ ?_ (by omega) (by omega))))
      · split <;> omega
      · split <;> omega

/-! ## Section 5e: first reductions for `d < a` -/

/-- A column met in the rows `[l, m)` exactly counts `m - l`. -/
private theorem low_colCount {S : Finset Cell} {x l m : ℤ}
    (h : ∀ y : ℤ, (x, y) ∈ S ↔ l ≤ y ∧ y < m) (hlm : l ≤ m) : colCount S x = m - l := by
  have hcol : (S.filter fun c => c.1 = x) = ({x} : Finset ℤ) ×ˢ Finset.Ico l m := by
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

/-- A connected set through a cell of row `< d` and a cell of row `>= d` has a connected
part in the rows `< d` that joins the first cell to row `d - 1`. -/
private theorem lemma43_truncate {S : Finset Cell} (hS : EdgeConnected S) {q c : Cell}
    (hq : q ∈ S) (hqd : q.2 < d) (hc : c ∈ S) (hcd : d ≤ c.2) :
    ∃ S' ⊆ S, EdgeConnected S' ∧ q ∈ S' ∧ (∀ e ∈ S', e.2 < d) ∧ ∃ x : ℤ, (x, d - 1) ∈ S' := by
  have hqA : q ∈ S.filter fun e => e.2 < d := Finset.mem_filter.2 ⟨hq, hqd⟩
  have hsub : ∀ e ∈ component (S.filter fun e => e.2 < d) q, e ∈ S ∧ e.2 < d := fun e he =>
    Finset.mem_filter.1 (mem_component.1 he).1
  refine ⟨component (S.filter fun e => e.2 < d) q, fun e he => (hsub e he).1,
    edgeConnected_component _ _, mem_component.2 ⟨hqA, Reach.refl _ _⟩,
    fun e he => (hsub e he).2, ?_⟩
  by_contra hno
  push Not at hno
  have key : ∀ e, Reach S q e → e ∈ component (S.filter fun e => e.2 < d) q := by
    intro e he
    induction he with
    | refl => exact mem_component.2 ⟨hqA, Reach.refl _ _⟩
    | @tail e₁ e₂ _ hstep ih =>
      obtain ⟨-, h2, hadj⟩ := hstep
      refine component_closed ih (Finset.mem_filter.2 ⟨h2, ?_⟩) hadj
      have h1 := (hsub e₁ ih).2
      have hne : e₁.2 ≠ d - 1 := by
        intro h
        refine hno e₁.1 ?_
        rw [← h]
        exact ih
      obtain ⟨x₁, y₁⟩ := e₁
      obtain ⟨x₂, y₂⟩ := e₂
      rw [adj_iff] at hadj
      dsimp only at h1 hne ⊢
      omega
  have := (hsub c (key c (hS q hq c hc))).2
  omega

/-- `T` meets column 0 in an interval. Source: `report-4.md`, Lemma 43 (a), proof: "the
tile of a cell (0, j) between cells of T is vertical or is T', and has a cell in a row
>= d". -/
private theorem lemma43_interval (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) :
    ColInterval (t i₀) 0 := by
  intro y₁ y₂ y₃ h12 h23 h1 h3
  by_contra h2
  obtain ⟨v, hv₀, hv₁⟩ := exists_vertical5 i₀ i₁
  have hb := H.bounds hv₀ hv₁
  have n1 : y₁ ≠ y₂ := fun h => h2 (h ▸ h1)
  have n3 : y₃ ≠ y₂ := fun h => h2 (h ▸ h3)
  have b1 := low_row_T H h1
  have b3 := low_row_T H h3
  have hpoly := fun j => (H.frame.isTiling.tile_isPolyomino H.frame.poly j).2
  -- the tile of the cell between
  have hj : ∃ j, j ≠ i₀ ∧ (0, y₂) ∈ t j ∧ ∃ c ∈ t j, d ≤ c.2 := by
    rcases low_cases H (x := 0) (y := y₂) (by omega) (by omega) with h | h | ⟨w, hw₀, hw₁, h⟩
    · exact absurd h h2
    · have hc := (H.frame.horizontal_spine H.horiz).2.2.1 0 le_rfl (by omega)
      rw [H.top] at hc
      exact ⟨i₁, H.ne, h, _, hc, by dsimp only; omega⟩
    · have hY := (H.frame.vertical_spine (H.vert w hw₀ hw₁)).2.2.2.2
      refine ⟨w, hw₀, h, _, low_spine H hw₀ hw₁ (y := (κ w).boxY a + a - 1) (by omega)
        (by omega), by dsimp only; omega⟩
  obtain ⟨j, hj0, hj2, c, hc, hcd⟩ := hj
  obtain ⟨S', hS'j, hS', hqS', hlow, x, hx⟩ :=
    lemma43_truncate (hpoly j) hj2 (by dsimp only; omega) hc hcd
  have hTsub : t i₀ ⊆ R a d := by
    rintro ⟨z, y⟩ hz
    exact mem_R.2 ⟨(low_in_R H hz).1, low_row_T H hz⟩
  have hS'sub : S' ⊆ R a d := by
    rintro ⟨z, y⟩ hz
    have h := low_in_R H (hS'j hz)
    exact mem_R.2 ⟨h.1, h.2.1, hlow _ hz⟩
  obtain ⟨e, he, he'⟩ := interlace_left (by omega) hb.1 hTsub (hpoly i₀) hS'sub hS'
    (by omega : y₁ < y₂) (by omega : y₂ < y₃) h1 h3 hqS' (q' := (x, d - 1))
    ⟨hS'sub hx, Or.inr (Or.inr (Or.inr rfl))⟩ hx
    (fun h => by have := h.2.2; dsimp only at this; omega)
  exact hj0 (low_same H (hS'j he') he)

/-- A set that meets column `x` in an interval starting at row 0 meets it in the rows
`[0, colCount S x)`. -/
private theorem lemma43_mem_col {S : Finset Cell} {x : ℤ} (hI : ColInterval S x)
    (h0 : (x, 0) ∈ S) (hnn : ∀ y : ℤ, (x, y) ∈ S → 0 ≤ y) (y : ℤ) :
    (x, y) ∈ S ↔ 0 ≤ y ∧ y < colCount S x := by
  obtain ⟨⟨x', m⟩, hm, hmax⟩ := Finset.exists_max_image (S.filter fun c => c.1 = x)
    (fun c => c.2) ⟨(x, 0), Finset.mem_filter.2 ⟨h0, rfl⟩⟩
  rw [Finset.mem_filter] at hm
  obtain ⟨hm, hx⟩ := hm
  dsimp only at hx
  subst hx
  have hmem : ∀ z : ℤ, (x', z) ∈ S ↔ 0 ≤ z ∧ z < m + 1 := by
    intro z
    constructor
    · intro hz
      have h1 := hmax (x', z) (Finset.mem_filter.2 ⟨hz, rfl⟩)
      dsimp only at h1
      exact ⟨hnn z hz, by omega⟩
    · rintro ⟨h1, h2⟩
      exact hI 0 z m h1 (by omega) h0 hm
  have hm0 := hnn m hm
  rw [low_colCount hmem (by omega), hmem]
  omega

/-- Membership in the mirror image. -/
private theorem low_mem_flipX {S : Finset Cell} {x y : ℤ} :
    (x, y) ∈ S.image (GridIso.flipX a).apply ↔ (a - 1 - x, y) ∈ S := by
  constructor
  · intro h
    obtain ⟨⟨u, v⟩, hc, he⟩ := Finset.mem_image.1 h
    rw [GridIso.flipX_apply] at he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rwa [show a - 1 - (a - 1 - u) = u by ring]
  · intro h
    refine Finset.mem_image.2 ⟨_, h, ?_⟩
    rw [GridIso.flipX_apply]
    simp

/-- Lemma 43 (a). PROVISIONAL. Source: `report-4.md`, Lemma 43 (a) (line 347): "T
meets column 0 in the rows [0, u_0) and column a - 1 in [0, u_1)". (What it says
about `T'` follows by `TypeH2.top_mem`.) -/
theorem lemma43a (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) :
    (∀ y : ℤ, (0, y) ∈ t i₀ ↔ 0 ≤ y ∧ y < colCount (t i₀) 0) ∧
      ∀ y : ℤ, (a - 1, y) ∈ t i₀ ↔ 0 ≤ y ∧ y < colCount (t i₀) (a - 1) := by
  have ha := H.frame.two_le.1
  refine ⟨lemma43_mem_col (lemma43_interval H hda) (H.frame.row0 0 le_rfl (by omega))
    fun y hy => (low_row_T H hy).1, lemma43_mem_col ?_
      (H.frame.row0 (a - 1) (by omega) (by omega)) fun y hy => (low_row_T H hy).1⟩
  intro y₁ y₂ y₃ h12 h23
  have h := lemma43_interval H.mirror hda y₁ y₂ y₃ h12 h23
  simp only [low_mem_flipX, sub_zero] at h
  exact h

/-- The bottom tiles: the vertical tiles whose box starts at row `s`. Source:
`report-4.md`, section 5e (line 343). -/
def bottomTiles (a s : ℤ) (κ : Fin 5 → GridIso) (i₀ i₁ : Fin 5) : Finset (Fin 5) :=
  Finset.univ.filter fun i => i ≠ i₀ ∧ i ≠ i₁ ∧ (κ i).boxY a = s

/-- The top tiles of type H2: the vertical tiles whose box starts at row `h - s`,
so that it ends at row `b - 1 - s`. Source: `report-4.md`, section 5e (line 343). -/
def upperTiles (a b s : ℤ) (κ : Fin 5 → GridIso) (i₀ i₁ : Fin 5) : Finset (Fin 5) :=
  Finset.univ.filter fun i => i ≠ i₀ ∧ i ≠ i₁ ∧ (κ i).boxY a = b - a - s

/-- Lemma 43 (b). PROVISIONAL. Source: `report-4.md`, Lemma 43 (b) (line 348): "T'
has no cell in row s and T none in row b - 1 - s. A bottom tile and a top tile
exist." -/
theorem lemma43b (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {s : ℤ}
    (hs : FullRows (t i₀) a s) :
    (∀ x : ℤ, (x, s) ∉ t i₁) ∧ (∀ x : ℤ, (x, b - 1 - s) ∉ t i₀) ∧
      (bottomTiles a s κ i₀ i₁).Nonempty ∧ (upperTiles a b s κ i₀ i₁).Nonempty := by
  obtain ⟨w, hw₀, hw₁⟩ := exists_vertical5 i₀ i₁
  obtain ⟨hb, hY⟩ := corollary42 H hs
  have hw := hY w hw₀ hw₁
  have hsd := low_s H hs
  have hT' : ∀ x : ℤ, (x, s) ∉ t i₁ := fun x h => by
    have := low_row_T' H h
    omega
  have hT : ∀ x : ℤ, (x, b - 1 - s) ∉ t i₀ := fun x h => by
    have := low_row_T H h
    omega
  obtain ⟨-, -, x, hx0, hxa, hx⟩ := low_fullRows hs
  refine ⟨hT', hT, ?_, ?_⟩
  · rcases low_cases H (x := x) (y := s) ⟨hx0, hxa⟩ (by omega) with h | h | ⟨v, hv₀, hv₁, h⟩
    · exact absurd h hx
    · exact absurd h (hT' x)
    · have h1 := (low_box H hv₀ hv₁ h).2
      have h2 := hY v hv₀ hv₁
      exact ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ _, hv₀, hv₁, by omega⟩⟩
  · obtain ⟨x', hx', hmem⟩ : ∃ x', (0 ≤ x' ∧ x' < a) ∧ (x', b - 1 - s) ∉ t i₁ := by
      refine ⟨if (κ i₁).negX then a - 1 - x else x, by split <;> omega, fun h => hx ?_⟩
      rw [H.top_mem] at h
      rcases H.mirror_form with ⟨hn, -⟩ | ⟨hn, -⟩ <;>
        simpa [hn, show b - 1 - (b - 1 - s) = s by ring,
          show a - 1 - (a - 1 - x) = x by ring] using h
    rcases low_cases H (y := b - 1 - s) hx' (by omega) with h | h | ⟨v, hv₀, hv₁, h⟩
    · exact absurd h (hT x')
    · exact absurd h hmem
    · have h1 := (low_box H hv₀ hv₁ h).2
      have h2 := hY v hv₀ hv₁
      exact ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ _, hv₀, hv₁, by omega⟩⟩

/-- For vertical tiles with the same rows, the box of one does not contain the spine
column of the other. Source: `report-4.md`, Lemma 43 (c), proof: "each lies left or
right of the spine column of another, so its box contains no other spine column". -/
private theorem lemma43_spine_out (H : TypeH2 a b d t i₀ i₁ κ) {v w : Fin 5} (hv₀ : v ≠ i₀)
    (hv₁ : v ≠ i₁) (hw₀ : w ≠ i₀) (hw₁ : w ≠ i₁) (hvw : v ≠ w)
    (hy : (κ v).boxY a = (κ w).boxY a) :
    ¬ ((κ v).boxX d ≤ (κ w).shift.1 ∧ (κ w).shift.1 < (κ v).boxX d + d) := by
  intro h
  have hmem : (κ w).shift.1 ∈ xSpan (t v) := by
    rw [(H.frame.vertical_spine (H.vert v hv₀ hv₁)).2.1, Finset.mem_Ico]
    exact h
  obtain ⟨c, hc, e, he, h1, h2⟩ := mem_xSpan.1 hmem
  obtain ⟨y, hyv⟩ :=
    (H.frame.isTiling.tile_isPolyomino H.frame.poly v).2.exists_in_col hc he h1 h2
  have hbox := (low_box H hv₀ hv₁ hyv).2
  exact hvw (low_same H hyv (low_spine H hw₀ hw₁ (by omega) (by omega)))

/-- Lemma 43 (c), the block of one tile: for `h = 2s`, if the box of the vertical tile
`v` is disjoint in columns from the boxes of the others, then `T` contains the columns
`[d - s, a + s - d)` of its box in full. Source: `report-4.md`, Lemma 43 (c), proof:
"W contains the rows d - s, ..., a + s - d - 1 of its box in full. This set of rows is
its own reversal, so T contains the columns [d - s, a + s - d) of its box in full." -/
private theorem lemma43_single (H : TypeH2 a b d t i₀ i₁ κ) {s : ℤ}
    (hbs : b = a + 2 * s) {v : Fin 5} (hv₀ : v ≠ i₀) (hv₁ : v ≠ i₁) (hy : (κ v).boxY a = s)
    (hsep : ∀ w, w ≠ i₀ → w ≠ i₁ → w ≠ v →
      (κ v).boxX d + d ≤ (κ w).boxX d ∨ (κ w).boxX d + d ≤ (κ v).boxX d)
    {x j : ℤ} (hx0 : d - s ≤ x) (hxa : x < a + s - d) (hj0 : 0 ≤ j) (hjd : j < d) :
    (x, j) ∈ t i₀ := by
  have hb := H.bounds hv₀ hv₁
  have hX := (low_range H hv₀ hv₁).1
  rw [← H.frame.vertical_mem (H.vert v hv₀ hv₁)]
  have hcol : (κ v).boxX d ≤ (if (κ v).negX then -j else j) + (κ v).shift.1 ∧
      (if (κ v).negX then -j else j) + (κ v).shift.1 < (κ v).boxX d + d := by
    unfold GridIso.boxX
    split <;> omega
  have hrow : d ≤ (if (κ v).negY then -x else x) + (κ v).shift.2 ∧
      (if (κ v).negY then -x else x) + (κ v).shift.2 < b - d := by
    unfold GridIso.boxY at hy
    cases hn : (κ v).negY <;>
      simp only [hn, Bool.false_eq_true, ite_true, ite_false] at hy ⊢ <;> omega
  obtain ⟨w, hw₀, hw₁, hw⟩ := low_middle H (x := (if (κ v).negX then -j else j) + (κ v).shift.1)
    (by omega) hrow
  by_cases hwv : w = v
  · rwa [hwv] at hw
  · have h1 := (low_box H hw₀ hw₁ hw).1
    have h2 := hsep w hw₀ hw₁ hwv
    omega

/-- Lemma 43 (c), the last step: with the full columns of `lemma43_single` the spines of
three vertical tiles with `y = s` have no place. Source: `report-4.md`, Lemma 43 (c),
proof, where the middle tile is used; here two of the spines lie on the same side of
the full columns. -/
private theorem lemma43_three (H : TypeH2 a b d t i₀ i₁ κ) {s : ℤ}
    (hs0 : 1 ≤ s) (hsd : s < d) (hY : ∀ v, v ≠ i₀ → v ≠ i₁ → (κ v).boxY a = s)
    (hfull : ∀ x : ℤ, d - s ≤ x → x < a + s - d → (x, s) ∈ t i₀) : False := by
  obtain ⟨p, q, r, hp, hq, hr, ⟨hpq, hpr, hqr⟩, -⟩ := low_vertical H
  have key : ∀ v, v ≠ i₀ → v ≠ i₁ → (κ v).shift.1 < d - s ∨ a + s - d ≤ (κ v).shift.1 := by
    intro v hv₀ hv₁
    by_contra h
    have hy := hY v hv₀ hv₁
    have hc := low_spine H hv₀ hv₁ (y := s) (by omega) (by omega)
    exact hv₀ (low_same H hc (hfull _ (by omega) (by omega)))
  have out : ∀ v w, v ≠ i₀ ∧ v ≠ i₁ → w ≠ i₀ ∧ w ≠ i₁ → v ≠ w →
      ¬ ((κ v).boxX d ≤ (κ w).shift.1 ∧ (κ w).shift.1 < (κ v).boxX d + d) :=
    fun v w hv hw hvw => lemma43_spine_out H hv.1 hv.2 hw.1 hw.2 hvw
      ((hY v hv.1 hv.2).trans (hY w hw.1 hw.2).symm)
  have two : ∀ v w, v ≠ i₀ ∧ v ≠ i₁ → w ≠ i₀ ∧ w ≠ i₁ → v ≠ w →
      (κ v).shift.1 < d - s → a + s - d ≤ (κ w).shift.1 := by
    intro v w hv hw hvw hlt
    have h1 := out v w hv hw hvw
    have h2 := out w v hw hv hvw.symm
    obtain ⟨-, v1, v2⟩ := low_range H hv.1 hv.2
    obtain ⟨-, w1, w2⟩ := low_range H hw.1 hw.2
    have hvR := (low_range H hv.1 hv.2).1
    have hwR := (low_range H hw.1 hw.2).1
    rcases key w hw.1 hw.2 with h | h
    · cases hnv : (κ v).negX
      · cases hnw : (κ w).negX
        · have := v1 hnv
          have := w1 hnw
          omega
        · have := w2 hnw
          omega
      · have := v2 hnv
        omega
    · exact h
  have two' : ∀ v w, v ≠ i₀ ∧ v ≠ i₁ → w ≠ i₀ ∧ w ≠ i₁ → v ≠ w →
      a + s - d ≤ (κ v).shift.1 → a + s - d ≤ (κ w).shift.1 → False := by
    intro v w hv hw hvw hlt hlt'
    have h1 := out v w hv hw hvw
    have h2 := out w v hw hv hvw.symm
    obtain ⟨hvR, v1, v2⟩ := low_range H hv.1 hv.2
    obtain ⟨hwR, w1, w2⟩ := low_range H hw.1 hw.2
    cases hnv : (κ v).negX
    · have := v1 hnv
      omega
    · cases hnw : (κ w).negX
      · have := w1 hnw
        omega
      · have := v2 hnv
        have := w2 hnw
        omega
  rcases key p hp.1 hp.2 with h | h
  · exact two' q r hq hr hqr (two p q hp hq hpq h) (two p r hp hr hpr h)
  · rcases key q hq.1 hq.2 with h' | h'
    · exact two' p r hp hr hpr h (two q r hq hr hqr h')
    · exact two' p q hp hq hpq h h'

/-- Lemma 43 (c). PROVISIONAL. Source: `report-4.md`, Lemma 43 (c) (line 349):
"h >= 2s + 1; so no tile is both." -/
theorem lemma43c (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {s : ℤ}
    (hs : FullRows (t i₀) a s) : 2 * s + 1 ≤ b - a := by
  have _ := hda -- not needed: Corollary 42 gives it
  by_contra hlt
  obtain ⟨p, q, r, hp, hq, hr, ⟨hpq, hpr, hqr⟩, hall⟩ := low_vertical H
  obtain ⟨hb, hrange⟩ := corollary42 H hs
  have hsd := low_s H hs
  have hYp := hrange p hp.1 hp.2
  have hbs : b = a + 2 * s := by omega
  have hY : ∀ v, v ≠ i₀ → v ≠ i₁ → (κ v).boxY a = s := fun v hv₀ hv₁ => by
    have := hrange v hv₀ hv₁
    omega
  have out : ∀ v w, v ≠ i₀ ∧ v ≠ i₁ → w ≠ i₀ ∧ w ≠ i₁ → v ≠ w →
      ¬ ((κ v).boxX d ≤ (κ w).shift.1 ∧ (κ w).shift.1 < (κ v).boxX d + d) :=
    fun v w hv hw hvw => lemma43_spine_out H hv.1 hv.2 hw.1 hw.2 hvw
      ((hY v hv.1 hv.2).trans (hY w hw.1 hw.2).symm)
  -- a tile whose box is disjoint in columns from the two others
  have single : ∀ v w u, v ≠ i₀ ∧ v ≠ i₁ → (∀ j, j ≠ i₀ → j ≠ i₁ → j = v ∨ j = w ∨ j = u) →
      (κ v).boxX d + d ≤ (κ w).boxX d ∨ (κ w).boxX d + d ≤ (κ v).boxX d →
      (κ v).boxX d + d ≤ (κ u).boxX d ∨ (κ u).boxX d + d ≤ (κ v).boxX d → False := by
    intro v w u hv hall' h1 h2
    refine lemma43_three H hsd.1 hsd.2 hY fun x hx hx' =>
      lemma43_single H hbs hv.1 hv.2 (hY v hv.1 hv.2) ?_ hx hx' (by omega) hsd.2
    intro j hj₀ hj₁ hjv
    rcases hall' j hj₀ hj₁ with rfl | rfl | rfl
    · exact absurd rfl hjv
    · exact h1
    · exact h2
  have sp := single p q r hp hall
  have sq := single q p r hq fun j h0 h1 => by have := hall j h0 h1; tauto
  have sr := single r p q hr fun j h0 h1 => by have := hall j h0 h1; tauto
  have o1 := out p q hp hq hpq
  have o2 := out q p hq hp hpq.symm
  have o3 := out p r hp hr hpr
  have o4 := out r p hr hp hpr.symm
  have o5 := out q r hq hr hqr
  have o6 := out r q hr hq hqr.symm
  obtain ⟨Rp, p1, p2⟩ := low_range H hp.1 hp.2
  obtain ⟨Rq, q1, q2⟩ := low_range H hq.1 hq.2
  obtain ⟨Rr, r1, r2⟩ := low_range H hr.1 hr.2
  have key : ((κ p).boxX d + d ≤ (κ q).boxX d ∨ (κ q).boxX d + d ≤ (κ p).boxX d) ∧
        ((κ p).boxX d + d ≤ (κ r).boxX d ∨ (κ r).boxX d + d ≤ (κ p).boxX d) ∨
      ((κ q).boxX d + d ≤ (κ p).boxX d ∨ (κ p).boxX d + d ≤ (κ q).boxX d) ∧
        ((κ q).boxX d + d ≤ (κ r).boxX d ∨ (κ r).boxX d + d ≤ (κ q).boxX d) ∨
      ((κ r).boxX d + d ≤ (κ p).boxX d ∨ (κ p).boxX d + d ≤ (κ r).boxX d) ∧
        ((κ r).boxX d + d ≤ (κ q).boxX d ∨ (κ q).boxX d + d ≤ (κ r).boxX d) := by
    cases hnp : (κ p).negX <;> cases hnq : (κ q).negX <;> cases hnr : (κ r).negX <;>
      simp only [hnp, hnq, hnr, Bool.false_eq_true, Bool.true_eq_false, forall_const,
        IsEmpty.forall_iff] at p1 p2 q1 q2 r1 r2 <;> omega
  rcases key with h | h | h
  · exact sp h.1 h.2
  · exact sq h.1 h.2
  · exact sr h.1 h.2

/-- The numbers `P`, `Q` of bottom and of top tiles: both at least 1, and at most 3
together. Source: `report-4.md`, section 5h (line 441): "P, Q >= 1 and no tile is
both (Lemma 43(b), (c)), so (P, Q) is (1, 1), (2, 1) or (1, 2)." -/
theorem counts_bottom_top (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {s : ℤ}
    (hs : FullRows (t i₀) a s) :
    1 ≤ (bottomTiles a s κ i₀ i₁).card ∧ 1 ≤ (upperTiles a b s κ i₀ i₁).card ∧
      (bottomTiles a s κ i₀ i₁).card + (upperTiles a b s κ i₀ i₁).card ≤ 3 := by
  obtain ⟨-, -, hP, hQ⟩ := lemma43b H hda hs
  have hh := lemma43c H hda hs
  refine ⟨hP.card_pos, hQ.card_pos, ?_⟩
  have hdisj : Disjoint (bottomTiles a s κ i₀ i₁) (upperTiles a b s κ i₀ i₁) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    have h1 := (Finset.mem_filter.1 hv).2.2.2
    have h2 := (Finset.mem_filter.1 hv').2.2.2
    have := (low_s H hs).1
    omega
  rw [← Finset.card_union_of_disjoint hdisj]
  have hsub : bottomTiles a s κ i₀ i₁ ∪ upperTiles a b s κ i₀ i₁ ⊆
      (Finset.univ.erase i₀).erase i₁ := by
    intro v hv
    have h : v ≠ i₀ ∧ v ≠ i₁ := by
      rcases Finset.mem_union.1 hv with h | h
      · exact ⟨(Finset.mem_filter.1 h).2.1, (Finset.mem_filter.1 h).2.2.1⟩
      · exact ⟨(Finset.mem_filter.1 h).2.1, (Finset.mem_filter.1 h).2.2.1⟩
    exact Finset.mem_erase.2 ⟨h.2, Finset.mem_erase.2 ⟨h.1, Finset.mem_univ _⟩⟩
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨H.ne, Finset.mem_univ _⟩),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

/-! ### Working lemmas for Proposition 44 -/

/-- Two sets with the same cells in rows `y` and `y'` have equal row counts. -/
private theorem prop44_rowCount_congr {S S' : Finset Cell} {y y' : ℤ}
    (h : ∀ x : ℤ, (x, y) ∈ S ↔ (x, y') ∈ S') : rowCount S y = rowCount S' y' := by
  unfold rowCount
  congr 1
  refine Finset.card_nbij' (fun c => (c.1, y')) (fun c => (c.1, y)) ?_ ?_ ?_ ?_
  · rintro ⟨x, z⟩ hc
    simp only [Finset.mem_coe, Finset.mem_filter] at hc ⊢
    obtain ⟨hc, rfl⟩ := hc
    exact ⟨(h x).1 hc, trivial⟩
  · rintro ⟨x, z⟩ hc
    simp only [Finset.mem_coe, Finset.mem_filter] at hc ⊢
    obtain ⟨hc, rfl⟩ := hc
    exact ⟨(h x).2 hc, trivial⟩
  · rintro ⟨x, z⟩ hc
    simp only [Finset.mem_coe, Finset.mem_filter] at hc
    exact Prod.ext rfl hc.2.symm
  · rintro ⟨x, z⟩ hc
    simp only [Finset.mem_coe, Finset.mem_filter] at hc
    exact Prod.ext rfl hc.2.symm

/-- The end rows of the box of a vertical tile are the images of the end columns of
`T`. -/
private theorem prop44_end_rows (H : TypeH2 a b d t i₀ i₁ κ) {v : Fin 5} (hv₀ : v ≠ i₀)
    (hv₁ : v ≠ i₁) :
    rowCount (t v) ((κ v).boxY a) = colCount (t i₀) (if (κ v).negY then a - 1 else 0) ∧
      rowCount (t v) ((κ v).boxY a + a - 1) =
        colCount (t i₀) (if (κ v).negY then 0 else a - 1) := by
  have h0 := H.frame.vertical_rowCount (H.vert v hv₀ hv₁) 0
  have h1 := H.frame.vertical_rowCount (H.vert v hv₀ hv₁) (a - 1)
  cases hn : (κ v).negY <;>
    simp only [hn, GridIso.boxY, Bool.false_eq_true, ite_true, ite_false] at h0 h1 ⊢
  · exact ⟨by rw [← h0, zero_add], by rw [← h1]; congr 1; omega⟩
  · exact ⟨by rw [← h1]; congr 1; omega, by rw [← h0]; congr 1; omega⟩

/-- For a left-type vertical tile the first column of the box is the image of row
`d - 1` of `T` (the report's Top). -/
private theorem prop44_top_mem (H : TypeH2 a b d t i₀ i₁ κ) {v : Fin 5} (hv₀ : v ≠ i₀)
    (hv₁ : v ≠ i₁) (hn : (κ v).negX = true) (x : ℤ) :
    ((κ v).boxX d, (κ v).boxY a + (if (κ v).negY then a - 1 - x else x)) ∈ t v ↔
      (x, d - 1) ∈ t i₀ := by
  rw [← H.frame.vertical_mem (H.vert v hv₀ hv₁) x (d - 1), hn, ite_eq_left rfl]
  have e1 : (κ v).boxX d = -(d - 1) + (κ v).shift.1 := by
    simp only [GridIso.boxX, hn, ite_true]
    omega
  have e2 : (κ v).boxY a + (if (κ v).negY then a - 1 - x else x) =
      (if (κ v).negY then -x else x) + (κ v).shift.2 := by
    unfold GridIso.boxY
    cases (κ v).negY <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega
  rw [e1, e2]

/-- The tile `v` starts at row `s`, the tile `w` stands on it, and the third vertical
tile `u` is at the other wall. Source: `report-4.md`, Proposition 44, proof
(line 357): "h = a + 2s, b = 2a + 2s, and the tiles are V_B (rows [s, s + a)), V_T
(rows [s + a, s + 2a)) and V_M (rows [y_m, y_m + a), s + 1 <= y_m <= s + a - 1)",
"a + 2s - d <= y_m <= d", "V_B and V_T have columns [0, d) and V_M has [a - d, a)". -/
private structure Prop44Stack (a b d s : ℤ) (t : Fin 5 → Finset Cell) (i₀ i₁ : Fin 5)
    (κ : Fin 5 → GridIso) (v w u : Fin 5) : Prop where
  H : TypeH2 a b d t i₀ i₁ κ
  hda : d < a
  hs : FullRows (t i₀) a s
  hv : v ≠ i₀ ∧ v ≠ i₁
  hw : w ≠ i₀ ∧ w ≠ i₁
  hu : u ≠ i₀ ∧ u ≠ i₁
  ne : u ≠ v ∧ u ≠ w ∧ v ≠ w
  hall : ∀ j, j = u ∨ j = i₀ ∨ j = i₁ ∨ j = v ∨ j = w
  hb : b = 2 * a + 2 * s
  yv : (κ v).boxY a = s
  yw : (κ w).boxY a = s + a
  yu : s + 1 ≤ (κ u).boxY a ∧ (κ u).boxY a ≤ s + a - 1
  yud : a + 2 * s - d ≤ (κ u).boxY a ∧ (κ u).boxY a ≤ d
  xv : (κ v).boxX d = 0
  xw : (κ w).boxX d = 0
  xu : (κ u).boxX d = a - d

namespace Prop44Stack

variable {s : ℤ} {v w u : Fin 5}

/-- Every cell is in one of the five tiles. -/
private theorem cell (L : Prop44Stack a b d s t i₀ i₁ κ v w u) {x y : ℤ}
    (hx : 0 ≤ x ∧ x < a) (hy : 0 ≤ y ∧ y < b) :
    (x, y) ∈ t i₀ ∨ (x, y) ∈ t i₁ ∨ (x, y) ∈ t v ∨ (x, y) ∈ t w ∨ (x, y) ∈ t u := by
  obtain ⟨j, hj⟩ := L.H.frame.isTiling.exists_tile (c := (x, y)) (mem_R.2 ⟨hx, hy⟩)
  rcases L.hall j with rfl | rfl | rfl | rfl | rfl <;> tauto

/-- `s <= u_0, u_1 <= d` and the two end columns of `T`. -/
private theorem ends (L : Prop44Stack a b d s t i₀ i₁ κ v w u) :
    (s ≤ colCount (t i₀) 0 ∧ colCount (t i₀) 0 ≤ d) ∧
      s ≤ colCount (t i₀) (a - 1) ∧ colCount (t i₀) (a - 1) ≤ d := by
  obtain ⟨h0, h1⟩ := lemma43a L.H L.hda
  have hs := low_s L.H L.hs
  have hda := L.hda
  have key : ∀ x m : ℤ, 0 ≤ x → x < a → (∀ y : ℤ, (x, y) ∈ t i₀ ↔ 0 ≤ y ∧ y < m) →
      s ≤ m ∧ m ≤ d := by
    intro x m hx0 hxa h
    have h2 := (h (s - 1)).1 ((low_fullRows L.hs).2.1 x (s - 1) hx0 hxa (by omega) (by omega))
    have h3 := low_row_T L.H ((h (m - 1)).2 (by omega))
    omega
  exact ⟨key 0 _ le_rfl (by omega) h0, key (a - 1) _ (by omega) (by omega) h1⟩

/-- `u_1 >= y_m`. Source: `report-4.md`, Proposition 44, proof: "Rows s <= r < y_m
outside T belong to V_B, so T contains [d, a) x [0, y_m) and u_1 >= y_m > s." -/
private theorem u1_ge (L : Prop44Stack a b d s t i₀ i₁ κ v w u) :
    (κ u).boxY a ≤ colCount (t i₀) (a - 1) := by
  have hs := low_s L.H L.hs
  obtain ⟨-, h1⟩ := lemma43a L.H L.hda
  have hda := L.hda
  have hb := L.hb
  have hyu := L.yu
  have hyud := L.yud
  have hm : (a - 1, (κ u).boxY a - 1) ∈ t i₀ := by
    rcases L.cell (x := a - 1) (y := (κ u).boxY a - 1) (by omega) (by omega) with
      h | h | h | h | h
    · exact h
    · have := low_row_T' L.H h
      omega
    · have := low_box L.H L.hv.1 L.hv.2 h
      have := L.xv
      omega
    · have := low_box L.H L.hw.1 L.hw.2 h
      have := L.xw
      omega
    · have := low_box L.H L.hu.1 L.hu.2 h
      omega
  have := (h1 _).1 hm
  omega

/-- Column 0 of `T'`. -/
private theorem col0_T' (L : Prop44Stack a b d s t i₀ i₁ κ v w u) (y : ℤ) :
    (0, y) ∈ t i₁ ↔ b - colCount (t i₀) (if (κ i₁).negX then a - 1 else 0) ≤ y ∧ y < b := by
  obtain ⟨h0, h1⟩ := lemma43a L.H L.hda
  rw [L.H.top_mem]
  cases (κ i₁).negX
  · simp only [Bool.false_eq_true, ite_false]
    rw [h0]
    omega
  · simp only [ite_true, sub_zero]
    rw [h1]
    omega

/-- Column 0 between `T` and `T'` is in `v` up to row `s + a` and in `w` from there. -/
private theorem col0 (L : Prop44Stack a b d s t i₀ i₁ κ v w u) :
    (∀ y : ℤ, (0, y) ∈ t v ↔ colCount (t i₀) 0 ≤ y ∧ y < s + a) ∧
      ∀ y : ℤ, (0, y) ∈ t w ↔
        s + a ≤ y ∧ y < b - colCount (t i₀) (if (κ i₁).negX then a - 1 else 0) := by
  obtain ⟨h0, h1⟩ := lemma43a L.H L.hda
  obtain ⟨e0, e1⟩ := L.ends
  have hT' := L.col0_T'
  have hs := low_s L.H L.hs
  have hda := L.hda
  have hb := L.hb
  have hyv := L.yv
  have hyw := L.yw
  have he : s ≤ colCount (t i₀) (if (κ i₁).negX then a - 1 else 0) ∧
      colCount (t i₀) (if (κ i₁).negX then a - 1 else 0) ≤ d := by
    cases (κ i₁).negX
    · simpa using e0
    · simpa using e1
  generalize colCount (t i₀) (if (κ i₁).negX then a - 1 else 0) = e at *
  constructor
  · intro y
    constructor
    · intro h
      have hbox := low_box L.H L.hv.1 L.hv.2 h
      have hn : ¬ (0 ≤ y ∧ y < colCount (t i₀) 0) := fun h' =>
        L.hv.1 (low_same L.H h ((h0 y).2 h'))
      omega
    · rintro ⟨hy0, hy1⟩
      rcases L.cell (x := 0) (y := y) (by omega) (by omega) with h | h | h | h | h
      · have := (h0 y).1 h
        omega
      · have := (hT' y).1 h
        omega
      · exact h
      · have := low_box L.H L.hw.1 L.hw.2 h
        omega
      · have := low_box L.H L.hu.1 L.hu.2 h
        have := L.xu
        omega
  · intro y
    constructor
    · intro h
      have hbox := low_box L.H L.hw.1 L.hw.2 h
      have hn : ¬ (b - e ≤ y ∧ y < b) := fun h' => L.hw.2 (low_same L.H h ((hT' y).2 h'))
      have := low_in_R L.H h
      omega
    · rintro ⟨hy0, hy1⟩
      rcases L.cell (x := 0) (y := y) (by omega) (by omega) with h | h | h | h | h
      · have := (h0 y).1 h
        omega
      · have := (hT' y).1 h
        omega
      · have := low_box L.H L.hv.1 L.hv.2 h
        omega
      · exact h
      · have := low_box L.H L.hu.1 L.hu.2 h
        have := L.xu
        omega

/-- The ends of Top, read off a left-type tile at column 0: `(0, d - 1)` is in `T`
exactly when `u_0 = d`, and `(a - 1, d - 1)` exactly when `u_1 = d`. -/
private theorem top_ends (L : Prop44Stack a b d s t i₀ i₁ κ v w u)
    (hn : (κ v).negX = true) :
    (((0 : ℤ), s + (if (κ v).negY then a - 1 else 0)) ∈ t v ↔ d - 1 < colCount (t i₀) 0) ∧
      (((0 : ℤ), s + (if (κ v).negY then 0 else a - 1)) ∈ t v ↔
        d - 1 < colCount (t i₀) (a - 1)) := by
  obtain ⟨h0, h1⟩ := lemma43a L.H L.hda
  have hs := low_s L.H L.hs
  have t0 := prop44_top_mem L.H L.hv.1 L.hv.2 hn 0
  have t1 := prop44_top_mem L.H L.hv.1 L.hv.2 hn (a - 1)
  rw [L.xv, L.yv] at t0 t1
  rw [sub_zero, h0] at t0
  rw [sub_self, h1] at t1
  exact ⟨t0.trans (by omega), t1.trans (by omega)⟩

/-- Proposition 44 for `G = H`. Source: `report-4.md`, Proposition 44, proof, "G = H"
(line 359). -/
private theorem absurd_half (L : Prop44Stack a b d s t i₀ i₁ κ v w u)
    (hG : (κ i₁).negX = true) : False := by
  obtain ⟨h0, h1⟩ := lemma43a L.H L.hda
  obtain ⟨e0, e1⟩ := L.ends
  obtain ⟨cv, cw⟩ := L.col0
  rw [hG, ite_eq_left rfl] at cw
  have hs := low_s L.H L.hs
  have hda := L.hda
  have hb := L.hb
  have hu1 := L.u1_ge
  have hyu := L.yu
  have hyv := L.yv
  have hyw := L.yw
  -- `w` has the spine column `d - 1`
  have hnw : (κ w).negX = true := by
    by_contra hn
    rw [Bool.not_eq_true] at hn
    have hc := low_spine L.H L.hw.1 L.hw.2 (y := s + 2 * a - 1) (by omega) (by omega)
    rw [(low_range L.H L.hw.1 L.hw.2).2.1 hn, L.xw] at hc
    have := (cw _).1 hc
    omega
  -- `v` has the spine column `d - 1`
  have hnv : (κ v).negX = true := by
    by_contra hn
    rw [Bool.not_eq_true] at hn
    have hc := low_spine L.H L.hv.1 L.hv.2 (y := s) (by omega) (by omega)
    rw [(low_range L.H L.hv.1 L.hv.2).2.1 hn, L.xv] at hc
    have hu0 := (cv _).1 hc
    have hcell : (a - 1, b - colCount (t i₀) 0 - 1) ∈ t u := by
      rcases L.cell (x := a - 1) (y := b - colCount (t i₀) 0 - 1) (by omega) (by omega) with
        h | h | h | h | h
      · have := (h1 _).1 h
        omega
      · rw [L.H.top_mem, hG, ite_eq_left rfl, sub_self, h0] at h
        omega
      · have := low_box L.H L.hv.1 L.hv.2 h
        have := L.xv
        omega
      · have := low_box L.H L.hw.1 L.hw.2 h
        have := L.xw
        omega
      · exact h
    have := low_box L.H L.hu.1 L.hu.2 hcell
    omega
  -- the two counts give `u_0 = u_1`
  have hcount : ∀ z, z ≠ i₀ ∧ z ≠ i₁ → (κ z).negX = true → (κ z).boxX d = 0 →
      colCount (t z) 0 = rowCount (t i₀) (d - 1) := by
    intro z hz hn hx
    have h := L.H.frame.vertical_colCount (L.H.vert z hz.1 hz.2) (d - 1)
    rwa [hn, ite_eq_left rfl, (low_range L.H hz.1 hz.2).2.2 hn, hx,
      show -(d - 1) + (0 + (d - 1)) = 0 by ring] at h
  have k1 := hcount v L.hv hnv L.xv
  have k2 := hcount w L.hw hnw L.xw
  rw [low_colCount cv (by omega)] at k1
  rw [low_colCount cw (by omega)] at k2
  obtain ⟨t0, t1⟩ := L.top_ends hnv
  rw [cv] at t0 t1
  cases hn : (κ v).negY <;> simp only [hn, Bool.false_eq_true, ite_true, ite_false] at t0 t1 <;>
    omega

/-- Proposition 44 for `G = F`: `V_B` and `V_T` have the same spine column and
`u_0 != u_1`. Source: `report-4.md`, Proposition 44, proof, the three cases "G = F"
(lines 360-362). -/
private theorem spines_flip (L : Prop44Stack a b d s t i₀ i₁ κ v w u)
    (hG : (κ i₁).negX = false) :
    (κ v).negX = (κ w).negX ∧ colCount (t i₀) 0 ≠ colCount (t i₀) (a - 1) := by
  obtain ⟨h0, h1⟩ := lemma43a L.H L.hda
  obtain ⟨e0, e1⟩ := L.ends
  obtain ⟨cv, cw⟩ := L.col0
  rw [hG, ite_eq_right Bool.false_ne_true] at cw
  have hs := low_s L.H L.hs
  have hda := L.hda
  have hb := L.hb
  have hu1 := L.u1_ge
  have hyu := L.yu
  have hyv := L.yv
  have hyw := L.yw
  -- a spine in column 0 gives `u_0 = s`
  have hv0 : (κ v).negX = false → colCount (t i₀) 0 = s := by
    intro hn
    have hc := low_spine L.H L.hv.1 L.hv.2 (y := s) (by omega) (by omega)
    rw [(low_range L.H L.hv.1 L.hv.2).2.1 hn, L.xv] at hc
    have := (cv _).1 hc
    omega
  have hw0 : (κ w).negX = false → colCount (t i₀) 0 = s := by
    intro hn
    have hc := low_spine L.H L.hw.1 L.hw.2 (y := s + 2 * a - 1) (by omega) (by omega)
    rw [(low_range L.H L.hw.1 L.hw.2).2.1 hn, L.xw] at hc
    have := (cw _).1 hc
    omega
  -- a spine in column `d - 1` excludes `u_0 = s`
  have hv1 : (κ v).negX = true → colCount (t i₀) 0 ≠ s := by
    intro hn he
    obtain ⟨t0, -⟩ := L.top_ends hn
    rw [cv] at t0
    cases hY : (κ v).negY <;> simp only [hY, Bool.false_eq_true, ite_true, ite_false] at t0 <;>
      omega
  have hw1 : (κ w).negX = true → colCount (t i₀) 0 ≠ s := by
    intro hn he
    have t0 := prop44_top_mem L.H L.hw.1 L.hw.2 hn 0
    rw [L.xw, L.yw, h0, cw] at t0
    cases hY : (κ w).negY <;> simp only [hY, Bool.false_eq_true, ite_true, ite_false] at t0 <;>
      omega
  cases hnv : (κ v).negX
  · have hu0 := hv0 hnv
    cases hnw : (κ w).negX
    · exact ⟨rfl, by omega⟩
    · exact absurd hu0 (hw1 hnw)
  · have hu0 := hv1 hnv
    cases hnw : (κ w).negX
    · exact absurd (hw0 hnw) hu0
    · refine ⟨rfl, fun he => ?_⟩
      obtain ⟨t0, t1⟩ := L.top_ends hnv
      rw [cv] at t0 t1
      cases hY : (κ v).negY <;>
        simp only [hY, Bool.false_eq_true, ite_true, ite_false] at t0 t1 <;> omega

/-- The tiles `v` and `w` are images of each other under `F`. Source: `report-4.md`,
Proposition 44, proof (line 363): "So V_B = F(V_T)." -/
private theorem flip_eq (L : Prop44Stack a b d s t i₀ i₁ κ v w u)
    (hG : (κ i₁).negX = false) (x y : ℤ) : (x, y) ∈ t v ↔ (x, b - 1 - y) ∈ t w := by
  obtain ⟨hnX, hne⟩ := L.spines_flip hG
  have hs := low_s L.H L.hs
  have hda := L.hda
  have hb := L.hb
  have hyu := L.yu
  have hyud := L.yud
  have hyv := L.yv
  have hyw := L.yw
  have back : b - 1 - (b - 1 - s) = s := by ring
  -- row `s` outside `T`, and row `b - 1 - s` outside `T'`
  have rv : ∀ z : ℤ, (z, s) ∈ t v ↔ (0 ≤ z ∧ z < a) ∧ (z, s) ∉ t i₀ := by
    intro z
    refine ⟨fun h => ⟨(low_in_R L.H h).1, fun h' => L.hv.1 (low_same L.H h h')⟩, ?_⟩
    rintro ⟨hz, hT⟩
    rcases L.cell (x := z) (y := s) hz (by omega) with h | h | h | h | h
    · exact absurd h hT
    · have := low_row_T' L.H h
      omega
    · exact h
    · have := low_box L.H L.hw.1 L.hw.2 h
      omega
    · have := low_box L.H L.hu.1 L.hu.2 h
      omega
  have rw' : ∀ z : ℤ, (z, b - 1 - s) ∈ t w ↔ (0 ≤ z ∧ z < a) ∧ (z, s) ∉ t i₀ := by
    intro z
    have hT' : (z, b - 1 - s) ∈ t i₁ ↔ (z, s) ∈ t i₀ := by
      rw [L.H.top_mem, hG, ite_eq_right Bool.false_ne_true, back]
    refine ⟨fun h => ⟨(low_in_R L.H h).1, fun h' => L.hw.2 (low_same L.H h (hT'.2 h'))⟩, ?_⟩
    rintro ⟨hz, hT⟩
    rcases L.cell (x := z) (y := b - 1 - s) hz (by omega) with h | h | h | h | h
    · have := low_row_T L.H h
      omega
    · exact absurd (hT'.1 h) hT
    · have := low_box L.H L.hv.1 L.hv.2 h
      omega
    · exact h
    · have := low_box L.H L.hu.1 L.hu.2 h
      omega
  have hcount := prop44_rowCount_congr fun z => (rv z).trans (rw' z).symm
  have ev := (prop44_end_rows L.H L.hv.1 L.hv.2).1
  have ew := (prop44_end_rows L.H L.hw.1 L.hw.2).2
  rw [hyv] at ev
  rw [show (κ w).boxY a + a - 1 = b - 1 - s by omega] at ew
  rw [hcount, ew] at ev
  have hX : (κ v).shift.1 = (κ w).shift.1 := by
    obtain ⟨-, v0, v1⟩ := low_range L.H L.hv.1 L.hv.2
    obtain ⟨-, w0, w1⟩ := low_range L.H L.hw.1 L.hw.2
    have := L.xv
    have := L.xw
    cases hn : (κ v).negX
    · have := v0 hn
      have := w0 (hnX ▸ hn)
      omega
    · have := v1 hn
      have := w1 (hnX ▸ hn)
      omega
  have hsv := L.H.vert v L.hv.1 L.hv.2
  have hsw := L.H.vert w L.hw.1 L.hw.2
  unfold GridIso.boxY at hyv hyw
  have hpre : (κ v).inv.apply (x, y) = (κ w).inv.apply (x, b - 1 - y) := by
    cases h1 : (κ v).negY <;> cases h2 : (κ w).negY <;>
      simp only [h1, h2, Bool.false_eq_true, ite_true, ite_false] at ev hyv hyw
    · exact absurd ev.symm hne
    · simp only [GridIso.inv, GridIso.apply, hsv, hsw, h1, h2, hnX, hX, ite_true,
        Bool.false_eq_true, ite_false]
      exact Prod.ext (by dsimp only; omega) rfl
    · simp only [GridIso.inv, GridIso.apply, hsv, hsw, h1, h2, hnX, hX, ite_true,
        Bool.false_eq_true, ite_false]
      exact Prod.ext (by dsimp only; omega) rfl
    · exact absurd ev hne
  rw [L.H.frame.mem_tile_iff v, hpre, ← L.H.frame.mem_tile_iff w]

/-- Proposition 44 for `G = F`. Source: `report-4.md`, Proposition 44, proof
(line 363): "Then V_M, the complement, has F(V_M) = V_M, and T is preserved by
x -> a - 1 - x: u_0 = u_1." -/
private theorem absurd_flip (L : Prop44Stack a b d s t i₀ i₁ κ v w u)
    (hG : (κ i₁).negX = false) : False := by
  have hne := (L.spines_flip hG).2
  have hvw := L.flip_eq hG
  have hT : ∀ x y : ℤ, (x, y) ∈ t i₁ ↔ (x, b - 1 - y) ∈ t i₀ := by
    intro x y
    rw [L.H.top_mem, hG, ite_eq_right Bool.false_ne_true]
  have hda := L.hda
  have hd := L.H.frame.two_le_d
  have hsym : ∀ x y : ℤ, (x, y) ∈ t u → (x, b - 1 - y) ∈ t u := by
    intro x y hc
    have hbd := low_in_R L.H hc
    have back : b - 1 - (b - 1 - y) = y := by ring
    rcases L.cell (x := x) (y := b - 1 - y) hbd.1 (by omega) with h | h | h | h | h
    · exact absurd (low_same L.H hc ((hT x y).2 h)) L.hu.2
    · rw [hT, back] at h
      exact absurd (low_same L.H hc h) L.hu.1
    · rw [hvw, back] at h
      exact absurd (low_same L.H hc h) L.ne.2.1
    · exact absurd (low_same L.H hc ((hvw x y).2 h)) L.ne.1
    · exact h
  have hspine : ∀ y : ℤ, (κ u).boxY a ≤ y → y < (κ u).boxY a + a → ((κ u).shift.1, y) ∈ t u :=
    fun y h1 h2 => low_spine L.H L.hu.1 L.hu.2 h1 h2
  have e1 := (low_box L.H L.hu.1 L.hu.2
    (hsym _ _ (hspine ((κ u).boxY a) le_rfl (by omega)))).2
  have e2 := (low_box L.H L.hu.1 L.hu.2
    (hsym _ _ (hspine ((κ u).boxY a + a - 1) (by omega) (by omega)))).2
  have hcount : rowCount (t u) ((κ u).boxY a) = rowCount (t u) ((κ u).boxY a + a - 1) := by
    refine prop44_rowCount_congr fun x => ⟨fun h => ?_, fun h => ?_⟩
    · have h' := hsym _ _ h
      rwa [show b - 1 - (κ u).boxY a = (κ u).boxY a + a - 1 by omega] at h'
    · have h' := hsym _ _ h
      rwa [show b - 1 - ((κ u).boxY a + a - 1) = (κ u).boxY a by omega] at h'
  rw [(prop44_end_rows L.H L.hu.1 L.hu.2).1, (prop44_end_rows L.H L.hu.1 L.hu.2).2] at hcount
  cases h1 : (κ u).negY <;>
    simp only [h1, Bool.false_eq_true, ite_true, ite_false] at hcount
  · exact hne hcount
  · exact hne hcount.symm

/-- The configuration does not occur. -/
private theorem absurd (L : Prop44Stack a b d s t i₀ i₁ κ v w u) : False := by
  cases hG : (κ i₁).negX
  · exact L.absurd_flip hG
  · exact L.absurd_half hG

end Prop44Stack

/-- The box of a vertical tile in the mirror image. -/
private theorem prop44_mirror_box {g : GridIso} (hg : g.swap = true) :
    ((GridIso.flipX a).comp (g.comp (GridIso.flipX a))).boxX d = a - d - g.boxX d ∧
      ((GridIso.flipX a).comp (g.comp (GridIso.flipX a))).boxY a = g.boxY a := by
  obtain ⟨sw, n, m, x, y⟩ := g
  dsimp only at hg
  subst hg
  cases n <;> cases m <;>
    simp [GridIso.comp, GridIso.boxX, GridIso.boxY, GridIso.flipX, GridIso.apply] <;> omega

/-- The full rows of the mirror image. -/
private theorem prop44_mirror_fullRows {T : Finset Cell} {s : ℤ} (hs : FullRows T a s) :
    FullRows (T.image (GridIso.flipX a).apply) a s := by
  obtain ⟨hs0, hfull, x, hx0, hxa, hx⟩ := low_fullRows hs
  refine ⟨hs0, fun z y hz0 hza hy0 hys => low_mem_flipX.2 (hfull _ y (by omega) (by omega) hy0 hys),
    a - 1 - x, by omega, by omega, fun h => hx ?_⟩
  rw [low_mem_flipX, show a - 1 - (a - 1 - x) = x by ring] at h
  exact h

/-- No vertical tile stands on or above another one. Source: `report-4.md`, Proposition
44, first paragraph of the proof (line 357). -/
private theorem prop44_stack (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {s : ℤ}
    (hs : FullRows (t i₀) a s) {v w : Fin 5} (hv : v ≠ i₀ ∧ v ≠ i₁) (hw : w ≠ i₀ ∧ w ≠ i₁)
    (hst : (κ v).boxY a + a ≤ (κ w).boxY a) : False := by
  obtain ⟨hb, hY⟩ := corollary42 H hs
  have hsd := low_s H hs
  -- a row of `[d, b - d)` holds cells of at least two vertical tiles
  have cov : ∀ v w u : Fin 5, (∀ j, j = u ∨ j = i₀ ∨ j = i₁ ∨ j = v ∨ j = w) →
      ∀ x r : ℤ, 0 ≤ x ∧ x < a → d ≤ r ∧ r < b - d →
      ((κ v).boxX d ≤ x ∧ x < (κ v).boxX d + d) ∧
          ((κ v).boxY a ≤ r ∧ r < (κ v).boxY a + a) ∨
        ((κ w).boxX d ≤ x ∧ x < (κ w).boxX d + d) ∧
          ((κ w).boxY a ≤ r ∧ r < (κ w).boxY a + a) ∨
        ((κ u).boxX d ≤ x ∧ x < (κ u).boxX d + d) ∧
          ((κ u).boxY a ≤ r ∧ r < (κ u).boxY a + a) := by
    intro v w u hall x r hx hr
    obtain ⟨j, hj₀, hj₁, hj⟩ := low_middle H hx hr
    have hbox := low_box H hj₀ hj₁ hj
    rcases hall j with h | h | h | h | h
    · subst h
      exact Or.inr (Or.inr hbox)
    · exact absurd h hj₀
    · exact absurd h hj₁
    · subst h
      exact Or.inl hbox
    · subst h
      exact Or.inr (Or.inl hbox)
  -- a stacked pair touches
  have touch : ∀ v w : Fin 5, v ≠ i₀ ∧ v ≠ i₁ → w ≠ i₀ ∧ w ≠ i₁ →
      (κ v).boxY a + a ≤ (κ w).boxY a → (κ w).boxY a = (κ v).boxY a + a := by
    intro v w hv hw hst
    have hvw : v ≠ w := by
      rintro rfl
      omega
    obtain ⟨u, -, -, -, -, hall⟩ := low_third H hv.1 hv.2 hw.1 hw.2 hvw
    have y1 := hY v hv.1 hv.2
    have y2 := hY w hw.1 hw.2
    by_contra hne
    have c1 := cov v w u hall 0 ((κ v).boxY a + a) (by omega) (by omega)
    have c2 := cov v w u hall (a - 1) ((κ v).boxY a + a) (by omega) (by omega)
    omega
  obtain ⟨-, -, ⟨p, hp⟩, q, hq⟩ := lemma43b H hda hs
  obtain ⟨-, hp₀, hp₁, hpY⟩ := Finset.mem_filter.1 hp
  obtain ⟨-, hq₀, hq₁, hqY⟩ := Finset.mem_filter.1 hq
  have hvw : v ≠ w := by
    rintro rfl
    omega
  obtain ⟨u, hu₀, hu₁, huv, huw, hall⟩ := low_third H hv.1 hv.2 hw.1 hw.2 hvw
  have y1 := hY v hv.1 hv.2
  have y2 := hY w hw.1 hw.2
  have y3 := hY u hu₀ hu₁
  have hpq := touch p q ⟨hp₀, hp₁⟩ ⟨hq₀, hq₁⟩ (by omega)
  have hbs : b = 2 * a + 2 * s := by omega
  have hyv : (κ v).boxY a = s := by omega
  have hyw : (κ w).boxY a = s + a := by omega
  have xv := (low_range H hv.1 hv.2).1
  have xw := (low_range H hw.1 hw.2).1
  have xu := (low_range H hu₀ hu₁).1
  have c1 := cov v w u hall 0 (s + a - 1) (by omega) (by omega)
  have c2 := cov v w u hall (a - 1) (s + a - 1) (by omega) (by omega)
  have c3 := cov v w u hall 0 (s + a) (by omega) (by omega)
  have c4 := cov v w u hall (a - 1) (s + a) (by omega) (by omega)
  have c5 := cov v w u hall 0 d (by omega) (by omega)
  have c6 := cov v w u hall (a - 1) d (by omega) (by omega)
  have c7 := cov v w u hall 0 (b - d - 1) (by omega) (by omega)
  have c8 := cov v w u hall (a - 1) (b - d - 1) (by omega) (by omega)
  have hyu : s + 1 ≤ (κ u).boxY a ∧ (κ u).boxY a ≤ s + a - 1 := by omega
  have hyud : a + 2 * s - d ≤ (κ u).boxY a ∧ (κ u).boxY a ≤ d := by omega
  have hx : (κ v).boxX d = 0 ∧ (κ w).boxX d = 0 ∧ (κ u).boxX d = a - d ∨
      (κ v).boxX d = a - d ∧ (κ w).boxX d = a - d ∧ (κ u).boxX d = 0 := by omega
  rcases hx with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Prop44Stack.absurd ⟨H, hda, hs, hv, hw, ⟨hu₀, hu₁⟩, ⟨huv, huw, hvw⟩, hall, hbs, hyv,
      hyw, hyu, hyud, h1, h2, h3⟩
  · obtain ⟨mv, mv'⟩ := prop44_mirror_box (a := a) (d := d) (H.vert v hv.1 hv.2)
    obtain ⟨mw, mw'⟩ := prop44_mirror_box (a := a) (d := d) (H.vert w hw.1 hw.2)
    obtain ⟨mu, mu'⟩ := prop44_mirror_box (a := a) (d := d) (H.vert u hu₀ hu₁)
    refine Prop44Stack.absurd (v := v) (w := w) (u := u) ⟨H.mirror, hda,
      prop44_mirror_fullRows hs, hv, hw, ⟨hu₀, hu₁⟩, ⟨huv, huw, hvw⟩, hall, hbs, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩ <;> omega

/-- Proposition 44. PROVISIONAL. Source: `report-4.md`, Proposition 44 (line 355):
"In case (II.3) with d < a the row ranges [y_i, y_i + a) of any two vertical tiles
overlap. So 2s + 1 <= h <= a + 2s - 1". -/
theorem proposition44 (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {s : ℤ}
    (hs : FullRows (t i₀) a s) :
    (∀ v w, v ≠ i₀ → v ≠ i₁ → w ≠ i₀ → w ≠ i₁ → (κ w).boxY a < (κ v).boxY a + a) ∧
      b - a ≤ a + 2 * s - 1 := by
  have key : ∀ v w, v ≠ i₀ → v ≠ i₁ → w ≠ i₀ → w ≠ i₁ →
      (κ w).boxY a < (κ v).boxY a + a := by
    intro v w hv₀ hv₁ hw₀ hw₁
    by_contra hlt
    exact prop44_stack H hda hs ⟨hv₀, hv₁⟩ ⟨hw₀, hw₁⟩ (by omega)
  refine ⟨key, ?_⟩
  obtain ⟨-, -, ⟨p, hp⟩, q, hq⟩ := lemma43b H hda hs
  obtain ⟨-, hp₀, hp₁, hpY⟩ := Finset.mem_filter.1 hp
  obtain ⟨-, hq₀, hq₁, hqY⟩ := Finset.mem_filter.1 hq
  have := key p q hp₀ hp₁ hq₀ hq₁
  omega

/-! ## Section 5f: wall states (used for `G = H` only) -/

/-! ### Working lemmas of sections 5f to 5h -/

/-- Coordinates of a cell of a tile. -/
private theorem high_bounds (F : Frame a b d t i₀ κ) {i : Fin 5} {x y : ℤ}
    (hc : (x, y) ∈ t i) : (0 ≤ x ∧ x < a) ∧ 0 ≤ y ∧ y < b :=
  mem_R.1 (F.isTiling.subset_R i hc)

/-- The cells of `T` lie in the rows `[0, d)`. -/
private theorem high_low (F : Frame a b d t i₀ κ) {x y : ℤ} (hc : (x, y) ∈ t i₀) :
    0 ≤ y ∧ y < d := by
  have h : y ∈ ySpan (t i₀) := mem_ySpan.2 ⟨_, hc, _, hc, le_rfl, le_rfl⟩
  rwa [F.rows, Finset.mem_Ico] at h

/-- A vertical tile lies in its box. -/
private theorem high_box (F : Frame a b d t i₀ κ) {i : Fin 5} (hi : (κ i).swap = true)
    {x y : ℤ} (hc : (x, y) ∈ t i) :
    ((κ i).boxX d ≤ x ∧ x < (κ i).boxX d + d) ∧
      (κ i).boxY a ≤ y ∧ y < (κ i).boxY a + a := by
  obtain ⟨-, hx, hy, -, -⟩ := F.vertical_spine hi
  have h1 : x ∈ xSpan (t i) := mem_xSpan.2 ⟨_, hc, _, hc, le_rfl, le_rfl⟩
  have h2 : y ∈ ySpan (t i) := mem_ySpan.2 ⟨_, hc, _, hc, le_rfl, le_rfl⟩
  rw [hx, Finset.mem_Ico] at h1
  rw [hy, Finset.mem_Ico] at h2
  exact ⟨h1, h2⟩

/-- The cells of a vertical tile in the coordinates of its box. -/
private theorem high_mem (F : Frame a b d t i₀ κ) {i : Fin 5} (hi : (κ i).swap = true)
    (x y : ℤ) : (x, y) ∈ t i ↔
      ((if (κ i).negY then (κ i).boxY a + a - 1 - y else y - (κ i).boxY a),
        (if (κ i).negX then (κ i).shift.1 - x else x - (κ i).shift.1)) ∈ t i₀ := by
  rw [← F.vertical_mem hi]
  unfold GridIso.boxY
  refine iff_of_eq (congrArg (· ∈ t i) (Prod.ext ?_ ?_)) <;>
    cases (κ i).negX <;> cases (κ i).negY <;>
    simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega

/-- The spine side of a vertical tile and the first column of its box. -/
private theorem high_side (g : GridIso) (d : ℤ) :
    g.negX = false ∧ g.boxX d = g.shift.1 ∨ g.negX = true ∧ g.boxX d = g.shift.1 - (d - 1) := by
  unfold GridIso.boxX
  cases g.negX <;> simp

/-- A row without cells counts 0. -/
private theorem high_rowCount_zero {S : Finset Cell} {y : ℤ} (h : ∀ x : ℤ, (x, y) ∉ S) :
    rowCount S y = 0 := by
  unfold rowCount
  rw [Finset.filter_eq_empty_iff.2, Finset.card_empty, Nat.cast_zero]
  rintro ⟨x, y'⟩ hc rfl
  exact h x hc

/-- A row that is an interval of columns counts its length. -/
private theorem high_rowCount_interval {S : Finset Cell} {y p q : ℤ} (hpq : p ≤ q)
    (h : ∀ x : ℤ, (x, y) ∈ S ↔ p ≤ x ∧ x < q) : rowCount S y = q - p := by
  have hrow : (S.filter fun c => c.2 = y) = Finset.Ico p q ×ˢ ({y} : Finset ℤ) := by
    ext ⟨x, y'⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, rfl⟩
      exact ⟨(h x).1 hc, rfl⟩
    · rintro ⟨hc, rfl⟩
      exact ⟨(h x).2 hc, rfl⟩
  unfold rowCount
  rw [hrow, Finset.card_product, Finset.card_singleton, mul_one, Int.card_Ico]
  omega

/-- The number of full rows is less than `d`. -/
private theorem high_s_lt (F : Frame a b d t i₀ κ) {s : ℤ} (hs : FullRows (t i₀) a s) :
    0 ≤ s ∧ s < d := by
  refine ⟨hs.1, ?_⟩
  by_contra hlt
  obtain ⟨s', h1, h2, -, -, x, hx0, hxa, hx⟩ := F.exists_fullRows
  exact hx (hs.2.1 x s' hx0 hxa (by omega) (by omega))

/-- The end columns of `T` hold between 1 and `d` cells. -/
private theorem high_ends_pos (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) :
    (1 ≤ colCount (t i₀) 0 ∧ colCount (t i₀) 0 ≤ d) ∧
      1 ≤ colCount (t i₀) (a - 1) ∧ colCount (t i₀) (a - 1) ≤ d := by
  have F := H.frame
  have hd := F.two_le_d
  obtain ⟨h0, h1⟩ := lemma43a H hda
  have p0 := (h0 0).1 (F.row0 0 le_rfl (by omega))
  have p1 := (h1 0).1 (F.row0 (a - 1) (by omega) (by omega))
  refine ⟨⟨by omega, ?_⟩, by omega, ?_⟩
  · have := high_low F ((h0 (colCount (t i₀) 0 - 1)).2 (by omega))
    omega
  · have := high_low F ((h1 (colCount (t i₀) (a - 1) - 1)).2 (by omega))
    omega

/-- The end rows of the box of a vertical tile are intervals of columns starting at the
spine cell. Source: `report-4.md`, section 5g (line 403): "By Lemma 43(a) the bottom row
and the top row of its box are intervals of columns starting at the spine cell, one with
u_0 cells and one with u_1". Here `r` is the length of the bottom row and `r'` that of the
top row. -/
private theorem high_end_rows (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {v : Fin 5}
    (hv₀ : v ≠ i₀) (hv₁ : v ≠ i₁) :
    ∃ r r' : ℤ,
      ((κ v).negY = false ∧ r = colCount (t i₀) 0 ∧ r' = colCount (t i₀) (a - 1) ∨
        (κ v).negY = true ∧ r = colCount (t i₀) (a - 1) ∧ r' = colCount (t i₀) 0) ∧
      ((κ v).negX = false ∧ (κ v).boxX d = (κ v).shift.1 ∧
          (∀ x : ℤ, (x, (κ v).boxY a) ∈ t v ↔ (κ v).shift.1 ≤ x ∧ x < (κ v).shift.1 + r) ∧
          (∀ x : ℤ, (x, (κ v).boxY a + a - 1) ∈ t v ↔
            (κ v).shift.1 ≤ x ∧ x < (κ v).shift.1 + r') ∨
        (κ v).negX = true ∧ (κ v).boxX d = (κ v).shift.1 - (d - 1) ∧
          (∀ x : ℤ, (x, (κ v).boxY a) ∈ t v ↔ (κ v).shift.1 - r < x ∧ x ≤ (κ v).shift.1) ∧
          (∀ x : ℤ, (x, (κ v).boxY a + a - 1) ∈ t v ↔
            (κ v).shift.1 - r' < x ∧ x ≤ (κ v).shift.1)) ∧
      rowCount (t v) ((κ v).boxY a) = r ∧ rowCount (t v) ((κ v).boxY a + a - 1) = r' := by
  obtain ⟨h0, h1⟩ := lemma43a H hda
  have hpos := high_ends_pos H hda
  have hv := H.vert v hv₀ hv₁
  have hm := high_mem H.frame hv
  have e0 : (κ v).boxY a + a - 1 - (κ v).boxY a = a - 1 := by ring
  have e1 : (κ v).boxY a + a - 1 - ((κ v).boxY a + a - 1) = 0 := by ring
  have hb : ∃ r, ((κ v).negY = false ∧ r = colCount (t i₀) 0 ∨
      (κ v).negY = true ∧ r = colCount (t i₀) (a - 1)) ∧ ∀ x : ℤ, (x, (κ v).boxY a) ∈ t v ↔
        0 ≤ (if (κ v).negX then (κ v).shift.1 - x else x - (κ v).shift.1) ∧
          (if (κ v).negX then (κ v).shift.1 - x else x - (κ v).shift.1) < r := by
    cases hn : (κ v).negY
    · refine ⟨_, Or.inl ⟨rfl, rfl⟩, fun x => ?_⟩
      rw [hm, hn, ite_eq_right Bool.false_ne_true, sub_self]
      exact h0 _
    · refine ⟨_, Or.inr ⟨rfl, rfl⟩, fun x => ?_⟩
      rw [hm, hn, ite_eq_left rfl, e0]
      exact h1 _
  have ht : ∃ r, ((κ v).negY = false ∧ r = colCount (t i₀) (a - 1) ∨
      (κ v).negY = true ∧ r = colCount (t i₀) 0) ∧
      ∀ x : ℤ, (x, (κ v).boxY a + a - 1) ∈ t v ↔
        0 ≤ (if (κ v).negX then (κ v).shift.1 - x else x - (κ v).shift.1) ∧
          (if (κ v).negX then (κ v).shift.1 - x else x - (κ v).shift.1) < r := by
    cases hn : (κ v).negY
    · refine ⟨_, Or.inl ⟨rfl, rfl⟩, fun x => ?_⟩
      rw [hm, hn, ite_eq_right Bool.false_ne_true,
        show (κ v).boxY a + a - 1 - (κ v).boxY a = a - 1 by ring]
      exact h1 _
    · refine ⟨_, Or.inr ⟨rfl, rfl⟩, fun x => ?_⟩
      rw [hm, hn, ite_eq_left rfl, e1]
      exact h0 _
  obtain ⟨r, hr, hbr⟩ := hb
  obtain ⟨r', hr', htr⟩ := ht
  have hrpos : 1 ≤ r := by rcases hr with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hrpos' : 1 ≤ r' := by rcases hr' with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  refine ⟨r, r', ?_, ?_⟩
  · rcases hr with ⟨n, h⟩ | ⟨n, h⟩ <;> rcases hr' with ⟨n', h'⟩ | ⟨n', h'⟩
    · exact Or.inl ⟨n, h, h'⟩
    · rw [n] at n'
      exact absurd n' Bool.false_ne_true
    · rw [n'] at n
      exact absurd n Bool.false_ne_true
    · exact Or.inr ⟨n, h, h'⟩
  · rcases high_side (κ v) d with ⟨n, hx⟩ | ⟨n, hx⟩ <;>
      simp only [n, Bool.false_eq_true, ite_true, ite_false] at hbr htr
    · refine ⟨Or.inl ⟨n, hx, fun x => ?_, fun x => ?_⟩, ?_, ?_⟩
      · rw [hbr]; omega
      · rw [htr]; omega
      · rw [high_rowCount_interval (p := (κ v).shift.1) (q := (κ v).shift.1 + r) (by omega)
          fun x => by rw [hbr]; omega]
        ring
      · rw [high_rowCount_interval (p := (κ v).shift.1) (q := (κ v).shift.1 + r') (by omega)
          fun x => by rw [htr]; omega]
        ring
    · refine ⟨Or.inr ⟨n, hx, fun x => ?_, fun x => ?_⟩, ?_, ?_⟩
      · rw [hbr]; omega
      · rw [htr]; omega
      · rw [high_rowCount_interval (p := (κ v).shift.1 - r + 1) (q := (κ v).shift.1 + 1)
          (by omega) fun x => by rw [hbr]; omega]
        ring
      · rw [high_rowCount_interval (p := (κ v).shift.1 - r' + 1) (q := (κ v).shift.1 + 1)
          (by omega) fun x => by rw [htr]; omega]
        ring

/-- The spine cell of a vertical tile in a row of its box. -/
private theorem high_spine (H : TypeH2 a b d t i₀ i₁ κ) {v : Fin 5} (hv₀ : v ≠ i₀)
    (hv₁ : v ≠ i₁) {y : ℤ} (h1 : (κ v).boxY a ≤ y) (h2 : y < (κ v).boxY a + a) :
    ((κ v).shift.1, y) ∈ t v :=
  (H.frame.vertical_spine (H.vert v hv₀ hv₁)).1 y h1 h2

/-- A cell is in at most one tile. -/
private theorem high_unique (H : TypeH2 a b d t i₀ i₁ κ) {i j : Fin 5} {c : Cell}
    (hi : c ∈ t i) (hj : c ∈ t j) : i = j :=
  H.frame.isTiling.tile_unique hi hj

/-- Every cell of `R a b` is in a tile. -/
private theorem high_tile_at (H : TypeH2 a b d t i₀ i₁ κ) {x y : ℤ} (hx0 : 0 ≤ x) (hxa : x < a)
    (hy0 : 0 ≤ y) (hyb : y < b) : ∃ i, (x, y) ∈ t i :=
  H.frame.isTiling.exists_tile (mem_R.2 ⟨⟨hx0, hxa⟩, hy0, hyb⟩)

/-- Three different vertical tiles and the two horizontal ones are all five tiles. -/
private theorem high_all {p q r : Fin 5} (h : i₁ ≠ i₀) (hp₀ : p ≠ i₀) (hp₁ : p ≠ i₁)
    (hq₀ : q ≠ i₀) (hq₁ : q ≠ i₁) (hr₀ : r ≠ i₀) (hr₁ : r ≠ i₁) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (j : Fin 5) : j = i₀ ∨ j = i₁ ∨ j = p ∨ j = q ∨ j = r := by
  have hcard : ({i₀, i₁, p, q, r} : Finset (Fin 5)).card = 5 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_pair hqr] <;>
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    · exact ⟨hpq, hpr⟩
    · exact ⟨hp₁.symm, hq₁.symm, hr₁.symm⟩
    · exact ⟨h.symm, hp₀.symm, hq₀.symm, hr₀.symm⟩
  have huniv := Finset.eq_univ_of_card _ (hcard.trans (Fintype.card_fin 5).symm)
  have hj : j ∈ ({i₀, i₁, p, q, r} : Finset (Fin 5)) := huniv ▸ Finset.mem_univ j
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hj

/-- Two different vertical tiles leave a third one. -/
private theorem high_third (i₀ i₁ v w : Fin 5) :
    ∃ u : Fin 5, u ≠ i₀ ∧ u ≠ i₁ ∧ u ≠ v ∧ u ≠ w := by
  by_contra hno
  have h1 : ∀ j : Fin 5, j ∈ ({i₀, i₁, v, w} : Finset (Fin 5)) := by
    intro j
    by_contra hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    exact hno ⟨j, hj⟩
  have h2 := Finset.card_le_card fun j (_ : j ∈ Finset.univ) => h1 j
  have h3 : ({i₀, i₁, v, w} : Finset (Fin 5)).card ≤ 4 := Finset.card_le_four
  rw [Finset.card_univ, Fintype.card_fin] at h2
  omega

/-- A column without cells counts 0. -/
private theorem lemma45_colCount_zero {S : Finset Cell} {x : ℤ} (h : ∀ y : ℤ, (x, y) ∉ S) :
    colCount S x = 0 := by
  unfold colCount
  rw [Finset.filter_eq_empty_iff.2, Finset.card_empty, Nat.cast_zero]
  rintro ⟨x', y⟩ hc rfl
  exact h y hc

/-- Vertical tiles with the same spine column are the same tile. Source: `report-4.md`,
section 5f (line 369): "the three spines lie in distinct columns". -/
private theorem lemma45_spine_inj (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {v w : Fin 5}
    (hv₀ : v ≠ i₀) (hv₁ : v ≠ i₁) (hw₀ : w ≠ i₀) (hw₁ : w ≠ i₁)
    (h : (κ v).shift.1 = (κ w).shift.1) : v = w := by
  wlog hy : (κ v).boxY a ≤ (κ w).boxY a generalizing v w
  · exact (this hw₀ hw₁ hv₀ hv₁ h.symm (by omega)).symm
  obtain ⟨s, -, -, hs⟩ := H.frame.exists_fullRows
  have h44 := (proposition44 H hda hs).1 v w hv₀ hv₁ hw₀ hw₁
  have h1 := high_spine H hv₀ hv₁ (y := (κ w).boxY a) (by omega) (by omega)
  have h2 := high_spine H hw₀ hw₁ (y := (κ w).boxY a) (by omega) (by omega)
  rw [h] at h1
  exact high_unique H h1 h2

/-- Vertical tiles at the same wall with the spine on the same side are the same tile. -/
private theorem lemma45_wall_inj (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {v w : Fin 5}
    (hv₀ : v ≠ i₀) (hv₁ : v ≠ i₁) (hw₀ : w ≠ i₀) (hw₁ : w ≠ i₁)
    (h : (κ v).boxX d = (κ w).boxX d) (hn : (κ v).negX = (κ w).negX) : v = w := by
  refine lemma45_spine_inj H hda hv₀ hv₁ hw₀ hw₁ ?_
  rcases high_side (κ v) d with ⟨n, hx⟩ | ⟨n, hx⟩ <;>
    rcases high_side (κ w) d with ⟨n', hx'⟩ | ⟨n', hx'⟩
  · omega
  · rw [n, n'] at hn
    exact absurd hn Bool.false_ne_true
  · rw [n, n'] at hn
    exact absurd hn.symm Bool.false_ne_true
  · omega

/-- A vertical tile away from the left wall has no cell in column 0. -/
private theorem lemma45_col_away (H : TypeH2 a b d t i₀ i₁ κ) {v : Fin 5} (hv₀ : v ≠ i₀)
    (hv₁ : v ≠ i₁) (hx : (κ v).boxX d ≠ 0) : colCount (t v) 0 = 0 := by
  have hv := H.vert v hv₀ hv₁
  have hb := (H.frame.vertical_spine hv).2.2.2.1
  refine lemma45_colCount_zero fun y hy => ?_
  have h := (high_box H.frame hv hy).1
  omega

/-- A vertical tile with spine column 0 has `a` cells there. -/
private theorem lemma45_col_spine (H : TypeH2 a b d t i₀ i₁ κ) {v : Fin 5} (hv₀ : v ≠ i₀)
    (hv₁ : v ≠ i₁) (hx : (κ v).boxX d = 0) (hn : (κ v).negX = false) :
    colCount (t v) 0 = a := by
  have F := H.frame
  have ha := F.two_le.1
  have h := F.vertical_colCount (H.vert v hv₀ hv₁) 0
  have hrow : rowCount (t i₀) 0 = a := by
    rw [high_rowCount_interval (p := 0) (q := a) (by omega) fun x =>
      ⟨fun hc => (high_bounds F hc).1, fun hc => F.row0 x hc.1 hc.2⟩, sub_zero]
  simp only [GridIso.boxX, hn, Bool.false_eq_true, ite_false] at hx
  rwa [hn, ite_eq_right Bool.false_ne_true, hx, add_zero, hrow] at h

/-- A vertical tile at the left wall with spine column `d - 1` has `t` cells in column 0. -/
private theorem lemma45_col_far (H : TypeH2 a b d t i₀ i₁ κ) {v : Fin 5} (hv₀ : v ≠ i₀)
    (hv₁ : v ≠ i₁) (hx : (κ v).boxX d = 0) (hn : (κ v).negX = true) :
    colCount (t v) 0 = rowCount (t i₀) (d - 1) := by
  have h := H.frame.vertical_colCount (H.vert v hv₀ hv₁) (d - 1)
  simp only [GridIso.boxX, hn, ite_true] at hx
  rwa [hn, ite_eq_left rfl, show -(d - 1) + (κ v).shift.1 = 0 by omega] at h

/-- The count of column 0, with `J` the vertical tiles that meet it. -/
private theorem lemma45_sum (H : TypeH2 a b d t i₀ i₁ κ) (J : Finset (Fin 5)) (h₀ : i₀ ∉ J)
    (h₁ : i₁ ∉ J) (hJ : ∀ j, j ≠ i₀ → j ≠ i₁ → j ∉ J → (κ j).boxX d ≠ 0) :
    colCount (t i₀) 0 + (colCount (t i₁) 0 + ∑ v ∈ J, colCount (t v) 0) = b := by
  have ha := H.frame.two_le
  have hn : i₀ ∉ insert i₁ J := by
    rw [Finset.mem_insert, not_or]
    exact ⟨H.ne.symm, h₀⟩
  rw [← Finset.sum_insert (f := fun v => colCount (t v) 0) h₁,
    ← Finset.sum_insert (f := fun v => colCount (t v) 0) hn,
    Finset.sum_subset (Finset.subset_univ _)]
  · exact sum_colCount_of_cover t H.frame.disjoint H.frame.cover (by omega) le_rfl (by omega)
  · intro j _ hj
    rw [Finset.mem_insert, Finset.mem_insert, not_or, not_or] at hj
    exact lemma45_col_away H hj.1 hj.2.1 (hJ j hj.1 hj.2.1 hj.2.2)

/-- `T'` meets column 0 in its top rows. Source: `report-4.md`, Lemma 43 (a) (line 347). -/
private theorem lemma45_top_col (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) (y : ℤ) :
    (0, y) ∈ t i₁ ↔ b - colCount (t i₁) 0 ≤ y ∧ y < b := by
  obtain ⟨h0, h1⟩ := lemma43a H hda
  rw [H.top_mem, H.top_colCount]
  cases (κ i₁).negX
  · simp only [Bool.false_eq_true, ite_false, h0]
    omega
  · simp only [ite_true, sub_zero, h1]
    omega

/-- Lemma 45 (a), numeric part, at column 0. PROVISIONAL and UNSURE of the best
form. Source: `report-4.md`, Lemma 45 (a) (lines 373-377): with `u'_0` the number of
cells of `T'` in column 0, the vertical tiles with `x_i = 0` are none (state o,
`u_0 + u'_0 = b`), one with spine column 0 (alpha, `y = u_0`, `u_0 + u'_0 = h`),
one with spine column `d - 1` (beta, `t = a + h - u_0 - u'_0`) or two (gamma,
`t = h - u_0 - u'_0`). The states at column `a - 1` are those of the mirror image
(`TypeH2.mirror`). -/
theorem lemma45a (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {s : ℤ}
    (hs : FullRows (t i₀) a s) :
    ((∀ v, v ≠ i₀ → v ≠ i₁ → (κ v).boxX d ≠ 0) ∧
        colCount (t i₀) 0 + colCount (t i₁) 0 = b) ∨
      (∃ v, v ≠ i₀ ∧ v ≠ i₁ ∧ (κ v).boxX d = 0 ∧ (κ v).negX = false ∧
        (∀ w, w ≠ i₀ → w ≠ i₁ → (κ w).boxX d = 0 → w = v) ∧
        (κ v).boxY a = colCount (t i₀) 0 ∧
        colCount (t i₀) 0 + colCount (t i₁) 0 = b - a) ∨
      (∃ v, v ≠ i₀ ∧ v ≠ i₁ ∧ (κ v).boxX d = 0 ∧ (κ v).negX = true ∧
        (∀ w, w ≠ i₀ → w ≠ i₁ → (κ w).boxX d = 0 → w = v) ∧
        rowCount (t i₀) (d - 1) = a + (b - a) - colCount (t i₀) 0 - colCount (t i₁) 0) ∨
      (∃ v v', v ≠ i₀ ∧ v ≠ i₁ ∧ v' ≠ i₀ ∧ v' ≠ i₁ ∧ (κ v).boxX d = 0 ∧ (κ v').boxX d = 0 ∧
        (κ v).negX = false ∧ (κ v').negX = true ∧
        rowCount (t i₀) (d - 1) = (b - a) - colCount (t i₀) 0 - colCount (t i₁) 0) := by
  have _ := hs -- not needed: `exists_fullRows` gives the number
  have F := H.frame
  have ha := F.two_le.1
  have hT := (lemma43a H hda).1
  have hT' := lemma45_top_col H hda
  by_cases hα : ∃ v, v ≠ i₀ ∧ v ≠ i₁ ∧ (κ v).boxX d = 0 ∧ (κ v).negX = false <;>
    by_cases hβ : ∃ v, v ≠ i₀ ∧ v ≠ i₁ ∧ (κ v).boxX d = 0 ∧ (κ v).negX = true
  · obtain ⟨v, hv₀, hv₁, hx, hn⟩ := hα
    obtain ⟨w, hw₀, hw₁, hx', hn'⟩ := hβ
    have hvw : v ≠ w := by
      rintro rfl
      rw [hn] at hn'
      exact Bool.false_ne_true hn'
    refine Or.inr (Or.inr (Or.inr ⟨v, w, hv₀, hv₁, hw₀, hw₁, hx, hx', hn, hn', ?_⟩))
    have h := lemma45_sum H {v, w}
      (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hv₀.symm, hw₀.symm⟩)
      (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hv₁.symm, hw₁.symm⟩)
      fun j hj₀ hj₁ hj hjx => by
        rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
        cases hjn : (κ j).negX
        · exact hj.1 (lemma45_wall_inj H hda hj₀ hj₁ hv₀ hv₁ (hjx.trans hx.symm)
            (hjn.trans hn.symm))
        · exact hj.2 (lemma45_wall_inj H hda hj₀ hj₁ hw₀ hw₁ (hjx.trans hx'.symm)
            (hjn.trans hn'.symm))
    rw [Finset.sum_pair hvw, lemma45_col_spine H hv₀ hv₁ hx hn,
      lemma45_col_far H hw₀ hw₁ hx' hn'] at h
    omega
  · obtain ⟨v, hv₀, hv₁, hx, hn⟩ := hα
    have huniq : ∀ w, w ≠ i₀ → w ≠ i₁ → (κ w).boxX d = 0 → w = v := by
      intro w hw₀ hw₁ hwx
      cases hwn : (κ w).negX
      · exact lemma45_wall_inj H hda hw₀ hw₁ hv₀ hv₁ (hwx.trans hx.symm) (hwn.trans hn.symm)
      · exact absurd ⟨w, hw₀, hw₁, hwx, hwn⟩ hβ
    have h := lemma45_sum H {v} (by simpa using hv₀.symm) (by simpa using hv₁.symm)
      fun j hj₀ hj₁ hj hjx => hj (Finset.mem_singleton.2 (huniq j hj₀ hj₁ hjx))
    rw [Finset.sum_singleton, lemma45_col_spine H hv₀ hv₁ hx hn] at h
    have hc : (κ v).shift.1 = 0 := by
      simpa only [GridIso.boxX, hn, Bool.false_eq_true, ite_false] using hx
    have hb := (F.vertical_spine (H.vert v hv₀ hv₁)).2.2.2.2
    have s1 := high_spine H hv₀ hv₁ (y := (κ v).boxY a) le_rfl (by omega)
    have s2 := high_spine H hv₀ hv₁ (y := (κ v).boxY a + a - 1) (by omega) (by omega)
    rw [hc] at s1 s2
    have n1 : ((0, (κ v).boxY a) : Cell) ∉ t i₀ := fun h' => hv₀ (high_unique H s1 h')
    have n2 : ((0, (κ v).boxY a + a - 1) : Cell) ∉ t i₁ := fun h' => hv₁ (high_unique H s2 h')
    rw [hT] at n1
    rw [hT'] at n2
    exact Or.inr (Or.inl ⟨v, hv₀, hv₁, hx, hn, huniq, by omega, by omega⟩)
  · obtain ⟨v, hv₀, hv₁, hx, hn⟩ := hβ
    have huniq : ∀ w, w ≠ i₀ → w ≠ i₁ → (κ w).boxX d = 0 → w = v := by
      intro w hw₀ hw₁ hwx
      cases hwn : (κ w).negX
      · exact absurd ⟨w, hw₀, hw₁, hwx, hwn⟩ hα
      · exact lemma45_wall_inj H hda hw₀ hw₁ hv₀ hv₁ (hwx.trans hx.symm) (hwn.trans hn.symm)
    have h := lemma45_sum H {v} (by simpa using hv₀.symm) (by simpa using hv₁.symm)
      fun j hj₀ hj₁ hj hjx => hj (Finset.mem_singleton.2 (huniq j hj₀ hj₁ hjx))
    rw [Finset.sum_singleton, lemma45_col_far H hv₀ hv₁ hx hn] at h
    exact Or.inr (Or.inr (Or.inl ⟨v, hv₀, hv₁, hx, hn, huniq, by omega⟩))
  · have hno : ∀ v, v ≠ i₀ → v ≠ i₁ → (κ v).boxX d ≠ 0 := by
      intro v hv₀ hv₁ hx
      cases hn : (κ v).negX
      · exact hα ⟨v, hv₀, hv₁, hx, hn⟩
      · exact hβ ⟨v, hv₀, hv₁, hx, hn⟩
    have h := lemma45_sum H ∅ (Finset.notMem_empty _) (Finset.notMem_empty _)
      fun j hj₀ hj₁ _ => hno j hj₀ hj₁
    rw [Finset.sum_empty] at h
    exact Or.inl ⟨hno, by omega⟩

/-- The switches and the box of a vertical tile in the mirror image. -/
private theorem lemma45_mirror (a d : ℤ) {g : GridIso} (hg : g.swap = true) :
    ((GridIso.flipX a).comp (g.comp (GridIso.flipX a))).negX = !g.negX ∧
      ((GridIso.flipX a).comp (g.comp (GridIso.flipX a))).boxX d = a - d - g.boxX d ∧
      ((GridIso.flipX a).comp (g.comp (GridIso.flipX a))).boxY a = g.boxY a := by
  obtain ⟨s, n, m, u, v⟩ := g
  dsimp only at hg
  subst hg
  cases n <;> cases m <;>
    simp [GridIso.comp, GridIso.boxX, GridIso.boxY, GridIso.flipX, GridIso.apply] <;> omega

/-- Lemma 45 (a) at column `a - 1`: the mirror image of `lemma45a`. -/
private theorem lemma45a_right (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) :
    ((∀ v, v ≠ i₀ → v ≠ i₁ → (κ v).boxX d ≠ a - d) ∧
        colCount (t i₀) (a - 1) + colCount (t i₁) (a - 1) = b) ∨
      (∃ v, v ≠ i₀ ∧ v ≠ i₁ ∧ (κ v).boxX d = a - d ∧ (κ v).negX = true ∧
        (κ v).boxY a = colCount (t i₀) (a - 1) ∧
        colCount (t i₀) (a - 1) + colCount (t i₁) (a - 1) = b - a) ∨
      (∃ v, v ≠ i₀ ∧ v ≠ i₁ ∧ (κ v).boxX d = a - d ∧ (κ v).negX = false ∧
        rowCount (t i₀) (d - 1) =
          a + (b - a) - colCount (t i₀) (a - 1) - colCount (t i₁) (a - 1)) ∨
      (∃ v v', v ≠ i₀ ∧ v ≠ i₁ ∧ v' ≠ i₀ ∧ v' ≠ i₁ ∧ (κ v).boxX d = a - d ∧
        (κ v').boxX d = a - d ∧ (κ v).negX = true ∧ (κ v').negX = false ∧
        rowCount (t i₀) (d - 1) =
          (b - a) - colCount (t i₀) (a - 1) - colCount (t i₁) (a - 1)) := by
  obtain ⟨s, -, -, hs⟩ := H.mirror.frame.exists_fullRows
  have h := lemma45a H.mirror hda hs
  simp only [colCount_image_flipX, rowCount_image_flipX, sub_zero] at h
  have hm := fun v (hv₀ : v ≠ i₀) (hv₁ : v ≠ i₁) => lemma45_mirror a d (H.vert v hv₀ hv₁)
  rcases h with ⟨h1, h2⟩ | ⟨v, hv₀, hv₁, hx, hn, -, hy, h2⟩ | ⟨v, hv₀, hv₁, hx, hn, -, h2⟩ |
    ⟨v, w, hv₀, hv₁, hw₀, hw₁, hx, hx', hn, hn', h2⟩
  · refine Or.inl ⟨fun v hv₀ hv₁ hx => h1 v hv₀ hv₁ ?_, h2⟩
    rw [(hm v hv₀ hv₁).2.1]
    omega
  · rw [(hm v hv₀ hv₁).2.1] at hx
    rw [(hm v hv₀ hv₁).1, Bool.not_eq_false'] at hn
    rw [(hm v hv₀ hv₁).2.2] at hy
    exact Or.inr (Or.inl ⟨v, hv₀, hv₁, by omega, hn, hy, h2⟩)
  · rw [(hm v hv₀ hv₁).2.1] at hx
    rw [(hm v hv₀ hv₁).1, Bool.not_eq_true'] at hn
    exact Or.inr (Or.inr (Or.inl ⟨v, hv₀, hv₁, by omega, hn, h2⟩))
  · rw [(hm v hv₀ hv₁).2.1] at hx
    rw [(hm v hv₀ hv₁).1, Bool.not_eq_false'] at hn
    rw [(hm w hw₀ hw₁).2.1] at hx'
    rw [(hm w hw₀ hw₁).1, Bool.not_eq_true'] at hn'
    exact Or.inr (Or.inr (Or.inr ⟨v, w, hv₀, hv₁, hw₀, hw₁, by omega, by omega, hn, hn', h2⟩))

/-- The spine column of a bottom tile has no cell of `T` in row `d - 1`. Source:
`report-4.md`, Lemma 45, proof (line 381): "the spine column of a bottom tile is not in
Top". -/
private theorem lemma45_bottom_spine (H : TypeH2 a b d t i₀ i₁ κ) {s : ℤ}
    (hs : FullRows (t i₀) a s) {v : Fin 5} (hv : v ∈ bottomTiles a s κ i₀ i₁) :
    ((κ v).shift.1, d - 1) ∉ t i₀ := by
  have F := H.frame
  simp only [bottomTiles, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  obtain ⟨hv₀, hv₁, hy⟩ := hv
  have hsd := high_s_lt F hs
  have hda := (F.vertical_bounds (H.vert v hv₀ hv₁)).1
  intro h
  exact hv₀ (high_unique H (high_spine H hv₀ hv₁ (by omega) (by omega)) h)

/-- `1 <= t < a`: row `d - 1` of `T` is neither empty nor full. -/
private theorem lemma45_t_bounds (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) :
    1 ≤ rowCount (t i₀) (d - 1) ∧ rowCount (t i₀) (d - 1) < a := by
  have F := H.frame
  have hd := F.two_le_d
  obtain ⟨s, -, -, hs⟩ := F.exists_fullRows
  obtain ⟨-, -, ⟨v, hv⟩, -⟩ := lemma43b H hda hs
  have hno := lemma45_bottom_spine H hs hv
  simp only [bottomTiles, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  have hbd := high_bounds F (high_spine H hv.1 hv.2.1 (y := (κ v).boxY a) le_rfl (by omega))
  obtain ⟨x, hx⟩ := F.exists_in_row (y := d - 1) (by omega) (by omega)
  constructor
  · have : 0 < ((t i₀).filter fun c => c.2 = d - 1).card :=
      Finset.card_pos.2 ⟨_, Finset.mem_filter.2 ⟨hx, rfl⟩⟩
    unfold rowCount
    omega
  · have hsub : ((t i₀).filter fun c => c.2 = d - 1) ⊂
        Finset.Ico 0 a ×ˢ ({d - 1} : Finset ℤ) := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨((κ v).shift.1, d - 1), ?_, fun h => hno (Finset.mem_filter.1 h).1⟩
        rw [Finset.mem_product, Finset.mem_Ico, Finset.mem_singleton]
        exact ⟨hbd.1, rfl⟩
      · rintro ⟨x, y⟩ hc
        rw [Finset.mem_filter] at hc
        rw [Finset.mem_product, Finset.mem_Ico, Finset.mem_singleton]
        exact ⟨(high_bounds F hc.1).1, hc.2⟩
    have h := Finset.card_lt_card hsub
    rw [Finset.card_product, Finset.card_singleton, mul_one, Int.card_Ico] at h
    unfold rowCount
    omega

/-- Lemma 45 (b). PROVISIONAL and UNSURE of the best form. Source: `report-4.md`,
Lemma 45 (b) (line 378): "G = H: with K = u_0 + u_1 the two walls are in the same
state, (o, o) with K = b, (alpha, alpha) with K = h, or (beta, beta) with
t = a + h - K." Stated as: no wall has two vertical tiles, and the three numeric
alternatives. -/
theorem lemma45b (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {s : ℤ}
    (hs : FullRows (t i₀) a s) (hG : (κ i₁).negX = true) :
    ((∀ v, v ≠ i₀ → v ≠ i₁ → (κ v).boxX d ≠ 0 ∧ (κ v).boxX d ≠ a - d) ∧
        colCount (t i₀) 0 + colCount (t i₀) (a - 1) = b) ∨
      (∃ v w, v ≠ i₀ ∧ v ≠ i₁ ∧ w ≠ i₀ ∧ w ≠ i₁ ∧ (κ v).shift.1 = 0 ∧
        (κ w).shift.1 = a - 1 ∧ (κ v).boxY a = colCount (t i₀) 0 ∧
        (κ w).boxY a = colCount (t i₀) (a - 1) ∧
        colCount (t i₀) 0 + colCount (t i₀) (a - 1) = b - a) ∨
      (∃ v w, v ≠ i₀ ∧ v ≠ i₁ ∧ w ≠ i₀ ∧ w ≠ i₁ ∧ (κ v).boxX d = 0 ∧
        (κ v).shift.1 = d - 1 ∧ (κ w).boxX d = a - d ∧ (κ w).shift.1 = a - d ∧
        rowCount (t i₀) (d - 1) =
          a + (b - a) - colCount (t i₀) 0 - colCount (t i₀) (a - 1)) := by
  have _ := hs -- not needed: `exists_fullRows` gives the number
  have F := H.frame
  have ha := F.two_le.1
  have hd := F.two_le_d
  have ht := lemma45_t_bounds H hda
  obtain ⟨s', -, -, hs'⟩ := F.exists_fullRows
  have hL := lemma45a H hda hs'
  have hR := lemma45a_right H hda
  have e0 : colCount (t i₁) 0 = colCount (t i₀) (a - 1) := by
    rw [H.top_colCount, hG, ite_eq_left rfl, sub_zero]
  have e1 : colCount (t i₁) (a - 1) = colCount (t i₀) 0 := by
    rw [H.top_colCount, hG, ite_eq_left rfl, sub_self]
  rw [e0] at hL
  rw [e1] at hR
  rcases hL with ⟨h1, h2⟩ | ⟨v, hv₀, hv₁, hx, hn, -, hy, h2⟩ | ⟨v, hv₀, hv₁, hx, hn, -, h2⟩ |
      ⟨v, v', hv₀, hv₁, hv₀', hv₁', hx, hx', hn, hn', h2⟩ <;>
    rcases hR with ⟨g1, g2⟩ | ⟨w, hw₀, hw₁, gx, gn, gy, g2⟩ | ⟨w, hw₀, hw₁, gx, gn, g2⟩ |
      ⟨w, w', hw₀, hw₁, hw₀', hw₁', gx, gx', gn, gn', g2⟩ <;>
    try (exfalso; omega)
  · exact Or.inl ⟨fun v hv₀ hv₁ => ⟨h1 v hv₀ hv₁, g1 v hv₀ hv₁⟩, h2⟩
  · simp only [GridIso.boxX, hn, Bool.false_eq_true, ite_false] at hx
    simp only [GridIso.boxX, gn, ite_true] at gx
    exact Or.inr (Or.inl ⟨v, w, hv₀, hv₁, hw₀, hw₁, hx, by omega, hy, gy, h2⟩)
  · have c1 : (κ v).shift.1 = d - 1 := by
      simp only [GridIso.boxX, hn, ite_true] at hx
      omega
    have c2 : (κ w).shift.1 = a - d := by
      simpa only [GridIso.boxX, gn, Bool.false_eq_true, ite_false] using gx
    exact Or.inr (Or.inr ⟨v, w, hv₀, hv₁, hw₀, hw₁, hx, c1, gx, c2, h2⟩)
  · exfalso
    have n1 : v ≠ v' := by
      rintro rfl
      rw [hn] at hn'
      exact Bool.false_ne_true hn'
    have n2 : w ≠ w' := by
      rintro rfl
      rw [gn] at gn'
      exact Bool.false_ne_true gn'.symm
    have n3 : ∀ {p q : Fin 5}, (κ p).boxX d = 0 → (κ q).boxX d = a - d → q ≠ p := by
      rintro p q hp hq rfl
      omega
    rcases high_all H.ne hv₀ hv₁ hv₀' hv₁' hw₀ hw₁ n1 (n3 hx gx).symm (n3 hx' gx).symm w' with
      h | h | h | h | h
    · exact hw₀' h
    · exact hw₁' h
    · exact n3 hx gx' h
    · exact n3 hx' gx' h
    · exact n2 h.symm

/-! ## Section 5g: end rows against spines -/

/-- Lemma 48 (a). PROVISIONAL. Source: `report-4.md`, Lemma 48 (a) (line 407): for
vertical tiles `X`, `Y` with `y_X <= y_Y`, the top row of `X` does not contain the
spine column of `Y`, and the bottom row of `Y` does not contain the spine column
of `X`. -/
theorem lemma48a (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {v w : Fin 5} (hv₀ : v ≠ i₀)
    (hv₁ : v ≠ i₁) (hw₀ : w ≠ i₀) (hw₁ : w ≠ i₁) (hvw : v ≠ w)
    (hy : (κ v).boxY a ≤ (κ w).boxY a) :
    ((κ w).shift.1, (κ v).boxY a + a - 1) ∉ t v ∧ ((κ v).shift.1, (κ w).boxY a) ∉ t w := by
  have F := H.frame
  obtain ⟨s, -, -, hs⟩ := F.exists_fullRows
  have h44 := (proposition44 H hda hs).1 v w hv₀ hv₁ hw₀ hw₁
  have ha := F.two_le.1
  constructor
  · intro h
    exact hvw (high_unique H h (high_spine H hw₀ hw₁ (by omega) (by omega)))
  · intro h
    exact hvw (high_unique H (high_spine H hv₀ hv₁ (by omega) (by omega)) h)

/-- Lemma 48 (b). PROVISIONAL. Source: `report-4.md`, Lemma 48 (b) (line 408): "If X
and Y have the spine on the same side of the box, then
|c_X - c_Y| >= min(u_0, u_1)." -/
theorem lemma48b (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {v w : Fin 5} (hv₀ : v ≠ i₀)
    (hv₁ : v ≠ i₁) (hw₀ : w ≠ i₀) (hw₁ : w ≠ i₁) (hvw : v ≠ w)
    (hside : (κ v).negX = (κ w).negX) :
    min (colCount (t i₀) 0) (colCount (t i₀) (a - 1)) ≤ |(κ v).shift.1 - (κ w).shift.1| := by
  wlog hy : (κ v).boxY a ≤ (κ w).boxY a generalizing v w
  · rw [abs_sub_comm]
    exact this hw₀ hw₁ hv₀ hv₁ hvw.symm hside.symm (by omega)
  obtain ⟨h1, h2⟩ := lemma48a H hda hv₀ hv₁ hw₀ hw₁ hvw hy
  obtain ⟨r, r', hr, hX, -⟩ := high_end_rows H hda hv₀ hv₁
  obtain ⟨q, q', hq, hY, -⟩ := high_end_rows H hda hw₀ hw₁
  by_contra hlt
  rw [not_le, lt_min_iff] at hlt
  obtain ⟨l0, l1⟩ := hlt
  rw [abs_lt] at l0 l1
  rcases hX with ⟨n, -, -, ht⟩ | ⟨n, -, -, ht⟩ <;> rcases hY with ⟨n', -, hb, -⟩ | ⟨n', -, hb, -⟩
  · rw [ht] at h1
    rw [hb] at h2
    omega
  · rw [n, n'] at hside
    exact absurd hside Bool.false_ne_true
  · rw [n, n'] at hside
    exact absurd hside.symm Bool.false_ne_true
  · rw [ht] at h1
    rw [hb] at h2
    omega

/-- Lemma 48 (c). PROVISIONAL. Source: `report-4.md`, Lemma 48 (c) (line 409):
"min(u_0, u_1) <= a - d." -/
theorem lemma48c (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) :
    min (colCount (t i₀) 0) (colCount (t i₀) (a - 1)) ≤ a - d := by
  have F := H.frame
  obtain ⟨p, hp₀, hp₁⟩ := exists_vertical5 i₀ i₁
  obtain ⟨q, hq₀, hq₁, hqp, -⟩ := high_third i₀ i₁ p p
  obtain ⟨r, hr₀, hr₁, hrp, hrq⟩ := high_third i₀ i₁ p q
  have key : ∀ v w, v ≠ i₀ → v ≠ i₁ → w ≠ i₀ → w ≠ i₁ → v ≠ w → (κ v).negX = (κ w).negX →
      min (colCount (t i₀) 0) (colCount (t i₀) (a - 1)) ≤ a - d := by
    intro v w hv₀ hv₁ hw₀ hw₁ hvw hside
    refine (lemma48b H hda hv₀ hv₁ hw₀ hw₁ hvw hside).trans ?_
    have bv := (F.vertical_spine (H.vert v hv₀ hv₁)).2.2.2.1
    have bw := (F.vertical_spine (H.vert w hw₀ hw₁)).2.2.2.1
    rw [abs_le]
    rcases high_side (κ v) d with ⟨n, h⟩ | ⟨n, h⟩ <;>
      rcases high_side (κ w) d with ⟨n', h'⟩ | ⟨n', h'⟩
    · omega
    · rw [n, n'] at hside
      exact absurd hside Bool.false_ne_true
    · rw [n, n'] at hside
      exact absurd hside.symm Bool.false_ne_true
    · omega
  by_cases h1 : (κ p).negX = (κ q).negX
  · exact key p q hp₀ hp₁ hq₀ hq₁ hqp.symm h1
  by_cases h2 : (κ p).negX = (κ r).negX
  · exact key p r hp₀ hp₁ hr₀ hr₁ hrp.symm h2
  refine key q r hq₀ hq₁ hr₀ hr₁ hrq.symm ?_
  cases hp : (κ p).negX <;> cases hq : (κ q).negX <;> cases hr : (κ r).negX <;> simp_all

/-! ## Section 5h: the extreme rows -/

/-- Lemma 52 (a), the count. PROVISIONAL. Source: `report-4.md`, Lemma 52 (a)
(line 445): the cells of row `s` outside `T` are the bottom rows of the bottom
tiles, the cells of row `b - 1 - s` outside `T'` are the top rows of the top
tiles, and `G` maps the first set onto the second; so the two sets have the same
number of cells. -/
theorem lemma52a (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {s : ℤ}
    (hs : FullRows (t i₀) a s) :
    (∀ v, v ≠ i₀ → v ≠ i₁ → ((∃ x : ℤ, (x, s) ∈ t v) ↔ v ∈ bottomTiles a s κ i₀ i₁)) ∧
      (∀ v, v ≠ i₀ → v ≠ i₁ →
        ((∃ x : ℤ, (x, b - 1 - s) ∈ t v) ↔ v ∈ upperTiles a b s κ i₀ i₁)) ∧
      ∑ v ∈ bottomTiles a s κ i₀ i₁, rowCount (t v) s =
        ∑ v ∈ upperTiles a b s κ i₀ i₁, rowCount (t v) (b - 1 - s) := by
  have F := H.frame
  have hsd := high_s_lt F hs
  have hd := F.two_le_d
  have hab : a ≤ b - 2 := (corollary42 H hs).1.2.2.2
  have h42 := (corollary42 H hs).2
  obtain ⟨hT', hT, -, -⟩ := lemma43b H hda hs
  have hbot : ∀ v, v ≠ i₀ → v ≠ i₁ →
      ((∃ x : ℤ, (x, s) ∈ t v) ↔ v ∈ bottomTiles a s κ i₀ i₁) := by
    intro v hv₀ hv₁
    have hv := H.vert v hv₀ hv₁
    simp only [bottomTiles, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx⟩
      have h1 := high_box F hv hx
      have h2 := h42 v hv₀ hv₁
      exact ⟨hv₀, hv₁, by omega⟩
    · rintro ⟨-, -, h⟩
      exact ⟨_, high_spine H hv₀ hv₁ (by omega) (by omega)⟩
  have htop : ∀ v, v ≠ i₀ → v ≠ i₁ →
      ((∃ x : ℤ, (x, b - 1 - s) ∈ t v) ↔ v ∈ upperTiles a b s κ i₀ i₁) := by
    intro v hv₀ hv₁
    have hv := H.vert v hv₀ hv₁
    simp only [upperTiles, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx⟩
      have h1 := high_box F hv hx
      have h2 := h42 v hv₀ hv₁
      exact ⟨hv₀, hv₁, by omega⟩
    · rintro ⟨-, -, h⟩
      exact ⟨_, high_spine H hv₀ hv₁ (by omega) (by omega)⟩
  refine ⟨hbot, htop, ?_⟩
  have sum_row : ∀ (J : Finset (Fin 5)) (i : Fin 5) (y : ℤ), 0 ≤ y → y < b → i ∉ J →
      (∀ j, j ≠ i → j ∉ J → ∀ x : ℤ, (x, y) ∉ t j) →
      rowCount (t i) y + ∑ v ∈ J, rowCount (t v) y = a := by
    intro J i y hy0 hyb hiJ hno
    rw [← Finset.sum_insert (f := fun v => rowCount (t v) y) hiJ,
      Finset.sum_subset (Finset.subset_univ _)]
    · exact sum_rowCount_of_cover t F.disjoint F.cover (by omega) hy0 hyb
    · intro j _ hj
      rw [Finset.mem_insert, not_or] at hj
      exact high_rowCount_zero (hno j hj.1 hj.2)
  have e1 := sum_row (bottomTiles a s κ i₀ i₁) i₀ s (by omega) (by omega) (by simp [bottomTiles])
    fun j hj hjJ x hx => by
      by_cases hj₁ : j = i₁
      · exact hT' x (hj₁ ▸ hx)
      · exact hjJ ((hbot j hj hj₁).1 ⟨x, hx⟩)
  have e2 := sum_row (upperTiles a b s κ i₀ i₁) i₁ (b - 1 - s) (by omega) (by omega)
    (by simp [upperTiles])
    fun j hj hjJ x hx => by
      by_cases hj₀ : j = i₀
      · exact hT x (hj₀ ▸ hx)
      · exact hjJ ((htop j hj₀ hj).1 ⟨x, hx⟩)
  rw [H.top_rowCount, show b - 1 - (b - 1 - s) = s by ring] at e2
  omega

/-- Lemma 52 (b), first sentence. PROVISIONAL. Source: `report-4.md`, Lemma 52 (b)
(line 446): "If u_0 = u_1 then P = Q = 1." -/
theorem lemma52b (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {s : ℤ}
    (hs : FullRows (t i₀) a s) (hu : colCount (t i₀) 0 = colCount (t i₀) (a - 1)) :
    (bottomTiles a s κ i₀ i₁).card = 1 ∧ (upperTiles a b s κ i₀ i₁).card = 1 := by
  have hpos := high_ends_pos H hda
  have hc := counts_bottom_top H hda hs
  have hsum := (lemma52a H hda hs).2.2
  have e1 : ∀ v ∈ bottomTiles a s κ i₀ i₁, rowCount (t v) s = colCount (t i₀) 0 := by
    intro v hv
    simp only [bottomTiles, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨r, r', hr, -, h, -⟩ := high_end_rows H hda hv.1 hv.2.1
    rw [hv.2.2] at h
    rcases hr with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ <;> omega
  have e2 : ∀ v ∈ upperTiles a b s κ i₀ i₁, rowCount (t v) (b - 1 - s) = colCount (t i₀) 0 := by
    intro v hv
    simp only [upperTiles, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨r, r', hr, -, -, h⟩ := high_end_rows H hda hv.1 hv.2.1
    rw [hv.2.2, show b - a - s + a - 1 = b - 1 - s by ring] at h
    rcases hr with ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> omega
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_const, Finset.sum_const,
    nsmul_eq_mul, nsmul_eq_mul] at hsum
  have heq := mul_right_cancel₀ (by omega : colCount (t i₀) 0 ≠ 0) hsum
  have heq' : (bottomTiles a s κ i₀ i₁).card = (upperTiles a b s κ i₀ i₁).card := by
    exact_mod_cast heq
  omega

/-- Lemma 52 (c). PROVISIONAL. Source: `report-4.md`, Lemma 52 (c) (line 447): "If
two vertical tiles X, Y have y_X = y_Y, the box of X does not contain the column
c_Y." -/
theorem lemma52c (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {v w : Fin 5} (hv₀ : v ≠ i₀)
    (hv₁ : v ≠ i₁) (hw₀ : w ≠ i₀) (hw₁ : w ≠ i₁) (hvw : v ≠ w)
    (hy : (κ v).boxY a = (κ w).boxY a) :
    ¬ ((κ v).boxX d ≤ (κ w).shift.1 ∧ (κ w).shift.1 < (κ v).boxX d + d) := by
  have _ := hda -- not needed: the box and the spine are enough
  intro hc
  have F := H.frame
  have hv := H.vert v hv₀ hv₁
  obtain ⟨-, hx, -, -, -⟩ := F.vertical_spine hv
  have hmem : (κ w).shift.1 ∈ xSpan (t v) := by
    rw [hx, Finset.mem_Ico]
    exact hc
  obtain ⟨p, hp, q, hq, h1, h2⟩ := mem_xSpan.1 hmem
  obtain ⟨y, hy⟩ := (F.isTiling.tile_isPolyomino F.poly v).2.exists_in_col hp hq h1 h2
  have hbox := (high_box F hv hy).2
  exact hvw (high_unique H hy (high_spine H hw₀ hw₁ (by omega) (by omega)))

/-- Lemma 52 (a), the cells. Source: `report-4.md`, Lemma 52 (a) (line 445): "The cells of
row s outside T are the bottom rows of the boxes of the P bottom tiles, and the cells of
row b - 1 - s outside T' are the top rows of the Q top tiles. G maps the first set onto
the second (same columns for G = F, columns reversed for G = H)." -/
private theorem lemma52_row_image (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {s : ℤ}
    (hs : FullRows (t i₀) a s) {x : ℤ} (hx0 : 0 ≤ x) (hxa : x < a) :
    (∃ v ∈ bottomTiles a s κ i₀ i₁, (x, s) ∈ t v) ↔
      ∃ w ∈ upperTiles a b s κ i₀ i₁,
        ((if (κ i₁).negX then a - 1 - x else x), b - 1 - s) ∈ t w := by
  have F := H.frame
  have hsd := high_s_lt F hs
  have hd := F.two_le_d
  obtain ⟨hT', hT, -, -⟩ := lemma43b H hda hs
  obtain ⟨hbot, htop, -⟩ := lemma52a H hda hs
  have hL : (∃ v ∈ bottomTiles a s κ i₀ i₁, (x, s) ∈ t v) ↔ (x, s) ∉ t i₀ := by
    constructor
    · rintro ⟨v, hv, hc⟩ h
      simp only [bottomTiles, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact hv.1 (high_unique H hc h)
    · intro h
      obtain ⟨j, hj⟩ := high_tile_at H hx0 hxa (y := s) (by omega) (by omega)
      have hj₀ : j ≠ i₀ := fun e => h (e ▸ hj)
      have hj₁ : j ≠ i₁ := fun e => hT' x (e ▸ hj)
      exact ⟨j, (hbot j hj₀ hj₁).1 ⟨x, hj⟩, hj⟩
  have hR : ∀ z : ℤ, 0 ≤ z → z < a →
      ((∃ w ∈ upperTiles a b s κ i₀ i₁, (z, b - 1 - s) ∈ t w) ↔ (z, b - 1 - s) ∉ t i₁) := by
    intro z hz0 hza
    constructor
    · rintro ⟨v, hv, hc⟩ h
      simp only [upperTiles, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact hv.2.1 (high_unique H hc h)
    · intro h
      obtain ⟨j, hj⟩ := high_tile_at H hz0 hza (y := b - 1 - s) (by omega) (by omega)
      have hj₁ : j ≠ i₁ := fun e => h (e ▸ hj)
      have hj₀ : j ≠ i₀ := fun e => hT z (e ▸ hj)
      exact ⟨j, (htop j hj₀ hj₁).1 ⟨z, hj⟩, hj⟩
  rw [hL, hR _ (by split <;> omega) (by split <;> omega), H.top_mem,
    show b - 1 - (b - 1 - s) = s by ring]
  have e : (if (κ i₁).negX then a - 1 - (if (κ i₁).negX then a - 1 - x else x)
      else (if (κ i₁).negX then a - 1 - x else x)) = x := by
    cases (κ i₁).negX <;> simp
  rw [e]

/-- The sum over the five tiles. -/
private theorem lemma53_sum {p q r : Fin 5} (h : i₁ ≠ i₀) (hp₀ : p ≠ i₀) (hp₁ : p ≠ i₁)
    (hq₀ : q ≠ i₀) (hq₁ : q ≠ i₁) (hr₀ : r ≠ i₀) (hr₁ : r ≠ i₁) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (f : Fin 5 → ℤ) : ∑ i, f i = f i₀ + f i₁ + f p + f q + f r := by
  have huniv : (Finset.univ : Finset (Fin 5)) = {i₀, i₁, p, q, r} := by
    ext j
    simpa only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton] using
      high_all h hp₀ hp₁ hq₀ hq₁ hr₀ hr₁ hpq hpr hqr j
  rw [huniv, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_pair hqr]
  · ring
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hpq, hpr⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hp₁.symm, hq₁.symm, hr₁.symm⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h.symm, hp₀.symm, hq₀.symm, hr₀.symm⟩

/-- The row counts of a vertical tile in the coordinates of its box. -/
private theorem lemma53_rowCount (H : TypeH2 a b d t i₀ i₁ κ) {v : Fin 5} (hv₀ : v ≠ i₀)
    (hv₁ : v ≠ i₁) (y : ℤ) : rowCount (t v) y = colCount (t i₀)
      (if (κ v).negY then (κ v).boxY a + a - 1 - y else y - (κ v).boxY a) := by
  rw [← H.frame.vertical_rowCount (H.vert v hv₀ hv₁)]
  unfold GridIso.boxY
  congr 1
  cases (κ v).negY <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega

/-- A row that counts at least 1 has a cell. -/
private theorem lemma53_pos {S : Finset Cell} {y : ℤ} (h : 1 ≤ rowCount S y) :
    ∃ x : ℤ, (x, y) ∈ S := by
  by_contra hno
  push Not at hno
  rw [high_rowCount_zero hno] at h
  omega

/-- A column whose cells lie in the rows `[p, q)` and count `q - p` is full there. -/
private theorem lemma53_fill {S : Finset Cell} {x p q : ℤ}
    (h : ∀ y : ℤ, (x, y) ∈ S → p ≤ y ∧ y < q) (hc : colCount S x = q - p) {y : ℤ}
    (hp : p ≤ y) (hq : y < q) : (x, y) ∈ S := by
  have hsub : (S.filter fun c => c.1 = x) ⊆ ({x} : Finset ℤ) ×ˢ Finset.Ico p q := by
    rintro ⟨x', y'⟩ hc'
    rw [Finset.mem_filter] at hc'
    obtain ⟨hc', hx⟩ := hc'
    dsimp only at hx
    subst hx
    rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico]
    exact ⟨rfl, h y' hc'⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    unfold colCount at hc
    rw [Finset.card_product, Finset.card_singleton, one_mul, Int.card_Ico]
    omega)
  have hmem : ((x, y) : Cell) ∈ S.filter fun c => c.1 = x := by
    rw [heq, Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico]
    exact ⟨rfl, hp, hq⟩
  exact (Finset.mem_filter.1 hmem).1

/-- Proposition 53 for `u_0 != u_1`. Source: `report-4.md`, Proposition 53 (line 456): the
row counts of `B` and of the image of `W` agree, so those of the third tile `U` are
symmetric under `r -> b - 1 - r`, and the two end rows of its box have equally many
cells. -/
private theorem proposition53_ne (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {s : ℤ}
    {B W : Fin 5} (hB₀ : B ≠ i₀) (hB₁ : B ≠ i₁) (hW₀ : W ≠ i₀) (hW₁ : W ≠ i₁) (hBW : B ≠ W)
    (yB : (κ B).boxY a = s) (yW : (κ W).boxY a = b - a - s)
    (hsum : rowCount (t B) s = rowCount (t W) (b - 1 - s))
    (hu : colCount (t i₀) 0 ≠ colCount (t i₀) (a - 1)) : False := by
  have F := H.frame
  have ha := F.two_le
  have hpos := high_ends_pos H hda
  obtain ⟨U, hU₀, hU₁, hUB, hUW⟩ := high_third i₀ i₁ B W
  -- `B` and `G(W)` carry the columns of `T` to their box rows in the same order
  obtain ⟨r, r', e1, -, n1, -⟩ := high_end_rows H hda hB₀ hB₁
  obtain ⟨q, q', e2, -, -, n2⟩ := high_end_rows H hda hW₀ hW₁
  rw [yB] at n1
  rw [yW, show b - a - s + a - 1 = b - 1 - s by ring] at n2
  have hcount : ∀ y : ℤ, rowCount (t B) y = rowCount (t W) (b - 1 - y) := by
    intro y
    rw [lemma53_rowCount H hB₀ hB₁, lemma53_rowCount H hW₀ hW₁, yB, yW]
    rcases e1 with ⟨m1, g1, -⟩ | ⟨m1, g1, -⟩ <;> rcases e2 with ⟨m2, -, g2⟩ | ⟨m2, -, g2⟩ <;>
      rw [m1, m2]
    · exfalso
      omega
    · rw [ite_eq_right Bool.false_ne_true, ite_eq_left rfl]
      congr 1
      ring
    · rw [ite_eq_right Bool.false_ne_true, ite_eq_left rfl]
      congr 1
      ring
    · exfalso
      omega
  -- the row counts of `U` are symmetric
  have hU : ∀ y : ℤ, 0 ≤ y → y < b → rowCount (t U) y = rowCount (t U) (b - 1 - y) := by
    intro y hy0 hyb
    have s1 := sum_rowCount_of_cover t F.disjoint F.cover (by omega) hy0 hyb
    have s2 := sum_rowCount_of_cover t F.disjoint F.cover (by omega)
      (y := b - 1 - y) (by omega) (by omega)
    rw [lemma53_sum H.ne hB₀ hB₁ hW₀ hW₁ hU₀ hU₁ hBW hUB.symm hUW.symm] at s1 s2
    have back : b - 1 - (b - 1 - y) = y := by ring
    have c1 := hcount y
    have c2 := hcount (b - 1 - y)
    rw [back] at c2
    have c3 := H.top_rowCount y
    have c4 := H.top_rowCount (b - 1 - y)
    rw [back] at c4
    omega
  -- so the rows of `U` are exchanged and its end rows have equally many cells
  have hvU := H.vert U hU₀ hU₁
  have bU := (F.vertical_spine hvU).2.2.2.2
  obtain ⟨p, p', e3, -, n3, n4⟩ := high_end_rows H hda hU₀ hU₁
  have hp : 1 ≤ p ∧ 1 ≤ p' ∧ p ≠ p' := by
    rcases e3 with ⟨-, g1, g2⟩ | ⟨-, g1, g2⟩ <;> omega
  have h1 := hU ((κ U).boxY a) (by omega) (by omega)
  have h2 := hU ((κ U).boxY a + a - 1) (by omega) (by omega)
  obtain ⟨x, hx⟩ := lemma53_pos (S := t U) (y := b - 1 - (κ U).boxY a) (by omega)
  obtain ⟨x', hx'⟩ := lemma53_pos (S := t U) (y := b - 1 - ((κ U).boxY a + a - 1)) (by omega)
  have g1 := (high_box F hvU hx).2
  have g2 := (high_box F hvU hx').2
  rw [show b - 1 - (κ U).boxY a = (κ U).boxY a + a - 1 by omega] at h1
  omega

/-- For `u_0 = u_1` both end rows of a vertical tile are the same interval, and it holds no
spine column of another tile. Source: `report-4.md`, Proposition 53 (line 457): "Both end
rows of a vertical tile V_i are then the same interval of columns J_i, the u columns from
c_i into its box. By Lemma 48(a) J_i contains no spine column of another tile". -/
private theorem lemma53_no_spine (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {v w : Fin 5}
    (hv₀ : v ≠ i₀) (hv₁ : v ≠ i₁) (hw₀ : w ≠ i₀) (hw₁ : w ≠ i₁) (hvw : v ≠ w)
    (hu : colCount (t i₀) 0 = colCount (t i₀) (a - 1)) :
    ((κ w).shift.1, (κ v).boxY a) ∉ t v ∧ ((κ w).shift.1, (κ v).boxY a + a - 1) ∉ t v := by
  obtain ⟨r, r', e, X, -⟩ := high_end_rows H hda hv₀ hv₁
  have hr : r' = r := by rcases e with ⟨-, h, h'⟩ | ⟨-, h, h'⟩ <;> omega
  subst hr
  rcases le_total ((κ v).boxY a) ((κ w).boxY a) with hy | hy
  · have h := (lemma48a H hda hv₀ hv₁ hw₀ hw₁ hvw hy).1
    rcases X with ⟨-, -, hb, ht⟩ | ⟨-, -, hb, ht⟩ <;> rw [hb] <;> rw [ht] at h ⊢ <;> exact ⟨h, h⟩
  · have h := (lemma48a H hda hw₀ hw₁ hv₀ hv₁ hvw.symm hy).2
    rcases X with ⟨-, -, hb, ht⟩ | ⟨-, -, hb, ht⟩ <;> rw [ht] <;> rw [hb] at h ⊢ <;> exact ⟨h, h⟩

/-- Proposition 53, the last step for `G = H`: if `W` is the half turn of `B`, then the third
tile is its own half turn and row `d - 1` of `T` is full. Source: `report-4.md`,
Proposition 53 (line 459): "Then H(B) = W, H(U) = U, T is preserved by the half turn of
its box, and t = a. But the spine column of B has a cell in row d - 1 (s <= d - 1 < s + a),
so it is not in Top." -/
private theorem proposition53_half_turn (H : TypeH2 a b d t i₀ i₁ κ) {s : ℤ}
    (hs : FullRows (t i₀) a s) (hG : (κ i₁).negX = true) {B W : Fin 5}
    (hB : B ∈ bottomTiles a s κ i₀ i₁) (hW : W ∈ upperTiles a b s κ i₀ i₁) (hBW : B ≠ W)
    (hX : (κ B).negX ≠ (κ W).negX) (hY : (κ B).negY ≠ (κ W).negY)
    (hc : (κ B).shift.1 + (κ W).shift.1 = a - 1) : False := by
  have F := H.frame
  have ha := F.two_le.1
  have hd := F.two_le_d
  have hno := lemma45_bottom_spine H hs hB
  simp only [bottomTiles, upperTiles, Finset.mem_filter, Finset.mem_univ, true_and] at hB hW
  obtain ⟨hB₀, hB₁, yB⟩ := hB
  obtain ⟨hW₀, hW₁, yW⟩ := hW
  obtain ⟨U, hU₀, hU₁, hUB, hUW⟩ := high_third i₀ i₁ B W
  have hvB := H.vert B hB₀ hB₁
  have hvW := H.vert W hW₀ hW₁
  have hvU := H.vert U hU₀ hU₁
  have hX' : (κ W).negX = !(κ B).negX := by
    revert hX
    cases (κ B).negX <;> cases (κ W).negX <;> simp
  have hY' : (κ W).negY = !(κ B).negY := by
    revert hY
    cases (κ B).negY <;> cases (κ W).negY <;> simp
  have hturn : ∀ x y : ℤ, (x, y) ∈ t B ↔ (a - 1 - x, b - 1 - y) ∈ t W := by
    intro x y
    rw [high_mem F hvB, high_mem F hvW, yB, yW, hX', hY']
    refine iff_of_eq (congrArg (· ∈ t i₀) (Prod.ext ?_ ?_)) <;>
      cases (κ B).negX <;> cases (κ B).negY <;>
      simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false] <;> omega
  have bx : ∀ x : ℤ, a - 1 - (a - 1 - x) = x := fun x => by ring
  have byy : ∀ y : ℤ, b - 1 - (b - 1 - y) = y := fun y => by ring
  -- the half turn of `U` is `U`
  have hsym : ∀ x y : ℤ, (x, y) ∈ t U → (a - 1 - x, b - 1 - y) ∈ t U := by
    intro x y hxy
    have hbd := high_bounds F hxy
    obtain ⟨j, hj⟩ := high_tile_at H (x := a - 1 - x) (y := b - 1 - y) (by omega) (by omega)
      (by omega) (by omega)
    rcases high_all H.ne hB₀ hB₁ hW₀ hW₁ hU₀ hU₁ hBW hUB.symm hUW.symm j with
      h | h | h | h | h <;> rw [h] at hj
    · refine absurd (high_unique H hxy ?_) hU₁
      rwa [H.top_mem, hG, ite_eq_left rfl]
    · rw [H.top_mem, hG, ite_eq_left rfl, bx, byy] at hj
      exact absurd (high_unique H hxy hj) hU₀
    · rw [hturn, bx, byy] at hj
      exact absurd (high_unique H hxy hj) hUW
    · rw [← hturn] at hj
      exact absurd (high_unique H hxy hj) hUB
    · exact hj
  -- the box of `U` is symmetric
  have s1 := (high_box F hvU (hsym _ _ (high_spine H hU₀ hU₁ (y := (κ U).boxY a) le_rfl
    (by omega)))).2
  have s2 := (high_box F hvU (hsym _ _ (high_spine H hU₀ hU₁ (y := (κ U).boxY a + a - 1)
    (by omega) (by omega)))).2
  obtain ⟨-, hxs, -, -, -⟩ := F.vertical_spine hvU
  have hcell : ∀ x : ℤ, (κ U).boxX d ≤ x → x < (κ U).boxX d + d → ∃ y : ℤ, (x, y) ∈ t U := by
    intro x h1 h2
    have hmem : x ∈ xSpan (t U) := by
      rw [hxs, Finset.mem_Ico]
      exact ⟨h1, h2⟩
    obtain ⟨p, hp, q, hq, h3, h4⟩ := mem_xSpan.1 hmem
    exact (F.isTiling.tile_isPolyomino F.poly U).2.exists_in_col hp hq h3 h4
  obtain ⟨y1, hy1⟩ := hcell ((κ U).boxX d) le_rfl (by omega)
  obtain ⟨y2, hy2⟩ := hcell ((κ U).boxX d + d - 1) (by omega) (by omega)
  have s3 := (high_box F hvU (hsym _ _ hy1)).1
  have s4 := (high_box F hvU (hsym _ _ hy2)).1
  -- its far column is full, so row `d - 1` of `T` is full
  have hfar : ∀ y : ℤ, (κ U).boxY a ≤ y → y < (κ U).boxY a + a →
      (a - 1 - (κ U).shift.1, y) ∈ t U := by
    intro y h1 h2
    have h := hsym _ _ (high_spine H hU₀ hU₁ (y := b - 1 - y) (by omega) (by omega))
    rwa [byy] at h
  have hcB := high_bounds F (high_spine H hB₀ hB₁ (y := (κ B).boxY a) le_rfl (by omega))
  apply hno
  have hdep : (if (κ U).negX then (κ U).shift.1 - (a - 1 - (κ U).shift.1)
      else a - 1 - (κ U).shift.1 - (κ U).shift.1) = d - 1 := by
    rcases high_side (κ U) d with ⟨n, h⟩ | ⟨n, h⟩ <;> rw [n] <;>
      simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega
  cases hn : (κ U).negY
  · have h := (high_mem F hvU _ _).1 (hfar ((κ U).boxY a + (κ B).shift.1) (by omega) (by omega))
    rwa [hdep, hn, ite_eq_right Bool.false_ne_true, add_sub_cancel_left] at h
  · have h := (high_mem F hvU _ _).1
      (hfar ((κ U).boxY a + a - 1 - (κ B).shift.1) (by omega) (by omega))
    rwa [hdep, hn, ite_eq_left rfl, sub_sub_cancel] at h

/-- Proposition 53, `G = H` and the wall states (beta, beta): the wall tiles do not carry the
columns of `T` in the same order unless their boxes have the same rows. Source:
`report-4.md`, Proposition 53 (line 459): "Each meets its wall in the rows [u, b - u), the
image of Top (Lemma 45). If B and W carried the columns of T in the same order, these two
sets of rows would differ by the shift". -/
private theorem lemma53_wall_order (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a)
    (hG : (κ i₁).negX = true) (hu : colCount (t i₀) 0 = colCount (t i₀) (a - 1)) {v w : Fin 5}
    (hv₀ : v ≠ i₀) (hv₁ : v ≠ i₁) (hw₀ : w ≠ i₀) (hw₁ : w ≠ i₁)
    (nv : (κ v).negX = true) (cv : (κ v).shift.1 = d - 1)
    (nw : (κ w).negX = false) (cw : (κ w).shift.1 = a - d)
    (ht : rowCount (t i₀) (d - 1) = b - colCount (t i₀) 0 - colCount (t i₀) 0)
    (hy : (κ v).boxY a ≠ (κ w).boxY a) : (κ v).negY ≠ (κ w).negY := by
  intro hn
  have F := H.frame
  have ha := F.two_le.1
  have hvv := H.vert v hv₀ hv₁
  have hvw := H.vert w hw₀ hw₁
  have htb := (lemma45_t_bounds H hda).1
  obtain ⟨hT0, hT1⟩ := lemma43a H hda
  rw [← hu] at hT1
  generalize colCount (t i₀) 0 = u at *
  -- the rows in which the two tiles meet their walls
  have hv : ∀ y : ℤ, (0, y) ∈ t v ↔ u ≤ y ∧ y < b - u := by
    have h1 : ∀ y : ℤ, (0, y) ∈ t v → u ≤ y ∧ y < b - u := by
      intro y hc
      have hbd := high_bounds F hc
      have n0 : ((0, y) : Cell) ∉ t i₀ := fun h => hv₀ (high_unique H hc h)
      have n1 : ((0, y) : Cell) ∉ t i₁ := fun h => hv₁ (high_unique H hc h)
      rw [hT0] at n0
      rw [H.top_mem, hG, ite_eq_left rfl, sub_zero, hT1] at n1
      omega
    have hc := F.vertical_colCount hvv (d - 1)
    rw [nv, ite_eq_left rfl, cv, neg_add_cancel] at hc
    exact fun y => ⟨h1 y, fun h => lemma53_fill h1 (by omega) h.1 h.2⟩
  have hw : ∀ y : ℤ, (a - 1, y) ∈ t w ↔ u ≤ y ∧ y < b - u := by
    have h1 : ∀ y : ℤ, (a - 1, y) ∈ t w → u ≤ y ∧ y < b - u := by
      intro y hc
      have hbd := high_bounds F hc
      have n0 : ((a - 1, y) : Cell) ∉ t i₀ := fun h => hw₀ (high_unique H hc h)
      have n1 : ((a - 1, y) : Cell) ∉ t i₁ := fun h => hw₁ (high_unique H hc h)
      rw [hT1] at n0
      rw [H.top_mem, hG, ite_eq_left rfl, sub_self, hT0] at n1
      omega
    have hc := F.vertical_colCount hvw (d - 1)
    rw [nw, ite_eq_right Bool.false_ne_true, cw, show d - 1 + (a - d) = a - 1 by ring] at hc
    exact fun y => ⟨h1 y, fun h => lemma53_fill h1 (by omega) h.1 h.2⟩
  -- the two sets of rows differ by the shift of the boxes
  have hshift : ∀ y : ℤ, (0, y) ∈ t v ↔ (a - 1, y + (κ w).boxY a - (κ v).boxY a) ∈ t w := by
    intro y
    rw [high_mem F hvv, high_mem F hvw, ← hn, nv, nw, cv, cw]
    refine iff_of_eq (congrArg (· ∈ t i₀) (Prod.ext ?_ ?_))
    · cases (κ v).negY <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega
    · simp only [Bool.false_eq_true, ite_true, ite_false]
      omega
  have k1 := hshift u
  have k2 := hshift (u + (κ v).boxY a - (κ w).boxY a)
  rw [hv, hw] at k1 k2
  omega

/-- Proposition 53 for `u_0 = u_1` and `G = F`. Source: `report-4.md`, Proposition 53
(line 458): "G = F: by Lemma 52(a) J_B = J_W." -/
private theorem proposition53_eq_F (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {s : ℤ}
    (hG : (κ i₁).negX = false) {B W : Fin 5} (hB₀ : B ≠ i₀) (hB₁ : B ≠ i₁) (hW₀ : W ≠ i₀)
    (hW₁ : W ≠ i₁) (hBW : B ≠ W) (yB : (κ B).boxY a = s) (yW : (κ W).boxY a = b - a - s)
    (hrow : ∀ x : ℤ, 0 ≤ x → x < a → ((x, s) ∈ t B ↔
      ((if (κ i₁).negX then a - 1 - x else x), b - 1 - s) ∈ t W))
    (hu : colCount (t i₀) 0 = colCount (t i₀) (a - 1)) : False := by
  have F := H.frame
  have ha := F.two_le.1
  have hc := high_spine H hB₀ hB₁ (y := s) (by omega) (by omega)
  have hbd := high_bounds F hc
  have h := (hrow _ hbd.1.1 hbd.1.2).1 hc
  rw [hG, ite_eq_right Bool.false_ne_true] at h
  have hno := (lemma53_no_spine H hda hW₀ hW₁ hB₀ hB₁ hBW.symm hu).2
  rw [yW, show b - a - s + a - 1 = b - 1 - s by ring] at hno
  exact hno h

/-- Proposition 53 for `u_0 = u_1` and `G = H`. Source: `report-4.md`, Proposition 53
(line 459). -/
private theorem proposition53_eq_H (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {s : ℤ}
    (hs : FullRows (t i₀) a s) (hG : (κ i₁).negX = true) {B W : Fin 5}
    (hB : B ∈ bottomTiles a s κ i₀ i₁) (hW : W ∈ upperTiles a b s κ i₀ i₁) (hBW : B ≠ W)
    (hrow : ∀ x : ℤ, 0 ≤ x → x < a → ((x, s) ∈ t B ↔
      ((if (κ i₁).negX then a - 1 - x else x), b - 1 - s) ∈ t W))
    (hu : colCount (t i₀) 0 = colCount (t i₀) (a - 1)) : False := by
  have F := H.frame
  have ha := F.two_le.1
  have hd := F.two_le_d
  have hab := (corollary42 H hs).1.2.2.2
  have h43 := lemma43c H hda hs
  have hpos := high_ends_pos H hda
  have hmB := hB
  have hmW := hW
  simp only [bottomTiles, upperTiles, Finset.mem_filter, Finset.mem_univ, true_and] at hB hW
  obtain ⟨hB₀, hB₁, yB⟩ := hB
  obtain ⟨hW₀, hW₁, yW⟩ := hW
  rcases lemma45b H hda hs hG with ⟨-, h⟩ | ⟨v, w, hv₀, hv₁, hw₀, hw₁, c1, c2, g1, g2, h⟩ |
    ⟨v, w, hv₀, hv₁, hw₀, hw₁, hx, cv, hx', cw, h⟩
  · -- (o, o)
    have h48 := lemma48c H hda
    rw [← hu, min_self] at h48
    omega
  · -- (alpha, alpha): the wall tiles are neither bottom nor top tiles
    have n1 : v ≠ w := by
      rintro rfl
      omega
    have n2 : v ≠ B := by
      rintro rfl
      omega
    have n3 : w ≠ B := by
      rintro rfl
      omega
    rcases high_all H.ne hv₀ hv₁ hw₀ hw₁ hB₀ hB₁ n1 n2 n3 W with e | e | e | e | e
    · exact hW₀ e
    · exact hW₁ e
    · rw [e] at yW
      omega
    · rw [e] at yW
      omega
    · exact hBW e.symm
  · -- (beta, beta)
    have nv : (κ v).negX = true := by
      rcases high_side (κ v) d with ⟨-, e⟩ | ⟨e, -⟩
      · omega
      · exact e
    have nw : (κ w).negX = false := by
      rcases high_side (κ w) d with ⟨e, -⟩ | ⟨-, e⟩
      · exact e
      · omega
    have hvw : v ≠ w := by
      rintro rfl
      omega
    rw [← hu] at h
    have hYne := lemma53_wall_order H hda hG hu hv₀ hv₁ hw₀ hw₁ nv cv nw cw (by omega)
    -- the rows of the images of the spine cells
    have hrow' : ∀ x : ℤ, 0 ≤ x → x < a →
        ((x, (κ B).boxY a) ∈ t B ↔ (a - 1 - x, (κ W).boxY a + a - 1) ∈ t W) := by
      intro x h0 h1
      have h2 := hrow x h0 h1
      rw [hG, ite_eq_left rfl] at h2
      rwa [yB, yW, show b - a - s + a - 1 = b - 1 - s by ring]
    have hspB : ((κ B).shift.1, (κ B).boxY a) ∈ t B :=
      high_spine H hB₀ hB₁ le_rfl (by omega)
    have hspW : ((κ W).shift.1, (κ W).boxY a + a - 1) ∈ t W :=
      high_spine H hW₀ hW₁ (by omega) (by omega)
    have keyB : B = v → W = w := by
      rintro rfl
      by_contra hne
      refine (lemma53_no_spine H hda hW₀ hW₁ hw₀ hw₁ hne hu).2 ?_
      have h2 := (hrow' (d - 1) (by omega) (by omega)).1 (cv ▸ hspB)
      rwa [show a - 1 - (d - 1) = a - d by ring, ← cw] at h2
    have keyB' : B = w → W = v := by
      rintro rfl
      by_contra hne
      refine (lemma53_no_spine H hda hW₀ hW₁ hv₀ hv₁ hne hu).2 ?_
      have h2 := (hrow' (a - d) (by omega) (by omega)).1 (cw ▸ hspB)
      rwa [show a - 1 - (a - d) = d - 1 by ring, ← cv] at h2
    have keyW : W = v → B = w := by
      rintro rfl
      by_contra hne
      refine (lemma53_no_spine H hda hB₀ hB₁ hw₀ hw₁ hne hu).1 ?_
      rw [hrow' _ (by omega) (by omega), cw, show a - 1 - (a - d) = d - 1 by ring, ← cv]
      exact hspW
    have keyW' : W = w → B = v := by
      rintro rfl
      by_contra hne
      refine (lemma53_no_spine H hda hB₀ hB₁ hv₀ hv₁ hne hu).1 ?_
      rw [hrow' _ (by omega) (by omega), cv, show a - 1 - (d - 1) = a - d by ring, ← cw]
      exact hspW
    have hcases : B = v ∧ W = w ∨ B = w ∧ W = v := by
      by_cases e1 : B = v
      · exact Or.inl ⟨e1, keyB e1⟩
      by_cases e2 : B = w
      · exact Or.inr ⟨e2, keyB' e2⟩
      rcases high_all H.ne hv₀ hv₁ hw₀ hw₁ hB₀ hB₁ hvw (Ne.symm e1) (Ne.symm e2) W with
        e | e | e | e | e
      · exact absurd e hW₀
      · exact absurd e hW₁
      · exact absurd (keyW e) e2
      · exact absurd (keyW' e) e1
      · exact absurd e.symm hBW
    rcases hcases with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · subst e1
      subst e2
      refine proposition53_half_turn H hs hG hmB hmW hBW ?_ (hYne (by omega)) (by omega)
      rw [nv, nw]
      exact Bool.false_ne_true.symm
    · subst e1
      subst e2
      refine proposition53_half_turn H hs hG hmB hmW hBW ?_ (hYne (by omega)).symm (by omega)
      rw [nv, nw]
      exact Bool.false_ne_true

/-- Proposition 53. Source: `report-4.md`, section 5h, Proposition 53 (line 453):
"P = Q = 1 does not occur." Proof (lines 455-459): for `u_0 != u_1` compare row
counts with the image tiling under `G` and get a vertical tile symmetric under
`r -> b - 1 - r`; for `u_0 = u_1` the cases `G = F` and `G = H` with the wall
states of Lemma 45 (b). -/
theorem proposition53 (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {s : ℤ}
    (hs : FullRows (t i₀) a s) (hP : (bottomTiles a s κ i₀ i₁).card = 1)
    (hQ : (upperTiles a b s κ i₀ i₁).card = 1) : False := by
  have h43 := lemma43c H hda hs
  obtain ⟨B, hB⟩ := Finset.card_eq_one.1 hP
  obtain ⟨W, hW⟩ := Finset.card_eq_one.1 hQ
  have mB : B ∈ bottomTiles a s κ i₀ i₁ := by simp [hB]
  have mW : W ∈ upperTiles a b s κ i₀ i₁ := by simp [hW]
  have hrow := fun (x : ℤ) (h0 : 0 ≤ x) (h1 : x < a) => lemma52_row_image H hda hs h0 h1
  have hsum := (lemma52a H hda hs).2.2
  rw [hB, hW, Finset.sum_singleton, Finset.sum_singleton] at hsum
  simp only [hB, hW, Finset.mem_singleton, exists_eq_left] at hrow
  have kB := mB
  have kW := mW
  simp only [bottomTiles, upperTiles, Finset.mem_filter, Finset.mem_univ, true_and] at kB kW
  obtain ⟨hB₀, hB₁, yB⟩ := kB
  obtain ⟨hW₀, hW₁, yW⟩ := kW
  have hBW : B ≠ W := by
    rintro rfl
    omega
  by_cases hu : colCount (t i₀) 0 = colCount (t i₀) (a - 1)
  · cases hG : (κ i₁).negX
    · exact proposition53_eq_F H hda hG hB₀ hB₁ hW₀ hW₁ hBW yB yW hrow hu
    · exact proposition53_eq_H H hda hs hG mB mW hBW hrow hu
  · exact proposition53_ne H hda hB₀ hB₁ hW₀ hW₁ hBW yB yW hsum hu

/-- Proposition 54, the tiles at the walls. Source: `report-4.md`, Proposition 54 (line 468):
"(o, o) needs b <= 2d, but b > a >= 2d; so by Lemma 45(b) exactly one box lies at each
wall". -/
private theorem proposition54_walls (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {s : ℤ}
    (hs : FullRows (t i₀) a s) (hG : (κ i₁).negX = true) (h2d : 2 * d ≤ a) :
    ∃ v w, v ≠ i₀ ∧ v ≠ i₁ ∧ w ≠ i₀ ∧ w ≠ i₁ ∧ (κ v).boxX d = 0 ∧ (κ w).boxX d = a - d := by
  have F := H.frame
  have hd := F.two_le_d
  have hab := (corollary42 H hs).1.2.2.2
  have hpos := high_ends_pos H hda
  rcases lemma45b H hda hs hG with ⟨-, h⟩ | ⟨v, w, hv₀, hv₁, hw₀, hw₁, c1, c2, -⟩ |
    ⟨v, w, hv₀, hv₁, hw₀, hw₁, hx, -, hx', -⟩
  · omega
  · have bv := (F.vertical_spine (H.vert v hv₀ hv₁)).2.2.2.1
    have bw := (F.vertical_spine (H.vert w hw₀ hw₁)).2.2.2.1
    refine ⟨v, w, hv₀, hv₁, hw₀, hw₁, ?_, ?_⟩
    · rcases high_side (κ v) d with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
    · rcases high_side (κ w) d with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  · exact ⟨v, w, hv₀, hv₁, hw₀, hw₁, hx, hx'⟩

/-- Proposition 54 for two bottom tiles `B₁`, `B₂` (spine of `B₁` on the left) and one top
tile `W`. Source: `report-4.md`, Proposition 54 (lines 465-468). -/
private theorem proposition54_core (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {s : ℤ}
    (hs : FullRows (t i₀) a s) {B₁ B₂ W : Fin 5} (h10 : B₁ ≠ i₀) (h11 : B₁ ≠ i₁)
    (h20 : B₂ ≠ i₀) (h21 : B₂ ≠ i₁) (hW0 : W ≠ i₀) (hW1 : W ≠ i₁)
    (y1 : (κ B₁).boxY a = s) (y2 : (κ B₂).boxY a = s) (yW : (κ W).boxY a = b - a - s)
    (hc : (κ B₁).shift.1 < (κ B₂).shift.1)
    (hrow : ∀ x : ℤ, 0 ≤ x → x < a → ((x, s) ∈ t B₁ ∨ (x, s) ∈ t B₂ ↔
      ((if (κ i₁).negX then a - 1 - x else x), b - 1 - s) ∈ t W))
    (hsum : rowCount (t B₁) s + rowCount (t B₂) s = rowCount (t W) (b - 1 - s)) : False := by
  have F := H.frame
  have ha := F.two_le.1
  have hsd := high_s_lt F hs
  have h43 := lemma43c H hda hs
  have hpos := high_ends_pos H hda
  have hne : B₁ ≠ B₂ := by
    rintro rfl
    omega
  have hne1 : B₁ ≠ W := by
    rintro rfl
    omega
  have hne2 : B₂ ≠ W := by
    rintro rfl
    omega
  obtain ⟨r1, r1', e1, X1, n1, -⟩ := high_end_rows H hda h10 h11
  obtain ⟨r2, r2', e2, X2, n2, -⟩ := high_end_rows H hda h20 h21
  obtain ⟨r3, r3', e3, X3, -, n3⟩ := high_end_rows H hda hW0 hW1
  have k1 := (lemma48a H hda h10 h11 hW0 hW1 hne1 (by omega)).2
  have k2 := (lemma48a H hda h20 h21 hW0 hW1 hne2 (by omega)).2
  have f1 := lemma52c H hda h10 h11 h20 h21 hne (y1.trans y2.symm)
  have f2 := lemma52c H hda h20 h21 h10 h11 hne.symm (y2.trans y1.symm)
  have b1 := (F.vertical_spine (H.vert B₁ h10 h11)).2.2.2.1
  have b2 := (F.vertical_spine (H.vert B₂ h20 h21)).2.2.2.1
  have bW := (F.vertical_spine (H.vert W hW0 hW1)).2.2.2.1
  rw [y1] at X1 n1
  rw [y2] at X2 n2
  rw [yW, show b - a - s + a - 1 = b - 1 - s by ring] at X3 n3
  rw [yW] at k1 k2
  rw [n1, n2, n3] at hsum
  -- the lengths of the end rows
  have hm : r2 = r1 ∧ r3' = 2 * r1 ∧ r3 = r1 ∧ 1 ≤ r1 ∧ 2 * r1 ≤ d := by
    rcases e1 with ⟨-, g1, g1'⟩ | ⟨-, g1, g1'⟩ <;> rcases e2 with ⟨-, g2, g2'⟩ | ⟨-, g2, g2'⟩ <;>
      rcases e3 with ⟨-, g3, g3'⟩ | ⟨-, g3, g3'⟩ <;> omega
  obtain ⟨rfl, rfl, rfl, hm1, hm2⟩ := hm
  -- the bottom boxes
  obtain ⟨hB1, hB2, hJ1, hJ2⟩ : (κ B₁).boxX d = (κ B₁).shift.1 - (d - 1) ∧
      (κ B₂).boxX d = (κ B₂).shift.1 ∧
      (∀ x : ℤ, (x, s) ∈ t B₁ ↔ (κ B₁).shift.1 - r3 < x ∧ x ≤ (κ B₁).shift.1) ∧
      (∀ x : ℤ, (x, s) ∈ t B₂ ↔ (κ B₂).shift.1 ≤ x ∧ x < (κ B₂).shift.1 + r3) := by
    have c1 : 0 ≤ (κ B₁).shift.1 ∧ (κ B₁).shift.1 < a := by
      rcases high_side (κ B₁) d with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
    have c2 : 0 ≤ (κ B₂).shift.1 ∧ (κ B₂).shift.1 < a := by
      rcases high_side (κ B₂) d with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
    have g1 := (hrow _ c1.1 c1.2).1 (Or.inl (high_spine H h10 h11 (by omega) (by omega)))
    have g2 := (hrow _ c2.1 c2.2).1 (Or.inr (high_spine H h20 h21 (by omega) (by omega)))
    have hdiff : (κ B₂).shift.1 - (κ B₁).shift.1 < 2 * r3 := by
      rcases X3 with ⟨-, -, -, hq⟩ | ⟨-, -, -, hq⟩ <;> rw [hq] at g1 g2 <;>
        cases hG : (κ i₁).negX <;>
        simp only [hG, Bool.false_eq_true, ite_true, ite_false] at g1 g2 <;> omega
    rcases X1 with ⟨-, hx1, hj1, -⟩ | ⟨-, hx1, hj1, -⟩
    · exact absurd ⟨by omega, by omega⟩ f1
    rcases X2 with ⟨-, hx2, hj2, -⟩ | ⟨-, hx2, hj2, -⟩
    · exact ⟨hx1, hx2, hj1, hj2⟩
    · exact absurd ⟨by omega, by omega⟩ f2
  -- the top row of `W`
  have g1 := (hrow ((κ B₁).shift.1 - r3 + 1) (by omega) (by omega)).1
    (Or.inl ((hJ1 _).2 (by omega)))
  have g2 := (hrow ((κ B₂).shift.1 + r3 - 1) (by omega) (by omega)).1
    (Or.inr ((hJ2 _).2 (by omega)))
  cases hG : (κ i₁).negX
  · rw [hG, ite_eq_right Bool.false_ne_true] at g1 g2
    rcases X3 with ⟨-, -, hb, hq⟩ | ⟨-, -, hb, hq⟩ <;> rw [hq] at g1 g2 <;> rw [hb] at k1 k2 <;>
      omega
  · rw [hG, ite_eq_left rfl] at g1 g2
    have h2d : 2 * d ≤ a := by
      rcases X3 with ⟨-, -, -, hq⟩ | ⟨-, -, -, hq⟩ <;> rw [hq] at g1 g2 <;> omega
    obtain ⟨v, w, hv₀, hv₁, hw₀, hw₁, hx, hx'⟩ := proposition54_walls H hda hs hG h2d
    have hv := high_all H.ne h10 h11 h20 h21 hW0 hW1 hne hne1 hne2 v
    have hw := high_all H.ne h10 h11 h20 h21 hW0 hW1 hne hne1 hne2 w
    rcases X3 with ⟨-, hxW, hb, hq⟩ | ⟨-, hxW, hb, hq⟩ <;> rw [hq] at g1 g2 <;>
      rw [hb] at k1 k2 <;> rcases hv with h | h | h | h | h <;>
      first
      | exact hv₀ h
      | exact hv₁ h
      | (subst h
         rcases hw with h | h | h | h | h <;>
          first
          | exact hw₀ h
          | exact hw₁ h
          | (subst h; omega))

/-- Proposition 54, the case `P = 2` and `Q = 1`. -/
private theorem proposition54_two_one (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {s : ℤ}
    (hs : FullRows (t i₀) a s) (hP : (bottomTiles a s κ i₀ i₁).card = 2)
    (hQ : (upperTiles a b s κ i₀ i₁).card = 1) : False := by
  obtain ⟨B₁, B₂, hne, hB⟩ := Finset.card_eq_two.1 hP
  obtain ⟨W, hW⟩ := Finset.card_eq_one.1 hQ
  have m1 : B₁ ∈ bottomTiles a s κ i₀ i₁ := by simp [hB]
  have m2 : B₂ ∈ bottomTiles a s κ i₀ i₁ := by simp [hB]
  have mW : W ∈ upperTiles a b s κ i₀ i₁ := by simp [hW]
  have hrow := fun (x : ℤ) (h0 : 0 ≤ x) (h1 : x < a) => lemma52_row_image H hda hs h0 h1
  have hsum := (lemma52a H hda hs).2.2
  rw [hB, hW, Finset.sum_pair hne, Finset.sum_singleton] at hsum
  simp only [hB, hW, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
    exists_eq_left] at hrow
  simp only [bottomTiles, upperTiles, Finset.mem_filter, Finset.mem_univ, true_and] at m1 m2 mW
  rcases lt_trichotomy (κ B₁).shift.1 (κ B₂).shift.1 with h | h | h
  · exact proposition54_core H hda hs m1.1 m1.2.1 m2.1 m2.2.1 mW.1 mW.2.1 m1.2.2 m2.2.2 mW.2.2 h
      hrow hsum
  · exact hne (lemma45_spine_inj H hda m1.1 m1.2.1 m2.1 m2.2.1 h)
  · exact proposition54_core H hda hs m2.1 m2.2.1 m1.1 m1.2.1 mW.1 mW.2.1 m2.2.2 m1.2.2 mW.2.2 h
      (fun x h0 h1 => or_comm.trans (hrow x h0 h1)) (by omega)

/-- Two grid isometries with the same switches and the same shift are equal. -/
private theorem lemma54_iso_eq {g g' : GridIso} (h1 : g.swap = g'.swap) (h2 : g.negX = g'.negX)
    (h3 : g.negY = g'.negY) (h4 : g.shift.1 = g'.shift.1) (h5 : g.shift.2 = g'.shift.2) :
    g = g' := by
  obtain ⟨s, n, m, u, v⟩ := g
  obtain ⟨s', n', m', u', v'⟩ := g'
  dsimp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  rfl

/-- Membership in the image under the half turn. -/
private theorem lemma54_mem_halfTurn {S : Finset Cell} {x y : ℤ} :
    (x, y) ∈ S.image (GridIso.halfTurn a b).apply ↔ (a - 1 - x, b - 1 - y) ∈ S := by
  constructor
  · intro h
    obtain ⟨⟨u, v⟩, hc, he⟩ := Finset.mem_image.1 h
    rw [GridIso.halfTurn_apply] at he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rwa [show a - 1 - (a - 1 - u) = u by ring, show b - 1 - (b - 1 - v) = v by ring]
  · intro h
    refine Finset.mem_image.2 ⟨_, h, ?_⟩
    rw [GridIso.halfTurn_apply]
    simp

/-- For `T' = H(T)` the half turn maps the tiling to a tiling of type H2 with the same `T`
and `T'`; the case `G = F` is `square_reflect`. Source: `report-4.md`, Lemma 52 (a)
(line 445): "The image of the tiling under G is a tiling with the same T and T'". -/
private theorem lemma54_half_turn (H : TypeH2 a b d t i₀ i₁ κ) (hG : (κ i₁).negX = true) :
    (t i₁).image (GridIso.halfTurn a b).apply = t i₀ ∧
      TypeH2 a b d (fun i => (t (Equiv.swap i₀ i₁ i)).image (GridIso.halfTurn a b).apply) i₀ i₁
        (fun i => (GridIso.halfTurn a b).comp (κ (Equiv.swap i₀ i₁ i))) := by
  have F := H.frame
  have hT : (t i₁).image (GridIso.halfTurn a b).apply = t i₀ := by
    ext ⟨x, y⟩
    rw [lemma54_mem_halfTurn, H.top_mem, hG, ite_eq_left rfl,
      show b - 1 - (b - 1 - y) = y by ring, show a - 1 - (a - 1 - x) = x by ring]
  have hκ : κ i₁ = GridIso.halfTurn a b := by
    refine lemma54_iso_eq H.horiz hG H.down ?_ H.top
    rcases H.mirror_form with h | h
    · rw [hG] at h
      exact absurd h.1.symm Bool.false_ne_true
    · exact h.2
  have hinv : (GridIso.halfTurn a b).comp (GridIso.halfTurn a b) = GridIso.one := by
    simp [GridIso.comp, GridIso.one, GridIso.halfTurn, GridIso.apply]
  have ht := F.isTiling.halfTurn.reindex (Equiv.swap i₀ i₁)
  refine ⟨hT, ⟨ht.disjoint, ht.cover, ?_, ?_, ?_, ?_, ?_, ?_⟩, H.ne, ?_, ?_, ?_, ?_⟩
  · simpa only [Equiv.swap_apply_left, hT] using F.poly
  · simpa only [Equiv.swap_apply_left, hT] using F.nonrect
  · simpa only [Equiv.swap_apply_left, hT] using F.row0
  · simpa only [Equiv.swap_apply_left, hT] using F.rows
  · intro i
    rw [Equiv.swap_apply_left, hT, GridIso.image_comp, ← F.image]
  · rw [Equiv.swap_apply_left, hκ, hinv]
  · simp [F.base, GridIso.comp, GridIso.one, GridIso.halfTurn]
  · simp [F.base, GridIso.comp, GridIso.one, GridIso.halfTurn]
  · simp [F.base, GridIso.comp, GridIso.one, GridIso.halfTurn, GridIso.apply]
  · intro i h0 h1
    simp [Equiv.swap_apply_of_ne_of_ne h0 h1, GridIso.comp, GridIso.halfTurn, H.vert i h0 h1]

/-- The image tiling under `G`: a tiling of type H2 with the same `T`, in which the images
of the top tiles are the bottom tiles. Source: `report-4.md`, Lemma 52 (a) (line 445). -/
private theorem lemma54_image (H : TypeH2 a b d t i₀ i₁ κ) (s : ℤ) :
    ∃ (t' : Fin 5 → Finset Cell) (κ' : Fin 5 → GridIso), TypeH2 a b d t' i₀ i₁ κ' ∧
      t' i₀ = t i₀ ∧ bottomTiles a s κ' i₀ i₁ = upperTiles a b s κ i₀ i₁ ∧
      upperTiles a b s κ' i₀ i₁ = bottomTiles a s κ i₀ i₁ := by
  have sets : ∀ κ' : Fin 5 → GridIso,
      (∀ i, i ≠ i₀ → i ≠ i₁ → (κ' i).boxY a = b - a - (κ i).boxY a) →
      bottomTiles a s κ' i₀ i₁ = upperTiles a b s κ i₀ i₁ ∧
        upperTiles a b s κ' i₀ i₁ = bottomTiles a s κ i₀ i₁ := by
    intro κ' h
    constructor <;> ext i <;>
      simp only [bottomTiles, upperTiles, Finset.mem_filter, Finset.mem_univ, true_and] <;>
      constructor <;> rintro ⟨h0, h1, h2⟩ <;> refine ⟨h0, h1, ?_⟩ <;>
      have := h i h0 h1 <;> omega
  cases hG : (κ i₁).negX
  · obtain ⟨hT, H'⟩ := square_reflect H hG
    refine ⟨_, _, H', by simp only [Equiv.swap_apply_left, hT], sets _ fun i h0 h1 => ?_⟩
    rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
    generalize κ i = g
    obtain ⟨s, n, m, u, v⟩ := g
    cases m <;> simp [GridIso.comp, GridIso.boxY, GridIso.flipY, GridIso.apply] <;> omega
  · obtain ⟨hT, H'⟩ := lemma54_half_turn H hG
    refine ⟨_, _, H', by simp only [Equiv.swap_apply_left, hT], sets _ fun i h0 h1 => ?_⟩
    rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
    generalize κ i = g
    obtain ⟨s, n, m, u, v⟩ := g
    cases m <;> simp [GridIso.comp, GridIso.boxY, GridIso.halfTurn, GridIso.apply] <;> omega

/-- Proposition 54. Source: `report-4.md`, section 5h, Proposition 54 (line 463):
"P = Q." Proof (lines 465-468): after replacing the tiling by its image under `G`,
`P = 2` and `Q = 1`; the bottom boxes; `G = F` against Lemma 48 (a); `G = H` by the
wall states. -/
theorem proposition54 (H : TypeH2 a b d t i₀ i₁ κ) (hda : d < a) {s : ℤ}
    (hs : FullRows (t i₀) a s) :
    (bottomTiles a s κ i₀ i₁).card = (upperTiles a b s κ i₀ i₁).card := by
  have hc := counts_bottom_top H hda hs
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨t', κ', H', hT, h1, h2⟩ := lemma54_image H s
    rw [← hT] at hs
    exact proposition54_two_one H' hda hs (by rw [h1]; omega) (by rw [h2]; omega)
  · exact proposition54_two_one H hda hs (by omega) (by omega)

/-- Theorem 55. Source: `report-4.md`, section 5h, Theorem 55 (line 472): "Case
(II.3) of Theorem 6 does not occur for k = 5." Proof (line 474): `d = a` is
Theorem 41; for `d < a`, `(P, Q)` is `(1, 1)`, `(2, 1)` or `(1, 2)`, and
Propositions 53 and 54 exclude all three. -/
theorem theorem55 (H : TypeH2 a b d t i₀ i₁ κ) : False := by
  obtain ⟨v, hv₀, hv₁⟩ := exists_vertical5 i₀ i₁
  have hb := H.bounds hv₀ hv₁
  by_cases hd : d = a
  · exact theorem41 H hd
  · have hda : d < a := by omega
    obtain ⟨s, _, _, hs⟩ := H.frame.exists_fullRows
    have hc := counts_bottom_top H hda hs
    have h54 := proposition54 H hda hs
    exact proposition53 H hda hs (by omega) (by omega)

end PolyominoOddOrder
