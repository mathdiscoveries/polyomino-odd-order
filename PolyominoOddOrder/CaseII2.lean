module

public import PolyominoOddOrder.CaseII2Long

/-!
# Case (II.2) does not occur for five tiles (`CaseII2.lean`)

Blueprint unit II2b. Type H1 with five tiles and `b - a <= d`: `report-4.md`,
section 5c (Lemma 36, Propositions 37 and 38), and Corollary 39.

The binding statement of this file is `corollary39`; its proof rests on
`corollary35` (`CaseII2Long.lean`), `TypeH1.corollary29` (`H1Top.lean`),
`proposition37` and `proposition38`. `proposition37` and `proposition38` use
nothing of `CaseII2Long.lean`.

Order of the file: coordinates of a vertical tile; Lemma 36 (b); the walls (Lemma
36 (d)); the tail and Steps 3 and 4 of Proposition 38, for five sets of cells
(`NF38`); Steps 1 and 2 of Proposition 38 (`Setting38`); Proposition 37; the
numbered statements of section 5c.

Notation: `h = b - a`; `u_0 = colCount (t i₀) 0`, `u_1 = colCount (t i₀) (a - 1)`,
`t = rowCount (t i₀) (d - 1)`; `s` the number of full bottom rows of `T`; Top the
set of columns `x` with `(x, d - 1)` in `T`.

Commit `e5ca51d`.
-/

@[expose] public section

namespace PolyominoOddOrder

open TypeH1

namespace CaseII2

/-- The rows below `s` lie in `T`. The only place of this file that reads the
definition of `FullRows`. -/
theorem full_row {T : Finset Cell} {a s : ℤ} (hs : FullRows T a s) {x y : ℤ} (h1 : 0 ≤ x)
    (h2 : x < a) (h3 : 0 ≤ y) (h4 : y < s) : (x, y) ∈ T :=
  hs.2.1 x y h1 h2 h3 h4

/-! ## Counting a column -/

/-- A column that meets `S` in an interval of rows. -/
theorem colCount_of_interval {S : Finset Cell} {x p q : ℤ}
    (h : ∀ y, (x, y) ∈ S ↔ p ≤ y ∧ y < q) (hpq : p ≤ q) : colCount S x = q - p := by
  have h1 : S.filter (fun c => c.1 = x) = (Finset.Ico p q).image fun y => (x, y) := by
    ext ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq]
    constructor
    · rintro ⟨h2, rfl⟩
      exact ⟨v, (h v).1 h2, rfl, rfl⟩
    · rintro ⟨v', h2, rfl, rfl⟩
      exact ⟨(h v').2 h2, rfl⟩
  unfold colCount
  rw [h1, Finset.card_image_of_injective _ (fun y y' h => (Prod.mk.inj h).2), Int.card_Ico,
    Int.toNat_of_nonneg (by omega)]

/-- A column of non-negative rows that is closed downwards is an interval of
`colCount` rows. -/
theorem col_initial {S : Finset Cell} {x : ℤ} (hb : ∀ y, (x, y) ∈ S → 0 ≤ y)
    (hd : ∀ y y', (x, y) ∈ S → 0 ≤ y' → y' ≤ y → (x, y') ∈ S) (y : ℤ) :
    (x, y) ∈ S ↔ 0 ≤ y ∧ y < colCount S x := by
  by_cases hne : ∃ y, (x, y) ∈ S
  · obtain ⟨y₀, hy₀⟩ := hne
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (S.filter fun c => c.1 = x) (fun c => c.2)
      ⟨(x, y₀), Finset.mem_filter.2 ⟨hy₀, rfl⟩⟩
    obtain ⟨hmS, hmx⟩ := Finset.mem_filter.1 hm
    have hm' : (x, m.2) ∈ S := by
      rw [← hmx]
      exact hmS
    have key : ∀ y, (x, y) ∈ S ↔ 0 ≤ y ∧ y < m.2 + 1 := by
      intro y
      constructor
      · intro h
        have := hmax (x, y) (Finset.mem_filter.2 ⟨h, rfl⟩)
        have := hb y h
        simp at *
        omega
      · rintro ⟨h1, h2⟩
        exact hd _ _ hm' h1 (by omega)
    rw [colCount_of_interval key (by have := hb _ hm'; omega), key]
    omega
  · push Not at hne
    have : colCount S x = 0 := by
      rw [colCount_of_interval (p := 0) (q := 0)
        (fun y => ⟨fun h => absurd h (hne y), fun h => by omega⟩) le_rfl]
      rfl
    rw [this]
    exact ⟨fun h => absurd h (hne y), fun h => by omega⟩

section General

variable {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell} {i₀ : Fin k} {κ : Fin k → GridIso}

/-! ## Boxes and membership in coordinates -/

/-- The box of `T`. -/
theorem box_T (F : Frame a b d t i₀ κ) {x y : ℤ} (h : (x, y) ∈ t i₀) :
    (0 ≤ x ∧ x < a) ∧ 0 ≤ y ∧ y < d := by
  have h1 : x ∈ xSpan (t i₀) := mem_xSpan.2 ⟨_, h, _, h, le_rfl, le_rfl⟩
  have h2 : y ∈ ySpan (t i₀) := mem_ySpan.2 ⟨_, h, _, h, le_rfl, le_rfl⟩
  rw [F.cols, Finset.mem_Ico] at h1
  rw [F.rows, Finset.mem_Ico] at h2
  exact ⟨h1, h2⟩

/-- The box of a vertical tile lies in `R a b`, above row 0. -/
theorem bounds_V (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true) :
    (0 ≤ (κ i).boxX d ∧ (κ i).boxX d + d ≤ a) ∧ 1 ≤ (κ i).boxY a ∧ (κ i).boxY a + a ≤ b :=
  (F.vertical_spine hi).2.2.2

/-- A vertical tile lies in its box. -/
theorem box_V (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true) {X Y : ℤ}
    (h : (X, Y) ∈ t i) :
    ((κ i).boxX d ≤ X ∧ X < (κ i).boxX d + d) ∧ (κ i).boxY a ≤ Y ∧ Y < (κ i).boxY a + a := by
  have h1 : X ∈ xSpan (t i) := mem_xSpan.2 ⟨_, h, _, h, le_rfl, le_rfl⟩
  have h2 : Y ∈ ySpan (t i) := mem_ySpan.2 ⟨_, h, _, h, le_rfl, le_rfl⟩
  rw [(F.vertical_spine hi).2.1, Finset.mem_Ico] at h1
  rw [(F.vertical_spine hi).2.2.1, Finset.mem_Ico] at h2
  exact ⟨h1, h2⟩

/-- Membership in a vertical tile: the cell `(X, Y)` comes from the column of `T` at
the place of row `Y` in the box (from the top if the order is reversed) and from
the row of `T` at the distance of column `X` from the spine. -/
theorem mem_V (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true) (X Y : ℤ) :
    (X, Y) ∈ t i ↔
      ((if (κ i).negY then (κ i).boxY a + a - 1 - Y else Y - (κ i).boxY a),
        (if (κ i).negX then (κ i).boxX d + d - 1 - X else X - (κ i).boxX d)) ∈ t i₀ := by
  rw [← F.vertical_mem hi]
  unfold GridIso.boxX GridIso.boxY
  cases (κ i).negX <;> cases (κ i).negY <;> simp <;> ring_nf

/-- The spine column in terms of the box. -/
theorem shift_eq (g : GridIso) (d : ℤ) :
    g.shift.1 = if g.negX then g.boxX d + d - 1 else g.boxX d := by
  unfold GridIso.boxX
  cases g.negX <;> simp; omega

/-- The spine of a vertical tile. -/
theorem spine_V (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true) {Y : ℤ}
    (h1 : (κ i).boxY a ≤ Y) (h2 : Y < (κ i).boxY a + a) : ((κ i).shift.1, Y) ∈ t i :=
  (F.vertical_spine hi).1 Y h1 h2

/-- A cell is in at most one tile. -/
theorem uniq (F : Frame a b d t i₀ κ) {i j : Fin k} {c : Cell} (hi : c ∈ t i) (hj : c ∈ t j) :
    i = j :=
  F.isTiling.tile_unique hi hj

/-- Every cell of `R a b` is in a tile. -/
theorem cover (F : Frame a b d t i₀ κ) {x y : ℤ} (h1 : 0 ≤ x) (h2 : x < a) (h3 : 0 ≤ y)
    (h4 : y < b) : ∃ i, (x, y) ∈ t i :=
  F.isTiling.exists_tile (mem_R.2 ⟨⟨h1, h2⟩, h3, h4⟩)

/-- Every column of the box of a vertical tile holds one of its cells. -/
theorem col_V (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true) {X : ℤ}
    (h1 : (κ i).boxX d ≤ X) (h2 : X < (κ i).boxX d + d) : ∃ Y, (X, Y) ∈ t i := by
  obtain ⟨x, hx⟩ := F.exists_in_row
    (y := if (κ i).negX then (κ i).boxX d + d - 1 - X else X - (κ i).boxX d)
    (by split <;> omega) (by split <;> omega)
  refine ⟨if (κ i).negY then (κ i).boxY a + a - 1 - x else x + (κ i).boxY a, (mem_V F hi _ _).2 ?_⟩
  convert hx using 2
  cases (κ i).negY <;> simp

/-- The thick spine of a vertical tile is an interval of `s` columns of its box. -/
theorem thick_V (F : Frame a b d t i₀ κ) {s : ℤ} (hs : FullRows (t i₀) a s) {i : Fin k}
    (hi : (κ i).swap = true) :
    ∃ p : ℤ, (p = if (κ i).negX then (κ i).boxX d + d - s else (κ i).boxX d) ∧
      ∀ X Y, p ≤ X → X < p + s → (κ i).boxY a ≤ Y → Y < (κ i).boxY a + a → (X, Y) ∈ t i := by
  refine ⟨_, rfl, fun X Y h1 h2 h3 h4 => (mem_V F hi X Y).2 (full_row hs ?_ ?_ ?_ ?_)⟩ <;>
    revert h1 h2 <;> cases (κ i).negX <;> cases (κ i).negY <;> simp <;> omega

end General

section H1

variable {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell} {i₀ : Fin k} {κ : Fin k → GridIso}

/-- A top tile is not `T`. -/
theorem ne_of_top {i : Fin k} (hi : i ∈ topTiles b t i₀) : i ≠ i₀ := by
  simp only [topTiles, Finset.mem_filter] at hi
  exact hi.2.1

/-- A tile other than `T` with a cell in row `b - 1` is a top tile. -/
theorem top_of_cell {i : Fin k} (hi : i ≠ i₀) {x : ℤ} (hx : (x, b - 1) ∈ t i) :
    i ∈ topTiles b t i₀ := by
  simp only [topTiles, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hi, x, hx⟩

/-- A tile other than `T` is a top tile exactly when its box starts in row `b - a`. -/
theorem mem_topTiles (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) {i : Fin k} (hi : i ≠ i₀) :
    i ∈ topTiles b t i₀ ↔ (κ i).boxY a = b - a := by
  have hb := bounds_V H.frame (H.vert i hi)
  have hB := H.bounds hk
  simp only [topTiles, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, x, hx⟩
    have := box_V H.frame (H.vert i hi) hx
    omega
  · intro h
    exact ⟨hi, _, spine_V H.frame (H.vert i hi) (Y := b - 1) (by omega) (by omega)⟩

/-! ## The mirror image in coordinates -/

/-- The isometries of the mirror image. -/
def mirrorIso (a : ℤ) (g : GridIso) : GridIso :=
  (GridIso.flipX a).comp (g.comp (GridIso.flipX a))

theorem mirrorIso_swap (a : ℤ) (g : GridIso) : (mirrorIso a g).swap = g.swap := by
  simp [mirrorIso, GridIso.comp, GridIso.flipX]

theorem mirrorIso_negX (a : ℤ) {g : GridIso} (hg : g.swap = true) :
    (mirrorIso a g).negX = !g.negX := by
  simp [mirrorIso, GridIso.comp, GridIso.flipX, hg]

theorem mirrorIso_negY (a : ℤ) {g : GridIso} (hg : g.swap = true) :
    (mirrorIso a g).negY = !g.negY := by
  simp [mirrorIso, GridIso.comp, GridIso.flipX, hg]

theorem mirrorIso_boxX (a d : ℤ) {g : GridIso} (hg : g.swap = true) :
    (mirrorIso a g).boxX d = a - d - g.boxX d := by
  unfold GridIso.boxX
  rw [mirrorIso_negX a hg]
  simp only [mirrorIso, GridIso.comp, GridIso.flipX, GridIso.apply, hg]
  cases g.negX <;> simp <;> ring

theorem mirrorIso_boxY (a : ℤ) {g : GridIso} (hg : g.swap = true) :
    (mirrorIso a g).boxY a = g.boxY a := by
  unfold GridIso.boxY
  rw [mirrorIso_negY a hg]
  simp only [mirrorIso, GridIso.comp, GridIso.flipX, GridIso.apply, hg]
  cases g.negY <;> simp
  ring

/-- The tiles of the mirror image. -/
theorem mem_mirror (a : ℤ) (S : Finset Cell) (x y : ℤ) :
    (x, y) ∈ S.image (GridIso.flipX a).apply ↔ (a - 1 - x, y) ∈ S := by
  rw [GridIso.mem_image_iff]
  simp [GridIso.flipX, GridIso.inv, GridIso.apply]
  rw [show -x + (a - 1) = a - 1 - x by ring]

/-! ## Lemma 36 (b): the walls meet `T` in an interval -/

/-- Lemma 36 (b), the argument: a cell of column 0 below a cell of `T` is in `T`. -/
theorem col_zero_closed (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) {j i : ℤ} (hj : 0 ≤ j)
    (hji : j < i) (hi : (0, i) ∈ t i₀) : (0, j) ∈ t i₀ := by
  classical
  by_contra hjT
  have F := H.frame
  have hB := H.bounds hk
  have hib := box_T F hi
  have h00 : ((0 : ℤ), (0 : ℤ)) ∈ t i₀ := F.row0 0 le_rfl (by omega)
  have hj0 : 0 < j := by
    rcases eq_or_lt_of_le hj with h | h
    · rw [← h] at hjT
      exact absurd h00 hjT
    · exact h
  -- the tile `V` of `(0, j)` is vertical
  obtain ⟨v, hv⟩ := cover F (x := 0) (y := j) le_rfl (by omega) hj (by omega)
  have hvi : v ≠ i₀ := by
    rintro rfl
    exact hjT hv
  have hvs := H.vert v hvi
  have hvb := bounds_V F hvs
  have hVconn : EdgeConnected (t v) := (F.isTiling.tile_isPolyomino F.poly v).2
  -- the part of `V` in the rows up to `d` that is joined to `(0, j)`
  set A : Finset Cell := (t v).filter fun c => c.2 ≤ d with hA
  set C : Finset Cell := component A (0, j) with hC
  have hjA : ((0 : ℤ), j) ∈ A := Finset.mem_filter.2 ⟨hv, by simp; omega⟩
  have hjC : ((0 : ℤ), j) ∈ C := mem_component.2 ⟨hjA, Reach.refl _ _⟩
  have hCA : ∀ c ∈ C, c ∈ t v ∧ c.2 ≤ d := fun c hc =>
    Finset.mem_filter.1 (mem_component.1 hc).1
  have hCconn : EdgeConnected C := edgeConnected_component A (0, j)
  -- it reaches row `d`
  have hreach : ∃ x', (x', d) ∈ C := by
    by_contra hno
    push Not at hno
    have hlt : ∀ c ∈ C, c.2 < d := by
      rintro ⟨x, y⟩ hc
      rcases lt_or_eq_of_le (hCA _ hc).2 with h | h
      · exact h
      · simp only at h
        rw [h] at hc
        exact absurd hc (hno x)
    have hall : ∀ c, Reach (t v) (0, j) c → c ∈ C := by
      intro c hc
      induction hc with
      | refl => exact hjC
      | tail _ hstep ih =>
        rename_i p q
        have h1 := hlt _ ih
        have h2 := hstep.2.2
        refine component_closed ih (Finset.mem_filter.2 ⟨hstep.2.1, ?_⟩) h2
        unfold Adj at h2
        omega
    have htop := spine_V F hvs (Y := (κ v).boxY a + a - 1) (by omega) (by omega)
    have := hlt _ (hall _ (hVconn _ hv _ htop))
    simp only at this
    omega
  obtain ⟨x', hx'⟩ := hreach
  have hTR : t i₀ ⊆ R a (d + 1) := by
    rintro ⟨x, y⟩ hc
    have := box_T F hc
    exact mem_R.2 ⟨by simp; omega, by simp; omega⟩
  have hCR : C ⊆ R a (d + 1) := by
    rintro ⟨x, y⟩ hc
    have h1 := hCA _ hc
    have h2 := mem_R.1 (F.isTiling.subset_R v h1.1)
    simp only at h1 h2
    exact mem_R.2 ⟨by simp; omega, by simp; omega⟩
  obtain ⟨c, hcT, hcC⟩ := interlace_left (a := a) (b := d + 1) (by omega) (by omega) hTR F.poly.2
    hCR hCconn hj0 hji h00 hi hjC (q' := (x', d))
    ⟨hCR hx', Or.inr (Or.inr (Or.inr (by simp)))⟩ hx' (by simp; omega)
  exact hvi (uniq F (hCA c hcC).1 hcT)

/-- Lemma 36 (b) at column 0. -/
theorem col_zero (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) (y : ℤ) :
    (0, y) ∈ t i₀ ↔ 0 ≤ y ∧ y < colCount (t i₀) 0 := by
  refine col_initial (fun y h => (box_T H.frame h).2.1) (fun y y' h h0 hle => ?_) y
  rcases eq_or_lt_of_le hle with rfl | hlt
  · exact h
  · exact col_zero_closed H hk h0 hlt h

/-- Lemma 36 (b) at column `a - 1`. -/
theorem col_last (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) (y : ℤ) :
    (a - 1, y) ∈ t i₀ ↔ 0 ≤ y ∧ y < colCount (t i₀) (a - 1) := by
  have h := col_zero H.mirror hk y
  rw [mem_mirror, colCount_image_flipX] at h
  simpa using h

end H1

/-! ## Lemma 36 (d): the states of a wall -/

section Walls

variable {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell} {i₀ : Fin k} {κ : Fin k → GridIso}

/-- The state alpha of a wall. `x₀` is the first column of a box at the wall, `c` the
column of the wall, `o` the value of `negX` for a tile with its spine at the wall:
`0`, `0`, `false` on the left and `a - d`, `a - 1`, `true` on the right. Source:
`report-4.md`, Lemma 36 (d) (line 263). -/
def WallAlpha (a b d : ℤ) {k : ℕ} (t : Fin k → Finset Cell) (i₀ : Fin k) (κ : Fin k → GridIso)
    (x₀ c : ℤ) (o : Bool) : Prop :=
  ∃ w, w ≠ i₀ ∧ (κ w).boxY a = b - a ∧ (κ w).boxX d = x₀ ∧ (κ w).negX = o ∧
    (∀ i, i ≠ i₀ → (κ i).boxX d = x₀ → i = w) ∧ colCount (t i₀) c = b - a

/-- The state beta of a wall: a top tile `w` with its spine at the wall and a non-top
tile `z` with its far column there. Source: `report-4.md`, Lemma 36 (d) (line 264). -/
def WallBeta (a b d : ℤ) {k : ℕ} (t : Fin k → Finset Cell) (i₀ : Fin k) (κ : Fin k → GridIso)
    (x₀ c : ℤ) (o : Bool) : Prop :=
  ∃ w z, w ≠ i₀ ∧ z ≠ i₀ ∧ (κ w).boxY a = b - a ∧ (κ z).boxY a ≤ colCount (t i₀) c ∧
    (κ w).boxX d = x₀ ∧ (κ z).boxX d = x₀ ∧ (κ w).negX = o ∧ (κ z).negX = !o ∧
    (∀ i, i ≠ i₀ → (κ i).boxX d = x₀ → i = w ∨ i = z) ∧ colCount (t i₀) c < b - a ∧
    ∀ Y, (c, Y) ∈ t z ↔ colCount (t i₀) c ≤ Y ∧ Y < b - a

/-- The state gamma of a wall: a non-top tile `z` with its spine at the wall and a top
tile `w` with its far column there. Source: `report-4.md`, Lemma 36 (d) (line 265). -/
def WallGamma (a b d : ℤ) {k : ℕ} (t : Fin k → Finset Cell) (i₀ : Fin k) (κ : Fin k → GridIso)
    (x₀ c : ℤ) (o : Bool) : Prop :=
  ∃ w z, w ≠ i₀ ∧ z ≠ i₀ ∧ (κ w).boxY a = b - a ∧ (κ z).boxY a = colCount (t i₀) c ∧
    (κ w).boxX d = x₀ ∧ (κ z).boxX d = x₀ ∧ (κ w).negX = !o ∧ (κ z).negX = o ∧
    (∀ i, i ≠ i₀ → (κ i).boxX d = x₀ → i = w ∨ i = z) ∧ colCount (t i₀) c < b - a ∧
    ∀ Y, (c, Y) ∈ t w ↔ colCount (t i₀) c + a ≤ Y ∧ Y < b

/-- Vertical tiles have different spine columns when `b - a <= d < a`: every spine
meets row `b - a`. Source: `report-4.md`, Lemma 36 (a) (line 259). -/
theorem spine_ne (H : TypeH1 a b d t i₀ κ) (hh : b - a ≤ d) {i j : Fin k}
    (hi : i ≠ i₀) (hj : j ≠ i₀) (hij : i ≠ j) : (κ i).shift.1 ≠ (κ j).shift.1 := by
  intro h
  have hib := bounds_V H.frame (H.vert i hi)
  have hjb := bounds_V H.frame (H.vert j hj)
  have h1 := spine_V H.frame (H.vert i hi) (Y := b - a) (by omega) (by omega)
  have h2 := spine_V H.frame (H.vert j hj) (Y := b - a) (by omega) (by omega)
  rw [h] at h1
  exact hij (uniq H.frame h1 h2)

/-- Lemma 36 (f), first sentence. -/
theorem spine_not_top (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) (hda : d < a) (hh : b - a ≤ d)
    {z : Fin k} (hz : z ≠ i₀) (hzt : z ∉ topTiles b t i₀) :
    ((κ z).shift.1, d - 1) ∉ t i₀ := by
  intro h
  rw [mem_topTiles H hk hz] at hzt
  have hzb := bounds_V H.frame (H.vert z hz)
  have hB := H.bounds hk
  have h1 := spine_V H.frame (H.vert z hz) (Y := d - 1) (by omega) (by omega)
  exact hz (uniq H.frame h1 h)

/-- Lemma 36 (d) at column 0, with the rows of column 0 each tile holds. -/
theorem wall_left (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) (hda : d < a) (hh : b - a ≤ d) :
    WallAlpha a b d t i₀ κ 0 0 false ∨ WallBeta a b d t i₀ κ 0 0 false ∨
      WallGamma a b d t i₀ κ 0 0 false := by
  have F := H.frame
  have hB := H.bounds hk
  have hcol := col_zero H hk
  have hu1 : 1 ≤ colCount (t i₀) 0 := by
    have := (hcol 0).1 (F.row0 0 le_rfl (by omega))
    omega
  have hud : colCount (t i₀) 0 ≤ d := by
    have := (hcol (colCount (t i₀) 0 - 1)).2 ⟨by omega, by omega⟩
    have := box_T F this
    omega
  generalize hu : colCount (t i₀) 0 = u at hcol hu1 hud
  -- a vertical tile with a cell in column 0 has its box at column 0
  have hwall : ∀ i, i ≠ i₀ → ∀ Y, (0, Y) ∈ t i → (κ i).boxX d = 0 := by
    intro i hi Y hY
    have h1 := box_V F (H.vert i hi) hY
    have h2 := bounds_V F (H.vert i hi)
    omega
  have hcov : ∀ Y, u ≤ Y → Y < b → ∃ i, i ≠ i₀ ∧ (0, Y) ∈ t i ∧ (κ i).boxX d = 0 := by
    intro Y h1 h2
    obtain ⟨i, hi⟩ := cover F (x := 0) (y := Y) le_rfl (by omega) (by omega) h2
    have hi0 : i ≠ i₀ := by
      rintro rfl
      have := (hcol Y).1 hi
      omega
    exact ⟨i, hi0, hi, hwall i hi0 Y hi⟩
  -- two tiles at the wall with spines on the same side are equal
  have hsame : ∀ i j, i ≠ i₀ → j ≠ i₀ → (κ i).boxX d = 0 → (κ j).boxX d = 0 →
      (κ i).negX = (κ j).negX → i = j := by
    intro i j hi hj h1 h2 h3
    by_contra hij
    refine spine_ne H hh hi hj hij ?_
    rw [shift_eq (κ i) d, shift_eq (κ j) d, h1, h2, h3]
  -- the spine of an outer tile is in column 0
  have hout : ∀ i, i ≠ i₀ → (κ i).boxX d = 0 → (κ i).negX = false → ∀ Y, (κ i).boxY a ≤ Y →
      Y < (κ i).boxY a + a → (0, Y) ∈ t i := by
    intro i hi h1 h2 Y h3 h4
    have h5 := spine_V F (H.vert i hi) h3 h4
    rw [shift_eq (κ i) d, h1, h2] at h5
    simpa using h5
  have hne : ∀ i, i ≠ i₀ → ∀ Y, (0, Y) ∈ t i → u ≤ Y := by
    intro i hi Y hY
    by_contra hlt
    have h1 := box_V F (H.vert i hi) hY
    have h2 := bounds_V F (H.vert i hi)
    exact hi (uniq F hY ((hcol Y).2 ⟨by omega, by omega⟩))
  by_cases ho : ∃ v, v ≠ i₀ ∧ (κ v).boxX d = 0 ∧ (κ v).negX = false
  · obtain ⟨v, hv, hvx, hvn⟩ := ho
    have hvb := bounds_V F (H.vert v hv)
    have hvs := hout v hv hvx hvn
    have huv : u ≤ (κ v).boxY a := hne v hv _ (hvs _ le_rfl (by omega))
    by_cases hi : ∃ v', v' ≠ i₀ ∧ (κ v').boxX d = 0 ∧ (κ v').negX = true
    · -- two tiles at the wall
      obtain ⟨v', hv', hvx', hvn'⟩ := hi
      have hvv' : v ≠ v' := by
        rintro rfl
        rw [hvn] at hvn'
        exact absurd hvn' (by decide)
      have hvb' := bounds_V F (H.vert v' hv')
      have honly : ∀ i, i ≠ i₀ → (κ i).boxX d = 0 → i = v ∨ i = v' := by
        intro i hi hix
        cases hn : (κ i).negX
        · exact Or.inl (hsame i v hi hv hix hvx (hn.trans hvn.symm))
        · exact Or.inr (hsame i v' hi hv' hix hvx' (hn.trans hvn'.symm))
      have hcov2 : ∀ Y, u ≤ Y → Y < b → (0, Y) ∈ t v ∨ (0, Y) ∈ t v' := by
        intro Y h1 h2
        obtain ⟨i, hi0, hi, hix⟩ := hcov Y h1 h2
        rcases honly i hi0 hix with rfl | rfl
        · exact Or.inl hi
        · exact Or.inr hi
      -- the rows of `v'` in column 0
      have hv'c : ∀ Y, (0, Y) ∈ t v' → Y < (κ v).boxY a ∨ (κ v).boxY a + a ≤ Y := by
        intro Y hY
        by_contra hc
        exact hvv' (uniq F (hvs Y (by omega) (by omega)) hY)
      by_cases hgam : (κ v).boxY a = u
      · -- gamma
        obtain ⟨Y', hY'⟩ := col_V F (H.vert v' hv') (X := 0) (by omega) (by omega)
        have e1 := hne v' hv' _ hY'
        have e2 := hv'c _ hY'
        have e3 := box_V F (H.vert v' hv') hY'
        have hlt : u < b - a := by omega
        have hiff : ∀ Y, (0, Y) ∈ t v' ↔ u + a ≤ Y ∧ Y < b := by
          intro Y
          constructor
          · intro h
            have := hne v' hv' _ h
            have := hv'c _ h
            have := box_V F (H.vert v' hv') h
            omega
          · rintro ⟨h1, h2⟩
            rcases hcov2 Y (by omega) h2 with h | h
            · have := box_V F (H.vert v hv) h
              omega
            · exact h
        have e4 := box_V F (H.vert v' hv') ((hiff (b - 1)).2 ⟨by omega, by omega⟩)
        exact Or.inr (Or.inr ⟨v', v, hv', hv, by omega, by rw [hu]; exact hgam, hvx', hvx, hvn',
          hvn, fun i hi hix => (honly i hi hix).symm, by rw [hu]; exact hlt,
          by rw [hu]; exact hiff⟩)
      · -- beta
        have e0 : (0, u) ∈ t v' := by
          rcases hcov2 u le_rfl (by omega) with h | h
          · have := box_V F (H.vert v hv) h
            omega
          · exact h
        have e1 := box_V F (H.vert v' hv') e0
        have e2 := hv'c _ e0
        have hvtop : (κ v).boxY a = b - a := by
          rcases hcov2 (b - 1) (by omega) (by omega) with h | h
          · have := box_V F (H.vert v hv) h
            omega
          · have := box_V F (H.vert v' hv') h
            omega
        have hiff : ∀ Y, (0, Y) ∈ t v' ↔ u ≤ Y ∧ Y < b - a := by
          intro Y
          constructor
          · intro h
            have := hne v' hv' _ h
            have := hv'c _ h
            have := box_V F (H.vert v' hv') h
            omega
          · rintro ⟨h1, h2⟩
            rcases hcov2 Y (by omega) (by omega) with h | h
            · have := box_V F (H.vert v hv) h
              omega
            · exact h
        exact Or.inr (Or.inl ⟨v, v', hv, hv', hvtop, by rw [hu]; exact e1.2.1, hvx, hvx', hvn, hvn',
          honly, by rw [hu]; omega, by rw [hu]; exact hiff⟩)
    · -- alpha: one tile, spine in column 0
      have honly : ∀ i, i ≠ i₀ → (κ i).boxX d = 0 → i = v := by
        intro i hi' hix
        cases hn : (κ i).negX
        · exact hsame i v hi' hv hix hvx (hn.trans hvn.symm)
        · exact absurd ⟨i, hi', hix, hn⟩ hi
      have hall : ∀ Y, u ≤ Y → Y < b → (0, Y) ∈ t v := by
        intro Y h1 h2
        obtain ⟨i, hi0, hi, hix⟩ := hcov Y h1 h2
        rw [honly i hi0 hix] at hi
        exact hi
      have e1 := box_V F (H.vert v hv) (hall u le_rfl (by omega))
      have e2 := box_V F (H.vert v hv) (hall (b - 1) (by omega) (by omega))
      exact Or.inl ⟨v, hv, by omega, hvx, hvn, honly, by omega⟩
  · -- no spine in column 0: the fourth state
    exfalso
    obtain ⟨v, hv, hvt, hvx⟩ := hcov (b - 1) (by omega) (by omega)
    have hvn : (κ v).negX = true := by
      by_contra hn
      exact ho ⟨v, hv, hvx, by simpa using hn⟩
    have honly : ∀ i, i ≠ i₀ → (κ i).boxX d = 0 → i = v := by
      intro i hi hix
      refine hsame i v hi hv hix hvx ?_
      rw [hvn]
      by_contra hn
      exact ho ⟨i, hi, hix, by simpa using hn⟩
    have hall : ∀ Y, u ≤ Y → Y < b → (0, Y) ∈ t v := by
      intro Y h1 h2
      obtain ⟨i, hi0, hi, hix⟩ := hcov Y h1 h2
      rw [honly i hi0 hix] at hi
      exact hi
    have hvb := bounds_V F (H.vert v hv)
    have e2 := box_V F (H.vert v hv) hvt
    have e1 := box_V F (H.vert v hv) (hall u le_rfl (by omega))
    have hvY : (κ v).boxY a = b - a := by omega
    have hvtop : v ∈ topTiles b t i₀ := (mem_topTiles H hk hv).2 hvY
    -- `Top` is the image of the rows `[u, b)`
    have hTop : ∀ x, 0 ≤ x → x < a → u ≤ (if (κ v).negY then b - 1 - x else x + (b - a)) →
        (x, d - 1) ∈ t i₀ := by
      intro x h1 h2 h3
      have h4 := (mem_V F (H.vert v hv) _ _).1
        (hall (if (κ v).negY then b - 1 - x else x + (b - a)) h3 (by split <;> omega))
      rw [hvx, hvY, hvn] at h4
      convert h4 using 2
      · cases (κ v).negY <;> simp
      · simp
    by_cases hd : b - a = d
    · -- `h = d`: every column is in `Top`
      obtain ⟨z, hz, hzt⟩ := H.proposition28 hk hda
      have hzb := bounds_V F (H.vert z hz)
      refine spine_not_top H hk hda hh hz hzt (hTop _ ?_ ?_ ?_)
      · rw [shift_eq (κ z) d]
        split <;> omega
      · rw [shift_eq (κ z) d]
        split <;> omega
      · have h5 : 0 ≤ (κ z).shift.1 ∧ (κ z).shift.1 < a := by
          rw [shift_eq (κ z) d]
          split <;> omega
        split <;> omega
    · -- `h < d`: the cell `(d - 1, d - 1)` is in the spine of `v`
      have hsp : (d - 1, d - 1) ∈ t v := by
        have h5 := spine_V F (H.vert v hv) (Y := d - 1) (by omega) (by omega)
        rw [shift_eq (κ v) d, hvx, hvn] at h5
        simpa using h5
      have hnot : ¬ u ≤ (if (κ v).negY then b - 1 - (d - 1) else d - 1 + (b - a)) := by
        intro h5
        exact hv (uniq F hsp (hTop (d - 1) (by omega) (by omega) h5))
      have ha2 : a < 2 * d := by
        cases hn : (κ v).negY <;> rw [hn] at hnot <;> simp at hnot <;> omega
      -- the block of the top row that starts at column `d`
      have hmark : d ∈ colMarks a κ (topTiles b t i₀) := by
        refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_image.2 ⟨v, hvtop, ?_⟩))
        rw [shift_eq (κ v) d, hvx, hvn]
        simp
      have hamem : a ∈ (colMarks a κ (topTiles b t i₀)).filter fun m => d < m :=
        Finset.mem_filter.2 ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), hda⟩
      obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image
        ((colMarks a κ (topTiles b t i₀)).filter fun m => d < m) id ⟨a, hamem⟩
      obtain ⟨hmM, hdm⟩ := Finset.mem_filter.1 hm
      have hma : m ≤ a := hmin a hamem
      have hcons : Consecutive (colMarks a κ (topTiles b t i₀)) d m := by
        refine ⟨hmark, hmM, hdm, fun m' hm' => ?_⟩
        by_contra hc
        push Not at hc
        have := hmin m' (Finset.mem_filter.2 ⟨hm', hc.1⟩)
        simp at this
        omega
      have := (H.lemma25b hk hcons).1
      omega

/-- `WallAlpha` of the mirror image at the left wall is `WallAlpha` at the right
wall. -/
theorem wallAlpha_mirror (H : TypeH1 a b d t i₀ κ) :
    WallAlpha a b d (fun i => (t i).image (GridIso.flipX a).apply) i₀
        (fun i => mirrorIso a (κ i)) 0 0 false ↔
      WallAlpha a b d t i₀ κ (a - d) (a - 1) true := by
  unfold WallAlpha
  refine exists_congr fun w => and_congr_right fun hw => ?_
  rw [mirrorIso_boxY a (H.vert w hw), mirrorIso_boxX a d (H.vert w hw),
    mirrorIso_negX a (H.vert w hw), colCount_image_flipX]
  have h1 : (∀ i, i ≠ i₀ → (mirrorIso a (κ i)).boxX d = 0 → i = w) ↔
      ∀ i, i ≠ i₀ → (κ i).boxX d = a - d → i = w := by
    refine forall_congr' fun i => forall_congr' fun hi => ?_
    rw [mirrorIso_boxX a d (H.vert i hi)]
    refine ⟨fun h h' => h (by omega), fun h h' => h (by omega)⟩
  rw [h1]
  simp only [sub_zero, Bool.not_eq_false']
  refine ⟨?_, ?_⟩ <;> rintro ⟨h2, h3, h4, h5, h6⟩ <;> exact ⟨h2, by omega, h4, h5, h6⟩

/-- Lemma 36 (d) at column `a - 1`. -/
theorem wall_right (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) (hda : d < a) (hh : b - a ≤ d) :
    WallAlpha a b d t i₀ κ (a - d) (a - 1) true ∨ WallBeta a b d t i₀ κ (a - d) (a - 1) true ∨
      WallGamma a b d t i₀ κ (a - d) (a - 1) true := by
  have hm := fun i (hi : i ≠ i₀) => mirrorIso_boxX a d (H.vert i hi)
  rcases wall_left H.mirror hk hda hh with h | h | h
  · exact Or.inl ((wallAlpha_mirror H).1 h)
  · obtain ⟨w, z, hw, hz, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    change (mirrorIso a (κ w)).boxY a = _ at h1
    change (mirrorIso a (κ z)).boxY a ≤ _ at h2
    change (mirrorIso a (κ w)).boxX d = _ at h3
    change (mirrorIso a (κ z)).boxX d = _ at h4
    change (mirrorIso a (κ w)).negX = _ at h5
    change (mirrorIso a (κ z)).negX = _ at h6
    change ∀ i, i ≠ i₀ → (mirrorIso a (κ i)).boxX d = 0 → _ at h7
    rw [colCount_image_flipX, sub_zero] at h2 h8
    rw [mirrorIso_boxY a (H.vert w hw)] at h1
    rw [mirrorIso_boxY a (H.vert z hz)] at h2
    rw [hm w hw] at h3
    rw [hm z hz] at h4
    rw [mirrorIso_negX a (H.vert w hw)] at h5
    rw [mirrorIso_negX a (H.vert z hz)] at h6
    refine Or.inr (Or.inl ⟨w, z, hw, hz, h1, h2, by omega, by omega, by simpa using h5,
      by simpa using h6, fun i hi hix => h7 i hi (by rw [hm i hi]; omega), h8, fun Y => ?_⟩)
    have := h9 Y
    rw [mem_mirror, colCount_image_flipX, sub_zero] at this
    exact this
  · obtain ⟨w, z, hw, hz, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    change (mirrorIso a (κ w)).boxY a = _ at h1
    change (mirrorIso a (κ z)).boxY a = _ at h2
    change (mirrorIso a (κ w)).boxX d = _ at h3
    change (mirrorIso a (κ z)).boxX d = _ at h4
    change (mirrorIso a (κ w)).negX = _ at h5
    change (mirrorIso a (κ z)).negX = _ at h6
    change ∀ i, i ≠ i₀ → (mirrorIso a (κ i)).boxX d = 0 → _ at h7
    rw [colCount_image_flipX, sub_zero] at h2 h8
    rw [mirrorIso_boxY a (H.vert w hw)] at h1
    rw [mirrorIso_boxY a (H.vert z hz)] at h2
    rw [hm w hw] at h3
    rw [hm z hz] at h4
    rw [mirrorIso_negX a (H.vert w hw)] at h5
    rw [mirrorIso_negX a (H.vert z hz)] at h6
    refine Or.inr (Or.inr ⟨w, z, hw, hz, h1, h2, by omega, by omega, by simpa using h5,
      by simpa using h6, fun i hi hix => h7 i hi (by rw [hm i hi]; omega), h8, fun Y => ?_⟩)
    have := h9 Y
    rw [mem_mirror, colCount_image_flipX, sub_zero] at this
    exact this

/-- The wall column is at most `h = b - a` high (Lemma 36 (e), first sentence). -/
theorem col_le (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) (hda : d < a) (hh : b - a ≤ d) :
    colCount (t i₀) 0 ≤ b - a ∧ colCount (t i₀) (a - 1) ≤ b - a := by
  constructor
  · rcases wall_left H hk hda hh with ⟨w, h⟩ | ⟨w, z, h⟩ | ⟨w, z, h⟩
    · exact h.2.2.2.2.2.le
    · exact h.2.2.2.2.2.2.2.2.2.1.le
    · exact h.2.2.2.2.2.2.2.2.2.1.le
  · rcases wall_right H hk hda hh with ⟨w, h⟩ | ⟨w, z, h⟩ | ⟨w, z, h⟩
    · exact h.2.2.2.2.2.le
    · exact h.2.2.2.2.2.2.2.2.2.1.le
    · exact h.2.2.2.2.2.2.2.2.2.1.le

end Walls

/-! ## Proposition 38: the tail, Steps 3 and 4

The last steps of Proposition 38 are about five sets of cells `T`, `W_1`, `W_2`,
`Z_1`, `Z_2` that fill a rectangle of `2h` columns and `3h` rows. They are stated
for predicates, without the tiling: every step is the covering of a cell by
exactly one of the five, and the membership of a cell in a tile as a membership
in `T`. -/

/-- The normal form in which the tail and Steps 3 and 4 of Proposition 38 work.
Source: `report-4.md` (line 288): "So in every case a = 2h, b = 3h, u_0 = h, W_1 has
spine column 0 and box [0, d) x [h, 3h), no other tile has x_i = 0, and W_1 reverses
the order. Put e = a - d. Z_1 has 1 <= x_1 <= e - 1." `n₁` says that the spine of
`Z_1` is the last column of its box, `m₁` that `Z_1` reverses the order. -/
structure NF38 (d h s u₁ x₁ y₁ y₂ : ℤ) (n₁ m₁ : Bool)
    (T W₁ W₂ Z₁ Z₂ : ℤ → ℤ → Prop) : Prop where
  /-- The case of section 5c. -/
  h_le : h ≤ d
  /-- `d < a`. -/
  d_lt : d < 2 * h
  /-- Row 0 is full. -/
  s_pos : 1 ≤ s
  /-- The box of `T`. -/
  T_box : ∀ x y, T x y → (0 ≤ x ∧ x < 2 * h) ∧ 0 ≤ y ∧ y < d
  /-- The rows `[0, s)` are full. -/
  T_full : ∀ x y, 0 ≤ x → x < 2 * h → 0 ≤ y → y < s → T x y
  /-- `T` meets column 0 in the rows `[0, u_0)`, and `u_0 = h`. -/
  T_zero : ∀ y, T 0 y ↔ 0 ≤ y ∧ y < h
  /-- `T` has a cell in every row of its box. -/
  T_rows : ∀ y, 0 ≤ y → y < d → ∃ x, T x y
  /-- `(a - 1, 0)` is in `T`. -/
  u₁_pos : 1 ≤ u₁
  /-- The right wall is in state beta' or gamma'. -/
  u₁_lt : u₁ < h
  /-- Every cell is in one of the five sets. -/
  cover : ∀ x y, 0 ≤ x → x < 2 * h → 0 ≤ y → y < 3 * h →
    T x y ∨ W₁ x y ∨ W₂ x y ∨ Z₁ x y ∨ Z₂ x y
  /-- No cell is in two of the five sets (this and the next nine fields). -/
  dTW₁ : ∀ x y, T x y → W₁ x y → False
  dTW₂ : ∀ x y, T x y → W₂ x y → False
  dTZ₁ : ∀ x y, T x y → Z₁ x y → False
  dTZ₂ : ∀ x y, T x y → Z₂ x y → False
  dW₁W₂ : ∀ x y, W₁ x y → W₂ x y → False
  dW₁Z₁ : ∀ x y, W₁ x y → Z₁ x y → False
  dW₁Z₂ : ∀ x y, W₁ x y → Z₂ x y → False
  dW₂Z₁ : ∀ x y, W₂ x y → Z₁ x y → False
  dW₂Z₂ : ∀ x y, W₂ x y → Z₂ x y → False
  dZ₁Z₂ : ∀ x y, Z₁ x y → Z₂ x y → False
  /-- `W_1` has spine column 0 and box `[0, d) x [h, 3h)` and reverses the order. -/
  W₁_mem : ∀ X Y, W₁ X Y ↔ T (3 * h - 1 - Y) X
  /-- `Z_1` has the box `[x_1, x_1 + d) x [y_1, y_1 + 2h)`. -/
  Z₁_mem : ∀ X Y, Z₁ X Y ↔
    T (if m₁ then y₁ + 2 * h - 1 - Y else Y - y₁) (if n₁ then x₁ + d - 1 - X else X - x₁)
  /-- `Z_1` is not at the left wall. -/
  x₁_pos : 1 ≤ x₁
  /-- `Z_1` is not at the right wall. -/
  x₁_lt : x₁ < 2 * h - d
  /-- Lemma 30 (a). -/
  s_le_y₁ : s ≤ y₁
  /-- `Z_1` is not a top tile. -/
  y₁_lt : y₁ < h
  /-- Lemma 30 (a). -/
  s_le_y₂ : s ≤ y₂
  /-- `Z_2` is not a top tile. -/
  y₂_lt : y₂ < h
  /-- One of the two is a bottom tile (Lemma 30 (a)). -/
  low : y₁ = s ∨ y₂ = s

namespace NF38

variable {d h s u₁ x₁ y₁ y₂ : ℤ} {n₁ m₁ : Bool} {T W₁ W₂ Z₁ Z₂ : ℤ → ℤ → Prop}

/-- The box of `Z_1`. -/
theorem Z₁_box (N : NF38 d h s u₁ x₁ y₁ y₂ n₁ m₁ T W₁ W₂ Z₁ Z₂) {X Y : ℤ} (hZ : Z₁ X Y) :
    (x₁ ≤ X ∧ X < x₁ + d) ∧ y₁ ≤ Y ∧ Y < y₁ + 2 * h := by
  have hT := N.T_box _ _ ((N.Z₁_mem X Y).1 hZ)
  cases n₁ <;> cases m₁ <;> simp at hT <;> omega

/-- The box of `W_1`. -/
theorem W₁_box (N : NF38 d h s u₁ x₁ y₁ y₂ n₁ m₁ T W₁ W₂ Z₁ Z₂) {X Y : ℤ} (hW : W₁ X Y) :
    (0 ≤ X ∧ X < d) ∧ h ≤ Y ∧ Y < 3 * h := by
  have hT := N.T_box _ _ ((N.W₁_mem X Y).1 hW)
  omega

/-- Every column of the box of `Z_1` holds a cell of `Z_1`. -/
theorem Z₁_col (N : NF38 d h s u₁ x₁ y₁ y₂ n₁ m₁ T W₁ W₂ Z₁ Z₂) {X : ℤ} (h1 : x₁ ≤ X)
    (h2 : X < x₁ + d) : ∃ Y, Z₁ X Y := by
  obtain ⟨x, hx⟩ := N.T_rows (if n₁ then x₁ + d - 1 - X else X - x₁)
    (by split <;> omega) (by split <;> omega)
  refine ⟨if m₁ then y₁ + 2 * h - 1 - x else x + y₁, (N.Z₁_mem _ _).2 ?_⟩
  have : (if m₁ then y₁ + 2 * h - 1 - (if m₁ then y₁ + 2 * h - 1 - x else x + y₁)
      else (if m₁ then y₁ + 2 * h - 1 - x else x + y₁) - y₁) = x := by
    cases m₁ <;> simp
  rw [this]
  exact hx

/-- The thick spine of `Z_1`. -/
theorem Z₁_spine (N : NF38 d h s u₁ x₁ y₁ y₂ n₁ m₁ T W₁ W₂ Z₁ Z₂) {j Y : ℤ} (hj : 0 ≤ j)
    (hjs : j < s) (h1 : y₁ ≤ Y) (h2 : Y < y₁ + 2 * h) :
    Z₁ (if n₁ then x₁ + d - 1 - j else x₁ + j) Y := by
  refine (N.Z₁_mem _ _).2 (N.T_full _ _ ?_ ?_ ?_ ?_) <;> cases n₁ <;> cases m₁ <;> simp <;> omega

/-- Proposition 38, the tail for `h = d`. Source: `report-4.md` (line 290): "Suppose
a = 2d, the boxes of W_2 and Z_2 have the columns [d, 2d), y_2 = u_1 < d,
Top = [0, d - u_1), Z_2 contains [d, 2d) x {u_1}, and Z_1 has no cell (d, r) with
r >= u_1." The end: the cell `(s, 3d - 1 - x_1)` is uncovered. -/
theorem tail (N : NF38 d h s u₁ x₁ y₁ y₂ n₁ m₁ T W₁ W₂ Z₁ Z₂) (hd : h = d)
    (hW₂ : ∀ X Y, W₂ X Y → d ≤ X) (hZ₂ : ∀ X Y, Z₂ X Y → d ≤ X) (hy₂ : y₂ = u₁)
    (hTop : ∀ x, T x (d - 1) ↔ 0 ≤ x ∧ x < d - u₁)
    (hrow : ∀ X, d ≤ X → X < 2 * d → Z₂ X u₁) (hcol : ∀ r, u₁ ≤ r → ¬ Z₁ d r) : False := by
  have b1 := N.h_le; have b2 := N.d_lt; have b3 := N.s_pos; have b4 := N.u₁_pos
  have b5 := N.u₁_lt; have b6 := N.x₁_pos; have b7 := N.x₁_lt; have b8 := N.s_le_y₁
  have b9 := N.y₁_lt; have b10 := N.s_le_y₂; have b11 := N.low
  -- `Z_1` has a cell in column `d`, so `y_1 < u_1` and `s = y_1`
  obtain ⟨r, hr⟩ := N.Z₁_col (X := d) (by omega) (by omega)
  have hrb := N.Z₁_box hr
  have hru : r < u₁ := by
    by_contra hle
    exact hcol r (by omega) hr
  have hs : y₁ = s := by omega
  -- its spine is column `x_1`
  have hspine := fun (j Y : ℤ) => N.Z₁_spine (j := j) (Y := Y)
  have hn : n₁ = false := by
    by_contra hn
    have hn' : n₁ = true := by simpa using hn
    have h1 := hspine 0 u₁ le_rfl (by omega) (by omega) (by omega)
    rw [hn'] at h1
    simp only [ite_true, sub_zero] at h1
    exact N.dZ₁Z₂ _ _ h1 (hrow _ (by omega) (by omega))
  -- `T` meets column `x_1` in the rows `[0, s)`
  have hcolx : ∀ y, T x₁ y → y < s := by
    intro y hy
    by_contra hys
    have hyb := N.T_box _ _ hy
    have h1 := hspine 0 y le_rfl (by omega) (by omega) (by omega)
    rw [hn] at h1
    simp only [Bool.false_eq_true, ite_false, add_zero] at h1
    exact N.dTZ₁ _ _ hy h1
  -- `T` contains `[0, x_1) x [0, d)`
  have hT : T (x₁ - 1) (d - 1) := by
    rcases N.cover (x₁ - 1) (d - 1) (by omega) (by omega) (by omega) (by omega) with
      h1 | h1 | h1 | h1 | h1
    · exact h1
    · have := N.W₁_box h1; omega
    · have := hW₂ _ _ h1; omega
    · have := N.Z₁_box h1; omega
    · have := hZ₂ _ _ h1; omega
  have e1 := (hTop _).1 hT
  have e2 : d - u₁ ≤ x₁ := by
    by_contra hlt
    have := hcolx _ ((hTop x₁).2 ⟨by omega, by omega⟩)
    omega
  -- the cell `(s, 3d - 1 - x_1)` is uncovered
  rcases N.cover s (3 * d - 1 - x₁) (by omega) (by omega) (by omega) (by omega) with
    h1 | h1 | h1 | h1 | h1
  · have := N.T_box _ _ h1; omega
  · rw [N.W₁_mem] at h1
    rw [show 3 * h - 1 - (3 * d - 1 - x₁) = x₁ by omega] at h1
    have := hcolx _ h1
    omega
  · have := hW₂ _ _ h1; omega
  · have := N.Z₁_box h1; omega
  · have := hZ₂ _ _ h1; omega

/-- Proposition 38, Step 3 (alpha, gamma'). Source: `report-4.md` (line 292): "Z_2 has
spine column 2d - 1 and y_2 = u_1; W_2 has spine column d and meets column 2d - 1 in
the top t = d - u_1 rows". -/
theorem step3 {m₂ : Bool} (N : NF38 d h s u₁ x₁ y₁ y₂ n₁ m₁ T W₁ W₂ Z₁ Z₂) (hd : h = d)
    (hy₂ : y₂ = u₁) (hW₂ : ∀ X Y, W₂ X Y ↔ T (3 * h - 1 - Y) (X - d))
    (hZ₂ : ∀ X Y, Z₂ X Y ↔ T (if m₂ then y₂ + 2 * h - 1 - Y else Y - y₂) (2 * h - 1 - X))
    (hcolW₂ : ∀ Y, W₂ (2 * h - 1) Y ↔ u₁ + 2 * h ≤ Y ∧ Y < 3 * h) : False := by
  have b1 := N.h_le; have b2 := N.d_lt; have b3 := N.s_pos; have b4 := N.u₁_pos
  have b5 := N.u₁_lt; have b9 := N.y₁_lt
  -- `Top = [0, d - u_1)`
  have hTop : ∀ x, T x (d - 1) ↔ 0 ≤ x ∧ x < d - u₁ := by
    intro x
    have h1 := (hW₂ (2 * h - 1) (3 * h - 1 - x)).symm.trans (hcolW₂ _)
    rw [show 3 * h - 1 - (3 * h - 1 - x) = x by omega, show 2 * h - 1 - d = d - 1 by omega] at h1
    rw [h1]
    omega
  -- the spine of `W_2` in column `d`
  have hspW : ∀ Y, h ≤ Y → Y < 3 * h → W₂ d Y := by
    intro Y h1 h2
    rw [hW₂]
    exact N.T_full _ _ (by omega) (by omega) (by omega) (by omega)
  -- `Z_2` keeps the order
  have hm : m₂ = false := by
    by_contra hm
    have hm' : m₂ = true := by simpa using hm
    have h1 : Z₂ d (y₂ + 2 * h - 1) := by
      rw [hZ₂, hm']
      simp only [ite_true]
      rw [show y₂ + 2 * h - 1 - (y₂ + 2 * h - 1) = 0 by omega, show 2 * h - 1 - d = d - 1 by omega,
        hTop]
      omega
    exact N.dW₂Z₂ _ _ (hspW _ (by omega) (by omega)) h1
  subst hm
  simp only [Bool.false_eq_true, ite_false] at hZ₂
  refine N.tail hd ?_ ?_ hy₂ hTop ?_ ?_
  · intro X Y h1
    have := N.T_box _ _ ((hW₂ _ _).1 h1); omega
  · intro X Y h1
    have := N.T_box _ _ ((hZ₂ _ _).1 h1); omega
  · intro X h1 h2
    rw [hZ₂, hy₂, sub_self, N.T_zero]
    omega
  · intro r h1 h2
    have hrb := N.Z₁_box h2
    by_cases hrd : r < d
    · refine N.dZ₁Z₂ _ _ h2 ?_
      rw [hZ₂, show 2 * h - 1 - d = d - 1 by omega, hTop]
      omega
    · exact N.dW₂Z₁ _ _ (hspW r (by omega) (by omega)) h2

/-- Proposition 38, Step 4 (alpha, beta'). Source: `report-4.md` (lines 294-299): "Z_2
has box [e, 2h) x [y_2, y_2 + 2h), spine column e, and meets column 2h - 1 in the
rows [u_1, h); t = h - u_1." Here `e` is `2h - d`. The sub-steps (1), (2), (3) of the
report are `s1`, `s2`, `s3`; then `h = d` (the tail), and for `h < d` the spine of
`Z_1` in column `x_1` (`n₁ = false`) or in column `x_1 + d - 1` (`n₁ = true`). -/
theorem step4 {m₂ : Bool} (N : NF38 d h s u₁ x₁ y₁ y₂ n₁ m₁ T W₁ W₂ Z₁ Z₂)
    (hu : u₁ ≤ h - s) (hlast : ∀ y, T (2 * h - 1) y ↔ 0 ≤ y ∧ y < u₁)
    (hW₂ : ∀ X Y, W₂ X Y ↔ T (3 * h - 1 - Y) (2 * h - 1 - X))
    (hZ₂ : ∀ X Y, Z₂ X Y ↔
      T (if m₂ then y₂ + 2 * h - 1 - Y else Y - y₂) (X - (2 * h - d)))
    (hcolZ₂ : ∀ Y, Z₂ (2 * h - 1) Y ↔ u₁ ≤ Y ∧ Y < h) : False := by
  have b1 := N.h_le; have b2 := N.d_lt; have b3 := N.s_pos; have b4 := N.u₁_pos
  have b5 := N.u₁_lt; have b6 := N.x₁_pos; have b7 := N.x₁_lt; have b8 := N.s_le_y₁
  have b9 := N.y₁_lt; have b10 := N.s_le_y₂; have b11 := N.low; have b12 := N.y₂_lt
  -- boxes
  have hW₂b : ∀ X Y, W₂ X Y → (2 * h - d ≤ X ∧ X < 2 * h) ∧ h ≤ Y ∧ Y < 3 * h := by
    intro X Y h1
    have := N.T_box _ _ ((hW₂ _ _).1 h1); omega
  have hZ₂b : ∀ X Y, Z₂ X Y → (2 * h - d ≤ X ∧ X < 2 * h) ∧ y₂ ≤ Y ∧ Y < y₂ + 2 * h := by
    intro X Y h1
    have := N.T_box _ _ ((hZ₂ _ _).1 h1)
    cases m₂ <;> simp at this <;> omega
  -- thick spines
  have hspW₁ : ∀ X Y, 0 ≤ X → X < s → h ≤ Y → Y < 3 * h → W₁ X Y := by
    intro X Y h1 h2 h3 h4
    rw [N.W₁_mem]
    exact N.T_full _ _ (by omega) (by omega) (by omega) (by omega)
  have hspZ₂ : ∀ X Y, 2 * h - d ≤ X → X < 2 * h - d + s → y₂ ≤ Y → Y < y₂ + 2 * h → Z₂ X Y := by
    intro X Y h1 h2 h3 h4
    rw [hZ₂]
    refine N.T_full _ _ ?_ ?_ (by omega) (by omega) <;> cases m₂ <;> simp <;> omega
  have hy₂u : y₂ ≤ u₁ := (hZ₂b _ _ ((hcolZ₂ u₁).2 ⟨le_rfl, b5⟩)).2.1
  -- `Top` lies in `[0, h - y_2)`
  have hTopsub : ∀ x, T x (d - 1) → x < h - y₂ := by
    intro x hx
    by_contra hge
    have hxb := N.T_box _ _ hx
    have h1 : W₂ (2 * h - d) (3 * h - 1 - x) := by
      rw [hW₂, show 3 * h - 1 - (3 * h - 1 - x) = x by omega,
        show 2 * h - 1 - (2 * h - d) = d - 1 by omega]
      exact hx
    exact N.dW₂Z₂ _ _ h1 (hspZ₂ _ _ (by omega) (by omega) (by omega) (by omega))
  -- `Z_2` keeps the order and `Top = [u_1 - y_2, h - y_2)`
  have hm : m₂ = false := by
    by_contra hm
    have hm' : m₂ = true := by simpa using hm
    have h1 := (hcolZ₂ u₁).2 ⟨le_rfl, b5⟩
    rw [hZ₂, hm'] at h1
    simp only [ite_true] at h1
    rw [show 2 * h - 1 - (2 * h - d) = d - 1 by omega] at h1
    have := hTopsub _ h1
    omega
  subst hm
  simp only [Bool.false_eq_true, ite_false] at hZ₂
  have hTop : ∀ x, T x (d - 1) ↔ u₁ - y₂ ≤ x ∧ x < h - y₂ := by
    intro x
    have h1 := (hZ₂ (2 * h - 1) (x + y₂)).symm.trans (hcolZ₂ _)
    rw [show 2 * h - 1 - (2 * h - d) = d - 1 by omega, show x + y₂ - y₂ = x by omega] at h1
    rw [h1]
    omega
  -- (1) `T` contains `[0, x_1) x [0, h)`
  have s1 : ∀ x y, 0 ≤ x → x < x₁ → 0 ≤ y → y < h → T x y := by
    intro x y h1 h2 h3 h4
    rcases N.cover x y (by omega) (by omega) (by omega) (by omega) with h5 | h5 | h5 | h5 | h5
    · exact h5
    · have := N.W₁_box h5; omega
    · have := hW₂b _ _ h5; omega
    · have := N.Z₁_box h5; omega
    · have := hZ₂b _ _ h5; omega
  -- (2) if a column of `T` holds the rows `[0, h)` it holds nothing else
  have s2 : ∀ x, 0 ≤ x → x < 2 * h → (∀ y, 0 ≤ y → y < h → T x y) → ∀ y, T x y → y < h := by
    intro x h1 h2 hfull y hy
    by_contra hyh
    have hyb := N.T_box _ _ hy
    have h3 : W₁ y (3 * h - 1 - x) := by
      rw [N.W₁_mem, show 3 * h - 1 - (3 * h - 1 - x) = x by omega]
      exact hy
    have h4 : W₂ y (3 * h - 1 - x) := by
      rw [hW₂, show 3 * h - 1 - (3 * h - 1 - x) = x by omega]
      exact hfull _ (by omega) (by omega)
    exact N.dW₁W₂ _ _ h3 h4
  -- (3) rows `x < x_1` of `T` are full, and the spine of `Z_1` avoids them
  have s3 : ∀ x, 0 ≤ x → x < x₁ → ∀ x', 0 ≤ x' → x' < 2 * h → T x' x := by
    intro x h1 h2 x' h3 h4
    rcases N.cover x (3 * h - 1 - x') (by omega) (by omega) (by omega) (by omega) with
      h5 | h5 | h5 | h5 | h5
    · have := s2 x h1 (by omega) (fun y => s1 x y h1 h2) _ h5
      omega
    · rw [N.W₁_mem, show 3 * h - 1 - (3 * h - 1 - x') = x' by omega] at h5
      exact h5
    · have := hW₂b _ _ h5; omega
    · have := N.Z₁_box h5; omega
    · have := hZ₂b _ _ h5; omega
  by_cases hhd : h = d
  · -- `h = d`
    have h0 := (hTop 0).1 (by
      have := s1 0 (d - 1) le_rfl (by omega) (by omega) (by omega)
      exact this)
    have hyu : y₂ = u₁ := by omega
    have hTop' : ∀ x, T x (d - 1) ↔ 0 ≤ x ∧ x < d - u₁ := by
      intro x
      rw [hTop]
      omega
    refine N.tail hhd ?_ ?_ hyu hTop' ?_ ?_
    · intro X Y h1
      have := hW₂b _ _ h1; omega
    · intro X Y h1
      have := hZ₂b _ _ h1; omega
    · intro X h1 h2
      rw [hZ₂, hyu, sub_self, N.T_zero]
      omega
    · intro r h1 h2
      have hrb := N.Z₁_box h2
      by_cases hr : r < y₂ + 2 * h
      · exact N.dZ₁Z₂ _ _ h2 (hspZ₂ _ _ (by omega) (by omega) (by omega) hr)
      · refine N.dW₂Z₁ _ _ ?_ h2
        rw [hW₂, show 2 * h - 1 - d = d - 1 by omega, hTop']
        omega
  · -- `h < d`
    have hlt : h < d := by omega
    -- `Top` avoids the thick spine of `W_1`: `u_1 - y_2 >= s`
    have hTs : s ≤ u₁ - y₂ := by
      by_contra hc
      have h1 := (hTop (u₁ - y₂)).2 ⟨le_rfl, by omega⟩
      exact N.dTW₁ _ _ h1 (hspW₁ _ _ (by omega) (by omega) (by omega) (by omega))
    -- `x_1 <= s`
    have hxs : x₁ ≤ s := by
      by_contra hc
      -- otherwise row `s` is full by (3), but a bottom tile has a cell there
      rcases b11 with hb | hb
      · -- `Z_1` is a bottom tile: its spine has a cell of row `s`
        have h1 := N.Z₁_spine (j := 0) (Y := s) le_rfl (by omega) (by omega) (by omega)
        refine N.dTZ₁ _ _ (s3 s (by omega) (by omega) _ ?_ ?_) h1 <;> cases n₁ <;> simp <;> omega
      · exact N.dTZ₂ _ _ (s3 s (by omega) (by omega) (2 * h - d) (by omega) (by omega))
          (hspZ₂ _ _ le_rfl (by omega) (by omega) (by omega))
    cases n₁
    · -- spine of `Z_1` in column `x_1`
      have hspZ₁ : ∀ Y, y₁ ≤ Y → Y < y₁ + 2 * h → Z₁ x₁ Y := by
        intro Y h1 h2
        have := N.Z₁_spine (j := 0) (Y := Y) le_rfl (by omega) h1 h2
        simpa using this
      have hx : x₁ = s := by
        by_contra hne
        exact N.dW₁Z₁ _ _ (hspW₁ x₁ h (by omega) (by omega) le_rfl (by omega))
          (hspZ₁ h (by omega) (by omega))
      -- `T` meets column `s` in `[0, y_1)`
      have hcol : ∀ y, T s y ↔ 0 ≤ y ∧ y < y₁ := by
        intro y
        constructor
        · intro h1
          have hb := N.T_box _ _ h1
          refine ⟨hb.2.1, ?_⟩
          by_contra hge
          have h2 := hspZ₁ y (by omega) (by omega)
          rw [hx] at h2
          exact N.dTZ₁ _ _ h1 h2
        · rintro ⟨h1, h2⟩
          rcases N.cover s y (by omega) (by omega) (by omega) (by omega) with
            h5 | h5 | h5 | h5 | h5
          · exact h5
          · have := N.W₁_box h5; omega
          · have := hW₂b _ _ h5; omega
          · have := N.Z₁_box h5; omega
          · have := hZ₂b _ _ h5; omega
      -- row `r = 3h - 1 - s`
      have key : ∀ X, y₁ ≤ X → X < 2 * h - y₁ → Z₁ X (3 * h - 1 - s) := by
        intro X h1 h2
        rcases N.cover X (3 * h - 1 - s) (by omega) (by omega) (by omega) (by omega) with
          h5 | h5 | h5 | h5 | h5
        · have := N.T_box _ _ h5; omega
        · rw [N.W₁_mem, show 3 * h - 1 - (3 * h - 1 - s) = s by omega, hcol] at h5
          omega
        · rw [hW₂, show 3 * h - 1 - (3 * h - 1 - s) = s by omega, hcol] at h5
          omega
        · exact h5
        · have := hZ₂b _ _ h5; omega
      have h1 := N.Z₁_box (key y₁ le_rfl (by omega))
      have h2 : y₁ ≤ s := by
        by_contra hc
        refine N.dW₁Z₁ s (3 * h - 1 - s) ?_ ?_
        · rw [N.W₁_mem, show 3 * h - 1 - (3 * h - 1 - s) = s by omega, hcol]
          omega
        · rw [← hx]
          exact hspZ₁ _ (by omega) (by omega)
      omega
    · -- spine of `Z_1` in column `c = x_1 + d - 1`
      have hspZ₁ : ∀ Y, y₁ ≤ Y → Y < y₁ + 2 * h → Z₁ (x₁ + d - 1) Y := by
        intro Y h1 h2
        have := N.Z₁_spine (j := 0) (Y := Y) le_rfl (by omega) h1 h2
        simpa using this
      -- row `h`: `c < 2h - u_1`
      have c1 : x₁ + d - 1 < 2 * h - u₁ := by
        by_contra hc
        refine N.dW₂Z₁ (x₁ + d - 1) h ?_ (hspZ₁ h (by omega) (by omega))
        rw [hW₂, show 3 * h - 1 - h = 2 * h - 1 by omega, hlast]
        omega
      -- `Top` avoids `e = 2h - d` and starts below it
      have c2 : h - y₂ ≤ 2 * h - d := by
        by_contra hc
        have h1 := (hTop (2 * h - d)).2 ⟨by omega, by omega⟩
        exact N.dTZ₂ _ _ h1 (hspZ₂ _ _ le_rfl (by omega) (by omega) (by omega))
      -- the cell `(0, ka)`, `ka = c - e`
      have c3 : T 0 (x₁ + 2 * d - 1 - 2 * h) := (N.T_zero _).2 ⟨by omega, by omega⟩
      have c4 : Z₂ (x₁ + d - 1) y₂ := by
        rw [hZ₂, sub_self, show x₁ + d - 1 - (2 * h - d) = x₁ + 2 * d - 1 - 2 * h by omega]
        exact c3
      have c5 : y₂ < y₁ := by
        by_contra hc
        exact N.dZ₁Z₂ _ _ (hspZ₁ _ (by omega) (by omega)) c4
      have c6 : y₂ = s := by omega
      -- `Z_1` reverses the order
      have hm₁ : m₁ = true := by
        by_contra hm
        have hm' : m₁ = false := by simpa using hm
        subst hm'
        have h1 : Z₁ (2 * h - d) y₁ := by
          rw [N.Z₁_mem]
          simp only [Bool.false_eq_true, ite_false, ite_true, sub_self]
          rw [show x₁ + d - 1 - (2 * h - d) = x₁ + 2 * d - 1 - 2 * h by omega]
          exact c3
        exact N.dZ₁Z₂ _ _ h1 (hspZ₂ _ _ le_rfl (by omega) (by omega) (by omega))
      subst hm₁
      -- the cells of `Z_1` in column `x_1`
      have hZcol : ∀ Y, Z₁ x₁ Y ↔ T (y₁ + 2 * h - 1 - Y) (d - 1) := by
        intro Y
        rw [N.Z₁_mem]
        simp only [ite_true]
        rw [show x₁ + d - 1 - x₁ = d - 1 by omega]
      have hx : x₁ = s := by
        by_contra hne
        have h1 : Z₁ x₁ (y₁ + 2 * h - 1 - (u₁ - y₂)) := by
          rw [hZcol, hTop]
          omega
        have := N.Z₁_box h1
        exact N.dW₁Z₁ _ _ (hspW₁ x₁ _ (by omega) (by omega) (by omega) (by omega)) h1
      -- `T` contains `{s} x [0, h)`
      have d1 : ∀ y, 0 ≤ y → y < h → T s y := by
        intro y h1 h2
        rcases N.cover s y (by omega) (by omega) (by omega) (by omega) with h5 | h5 | h5 | h5 | h5
        · exact h5
        · have := N.W₁_box h5; omega
        · have := hW₂b _ _ h5; omega
        · rw [← hx, hZcol, hTop] at h5
          omega
        · have := hZ₂b _ _ h5; omega
      have d2 := s2 s (by omega) (by omega) d1
      -- row `s` outside `T` is the bottom row of `Z_2` alone
      have r1 : ∀ x, 2 * h - d ≤ x → x < 3 * h - d → ¬ T x s := by
        intro x h1 h2 h3
        refine N.dTZ₂ _ _ h3 ?_
        rw [hZ₂, c6, sub_self, N.T_zero]
        omega
      have r2 : ∀ x, 0 ≤ x → x < 2 * h → ¬ T x s → 2 * h - d ≤ x ∧ x < 3 * h - d := by
        intro x h1 h2 h3
        rcases N.cover x s (by omega) (by omega) (by omega) (by omega) with h5 | h5 | h5 | h5 | h5
        · exact absurd h5 h3
        · have := N.W₁_box h5; omega
        · have := hW₂b _ _ h5; omega
        · have := N.Z₁_box h5; omega
        · rw [hZ₂, c6, sub_self, N.T_zero] at h5
          omega
      -- column `s` holds `T`, `W_1`, `Z_1` only
      have r3 : ∀ x, 0 ≤ x → x < 2 * h → (¬ T x s ↔
          Z₁ s (3 * h - 1 - x)) := by
        intro x h1 h2
        constructor
        · intro h3
          rcases N.cover s (3 * h - 1 - x) (by omega) (by omega) (by omega) (by omega) with
            h5 | h5 | h5 | h5 | h5
          · have := d2 _ h5; omega
          · rw [N.W₁_mem, show 3 * h - 1 - (3 * h - 1 - x) = x by omega] at h5
            exact absurd h5 h3
          · have := hW₂b _ _ h5; omega
          · exact h5
          · have := hZ₂b _ _ h5; omega
        · intro h3 h4
          refine N.dW₁Z₁ s (3 * h - 1 - x) ?_ h3
          rw [N.W₁_mem, show 3 * h - 1 - (3 * h - 1 - x) = x by omega]
          exact h4
      -- the two ends of `[e, e + h)` give cells of `Z_1` in column `s`, so `h <= t = h - u_1`
      have f1 := (r3 (2 * h - d) (by omega) (by omega)).1 (r1 _ le_rfl (by omega))
      have f2 := (r3 (3 * h - d - 1) (by omega) (by omega)).1 (r1 _ (by omega) (by omega))
      rw [← hx, hZcol, hTop] at f1 f2
      omega

end NF38


/-! ## Proposition 38: the setting and Steps 1 and 2 -/

/-- Membership in a vertical tile, with the two indices given by their values. -/
theorem mem_V_of {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell} {i₀ : Fin k}
    {κ : Fin k → GridIso} (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true)
    {X Y x j : ℤ} (hx : x = if (κ i).negY then (κ i).boxY a + a - 1 - Y else Y - (κ i).boxY a)
    (hj : j = if (κ i).negX then (κ i).boxX d + d - 1 - X else X - (κ i).boxX d) :
    (X, Y) ∈ t i ↔ (x, j) ∈ t i₀ := by
  rw [mem_V F hi, hx, hj]

/-- Four different tiles of five leave one. -/
theorem exists_fifth {p q r s : Fin 5} (h : [p, q, r, s].Nodup) :
    ∃ z, (z ≠ p ∧ z ≠ q ∧ z ≠ r ∧ z ≠ s) ∧ ∀ i, i = p ∨ i = q ∨ i = r ∨ i = s ∨ i = z := by
  have h1 : [p, q, r, s].toFinset.card = 4 := by
    rw [List.toFinset_card_of_nodup h]
    rfl
  have h2 : ([p, q, r, s].toFinsetᶜ).card = 1 := by
    rw [Finset.card_compl, h1]
    rfl
  obtain ⟨z, hz⟩ := Finset.card_eq_one.1 h2
  have h3 : ∀ i, i ∉ [p, q, r, s].toFinset ↔ i = z := by
    intro i
    rw [← Finset.mem_compl, hz, Finset.mem_singleton]
  simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false, not_or] at h3
  refine ⟨z, (h3 z).2 rfl, fun i => ?_⟩
  by_cases hi : i = p ∨ i = q ∨ i = r ∨ i = s
  · tauto
  · push Not at hi
    have := (h3 i).1 hi
    tauto

/-- The setting of Proposition 38. Source: `report-4.md`, Proposition 38 (line 282):
"Let W_1, W_2 be the top tiles with x = 0 and x = a - d, Z_1, Z_2 the non-top
tiles." -/
structure Setting38 (a b d : ℤ) (t : Fin 5 → Finset Cell) (i₀ : Fin 5) (κ : Fin 5 → GridIso)
    (w₁ w₂ z₁ z₂ : Fin 5) : Prop where
  /-- The tiling is of type H1. -/
  h1 : TypeH1 a b d t i₀ κ
  /-- `d < a`. -/
  hda : d < a
  /-- `h <= d`. -/
  hh : b - a ≤ d
  /-- The five tiles. -/
  nodup : [i₀, w₁, w₂, z₁, z₂].Nodup
  /-- There are no others. -/
  all : ∀ i, i = i₀ ∨ i = w₁ ∨ i = w₂ ∨ i = z₁ ∨ i = z₂
  /-- `W_1` has `x = 0`. -/
  w₁X : (κ w₁).boxX d = 0
  /-- `W_1` is a top tile. -/
  w₁Y : (κ w₁).boxY a = b - a
  /-- `W_2` has `x = a - d`. -/
  w₂X : (κ w₂).boxX d = a - d
  /-- `W_2` is a top tile. -/
  w₂Y : (κ w₂).boxY a = b - a
  /-- `Z_1` is not a top tile. -/
  z₁Y : (κ z₁).boxY a < b - a
  /-- `Z_2` is not a top tile. -/
  z₂Y : (κ z₂).boxY a < b - a

namespace Setting38

variable {a b d : ℤ} {t : Fin 5 → Finset Cell} {i₀ : Fin 5} {κ : Fin 5 → GridIso}
  {w₁ w₂ z₁ z₂ : Fin 5}

/-- `W_1` is not `T`. -/
theorem w₁ne (S : Setting38 a b d t i₀ κ w₁ w₂ z₁ z₂) : w₁ ≠ i₀ := by
  have := S.nodup
  simp at this
  tauto

/-- `W_2` is not `T`. -/
theorem w₂ne (S : Setting38 a b d t i₀ κ w₁ w₂ z₁ z₂) : w₂ ≠ i₀ := by
  have := S.nodup
  simp at this
  tauto

/-- `Z_1` is not `T`. -/
theorem z₁ne (S : Setting38 a b d t i₀ κ w₁ w₂ z₁ z₂) : z₁ ≠ i₀ := by
  have := S.nodup
  simp at this
  tauto

/-- `Z_2` is not `T`. -/
theorem z₂ne (S : Setting38 a b d t i₀ κ w₁ w₂ z₁ z₂) : z₂ ≠ i₀ := by
  have := S.nodup
  simp at this
  tauto

/-- Two different tiles of the five share no cell. -/
theorem apart {i j : Fin 5} (S : Setting38 a b d t i₀ κ w₁ w₂ z₁ z₂) (hij : i ≠ j) (x y : ℤ)
    (hi : (x, y) ∈ t i) (hj : (x, y) ∈ t j) : False :=
  hij (uniq S.h1.frame hi hj)

/-- Every cell of `R a b` is in one of the five tiles. -/
theorem cases5 (S : Setting38 a b d t i₀ κ w₁ w₂ z₁ z₂) (x y : ℤ) (h1 : 0 ≤ x) (h2 : x < a)
    (h3 : 0 ≤ y) (h4 : y < b) :
    (x, y) ∈ t i₀ ∨ (x, y) ∈ t w₁ ∨ (x, y) ∈ t w₂ ∨ (x, y) ∈ t z₁ ∨ (x, y) ∈ t z₂ := by
  obtain ⟨i, hi⟩ := cover S.h1.frame h1 h2 h3 h4
  rcases S.all i with rfl | rfl | rfl | rfl | rfl <;> tauto

/-- Row `b - 1` belongs to the two top tiles. -/
theorem top_row (S : Setting38 a b d t i₀ κ w₁ w₂ z₁ z₂) (x : ℤ) (h1 : 0 ≤ x) (h2 : x < a) :
    (x, b - 1) ∈ t w₁ ∨ (x, b - 1) ∈ t w₂ := by
  have hB := S.h1.bounds (by norm_num)
  rcases S.cases5 x (b - 1) h1 h2 (by omega) (by omega) with h | h | h | h | h
  · have := box_T S.h1.frame h
    omega
  · exact Or.inl h
  · exact Or.inr h
  · have := box_V S.h1.frame (S.h1.vert _ S.z₁ne) h
    have := S.z₁Y
    omega
  · have := box_V S.h1.frame (S.h1.vert _ S.z₂ne) h
    have := S.z₂Y
    omega

/-- Proposition 38, Step 1 (both top tiles outer). Source: `report-4.md` (line 284):
"So u_0 + u_1 <= a - s. Then l_1, l_2 are not u_0 and u_1 in some order: both are
the same u_E = a / 2". -/
theorem step1 (S : Setting38 a b d t i₀ κ w₁ w₂ z₁ z₂) {s : ℤ} (hs : FullRows (t i₀) a s)
    (hs1 : 1 ≤ s) (hw₁ : (κ w₁).negX = false) (hw₂ : (κ w₂).negX = true) :
    colCount (t i₀) 0 + colCount (t i₀) (a - 1) ≤ a - s ∧
      (((κ w₁).negY = true ∧ (κ w₂).negY = true ∧ 2 * colCount (t i₀) 0 = a) ∨
        ((κ w₁).negY = false ∧ (κ w₂).negY = false ∧ 2 * colCount (t i₀) (a - 1) = a)) := by
  have F := S.h1.frame
  have hda := S.hda
  have hh := S.hh
  have hB := S.h1.bounds (by norm_num)
  have vw₁ := S.h1.vert _ S.w₁ne
  have vw₂ := S.h1.vert _ S.w₂ne
  have vz₁ := S.h1.vert _ S.z₁ne
  have vz₂ := S.h1.vert _ S.z₂ne
  have eX₁ := S.w₁X
  have eY₁ := S.w₁Y
  have eX₂ := S.w₂X
  have eY₂ := S.w₂Y
  have bz₁ := bounds_V F vz₁
  have bz₂ := bounds_V F vz₂
  have cz₁ := S.z₁Y
  have cz₂ := S.z₂Y
  have hc0 := col_zero S.h1 (by norm_num)
  have hc1 := col_last S.h1 (by norm_num)
  have p0 := (hc0 0).1 (F.row0 0 le_rfl (by omega))
  have p1 := (hc1 0).1 (F.row0 (a - 1) (by omega) (by omega))
  have q0 := box_T F ((hc0 (colCount (t i₀) 0 - 1)).2 ⟨by omega, by omega⟩)
  have q1 := box_T F ((hc1 (colCount (t i₀) (a - 1) - 1)).2 ⟨by omega, by omega⟩)
  generalize colCount (t i₀) 0 = u at *
  generalize colCount (t i₀) (a - 1) = u' at *
  -- rows `b - 1` and `h` of the two top tiles
  have T₁ : ∀ X, (X, b - 1) ∈ t w₁ ↔ 0 ≤ X ∧ X < (if (κ w₁).negY then u else u') := by
    intro X
    rw [mem_V_of F vw₁ (x := if (κ w₁).negY then 0 else a - 1) (j := X)
      (by rw [eY₁]; split <;> omega) (by rw [hw₁, eX₁]; simp)]
    cases (κ w₁).negY
    · exact hc1 X
    · exact hc0 X
  have B₁ : ∀ X, (X, b - a) ∈ t w₁ ↔ 0 ≤ X ∧ X < (if (κ w₁).negY then u' else u) := by
    intro X
    rw [mem_V_of F vw₁ (x := if (κ w₁).negY then a - 1 else 0) (j := X)
      (by rw [eY₁]; split <;> omega) (by rw [hw₁, eX₁]; simp)]
    cases (κ w₁).negY
    · exact hc0 X
    · exact hc1 X
  have T₂ : ∀ X, (X, b - 1) ∈ t w₂ ↔
      0 ≤ a - 1 - X ∧ a - 1 - X < (if (κ w₂).negY then u else u') := by
    intro X
    rw [mem_V_of F vw₂ (x := if (κ w₂).negY then 0 else a - 1) (j := a - 1 - X)
      (by rw [eY₂]; split <;> omega) (by rw [hw₂, eX₂]; simp)]
    cases (κ w₂).negY
    · exact hc1 _
    · exact hc0 _
  have B₂ : ∀ X, (X, b - a) ∈ t w₂ ↔
      0 ≤ a - 1 - X ∧ a - 1 - X < (if (κ w₂).negY then u' else u) := by
    intro X
    rw [mem_V_of F vw₂ (x := if (κ w₂).negY then a - 1 else 0) (j := a - 1 - X)
      (by rw [eY₂]; split <;> omega) (by rw [hw₂, eX₂]; simp)]
    cases (κ w₂).negY
    · exact hc0 _
    · exact hc1 _
  -- distinctness
  have hnd := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true,
    List.nodup_nil, and_true] at hnd
  obtain ⟨-, ⟨nw, nw₁z₁, nw₁z₂⟩, ⟨nw₂z₁, nw₂z₂⟩, nz⟩ := hnd
  -- row `b - 1`: `l_1 + l_2 = a`
  have hl : (if (κ w₁).negY then u else u') + (if (κ w₂).negY then u else u') = a := by
    have l1 : 1 ≤ (if (κ w₁).negY then u else u') ∧ (if (κ w₁).negY then u else u') < a := by
      split <;> omega
    generalize (if (κ w₁).negY then u else u') = l₁ at *
    generalize (if (κ w₂).negY then u else u') = l₂ at *
    have e1 : a - 1 - l₁ < l₂ := by
      rcases S.top_row l₁ (by omega) (by omega) with h | h
      · have := (T₁ _).1 h
        omega
      · exact ((T₂ _).1 h).2
    have e2 : ¬ a - 1 - (l₁ - 1) < l₂ := by
      intro h
      exact S.apart nw _ _ ((T₁ (l₁ - 1)).2 ⟨by omega, by omega⟩)
        ((T₂ (l₁ - 1)).2 ⟨by omega, h⟩)
    omega
  -- row `h`: `m_1 + m_2 + 2 s <= a`
  have hm : (if (κ w₁).negY then u' else u) + (if (κ w₂).negY then u' else u) + 2 * s ≤ a := by
    obtain ⟨p, -, hp⟩ := thick_V F hs vz₁
    obtain ⟨q, -, hq⟩ := thick_V F hs vz₂
    have hp' : ∀ X, p ≤ X → X < p + s → (X, b - a) ∈ t z₁ := fun X h1 h2 =>
      hp X (b - a) h1 h2 (by omega) (by omega)
    have hq' : ∀ X, q ≤ X → X < q + s → (X, b - a) ∈ t z₂ := fun X h1 h2 =>
      hq X (b - a) h1 h2 (by omega) (by omega)
    generalize (if (κ w₁).negY then u' else u) = m₁ at *
    generalize (if (κ w₂).negY then u' else u) = m₂ at *
    have r1 := box_V F vz₁ (hp' p le_rfl (by omega))
    have r2 := box_V F vz₁ (hp' (p + s - 1) (by omega) (by omega))
    have r3 := box_V F vz₂ (hq' q le_rfl (by omega))
    have r4 := box_V F vz₂ (hq' (q + s - 1) (by omega) (by omega))
    have f1 : m₁ ≤ p := by
      by_contra h
      exact S.apart nw₁z₁ _ _ ((B₁ p).2 ⟨by omega, by omega⟩) (hp' p le_rfl (by omega))
    have f2 : m₁ ≤ q := by
      by_contra h
      exact S.apart nw₁z₂ _ _ ((B₁ q).2 ⟨by omega, by omega⟩) (hq' q le_rfl (by omega))
    have f3 : p + s ≤ a - m₂ := by
      by_contra h
      exact S.apart nw₂z₁ _ _ ((B₂ (p + s - 1)).2 ⟨by omega, by omega⟩)
        (hp' _ (by omega) (by omega))
    have f4 : q + s ≤ a - m₂ := by
      by_contra h
      exact S.apart nw₂z₂ _ _ ((B₂ (q + s - 1)).2 ⟨by omega, by omega⟩)
        (hq' _ (by omega) (by omega))
    have f5 : p + s ≤ q ∨ q + s ≤ p := by
      by_contra h
      push Not at h
      rcases le_total p q with hpq | hpq
      · exact S.apart nz _ _ (hp' q (by omega) (by omega)) (hq' q le_rfl (by omega))
      · exact S.apart nz _ _ (hp' p le_rfl (by omega)) (hq' p (by omega) (by omega))
    omega
  cases h₁ : (κ w₁).negY <;> cases h₂ : (κ w₂).negY <;> rw [h₁, h₂] at hl hm <;>
    simp at hl hm ⊢ <;> omega

/-- The normal form in which Steps 3 and 4 work. Source: `report-4.md` (line 288):
"So in every case a = 2h, b = 3h, u_0 = h, W_1 has spine column 0 and box
[0, d) x [h, 3h), no other tile has x_i = 0, and W_1 reverses the order." -/
theorem nf (S : Setting38 a b d t i₀ κ w₁ w₂ z₁ z₂) {s : ℤ} (hs : FullRows (t i₀) a s)
    (hs1 : 1 ≤ s) (ha : a = 2 * (b - a)) (hu0 : colCount (t i₀) 0 = b - a)
    (hu1 : colCount (t i₀) (a - 1) < b - a) (hw₁ : (κ w₁).negX = false)
    (hw₁' : (κ w₁).negY = true) (hzl : (κ z₁).boxX d ≠ 0) (hzr : (κ z₁).boxX d ≠ a - d) :
    NF38 d (b - a) s (colCount (t i₀) (a - 1)) ((κ z₁).boxX d) ((κ z₁).boxY a) ((κ z₂).boxY a)
      (κ z₁).negX (κ z₁).negY (fun x y => (x, y) ∈ t i₀) (fun x y => (x, y) ∈ t w₁)
      (fun x y => (x, y) ∈ t w₂) (fun x y => (x, y) ∈ t z₁) (fun x y => (x, y) ∈ t z₂) := by
  have F := S.h1.frame
  have hda := S.hda
  have hh := S.hh
  have hB := S.h1.bounds (by norm_num)
  have bz₁ := bounds_V F (S.h1.vert _ S.z₁ne)
  have hlow := S.h1.lemma30a (by norm_num) hs
  have hnd := S.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨n1, n2, n3, n4⟩, ⟨nw, nw₁z₁, nw₁z₂⟩, ⟨nw₂z₁, nw₂z₂⟩, nz⟩ := hnd
  have l₁ := hlow.1 _ S.z₁ne
  have l₂ := hlow.1 _ S.z₂ne
  exact
    { h_le := hh
      d_lt := by omega
      s_pos := hs1
      T_box := fun x y h => by
        have := box_T F h
        omega
      T_full := fun x y h1 h2 h3 h4 => full_row hs h1 (by omega) h3 h4
      T_zero := fun y => by
        rw [← hu0]
        exact col_zero S.h1 (by norm_num) y
      T_rows := fun y h1 h2 => F.exists_in_row h1 h2
      u₁_pos := by
        have := (col_last S.h1 (by norm_num) 0).1 (F.row0 (a - 1) (by omega) (by omega))
        omega
      u₁_lt := hu1
      cover := fun x y h1 h2 h3 h4 => S.cases5 x y h1 (by omega) h3 (by omega)
      dTW₁ := S.apart n1
      dTW₂ := S.apart n2
      dTZ₁ := S.apart n3
      dTZ₂ := S.apart n4
      dW₁W₂ := S.apart nw
      dW₁Z₁ := S.apart nw₁z₁
      dW₁Z₂ := S.apart nw₁z₂
      dW₂Z₁ := S.apart nw₂z₁
      dW₂Z₂ := S.apart nw₂z₂
      dZ₁Z₂ := S.apart nz
      W₁_mem := fun X Y => mem_V_of F (S.h1.vert _ S.w₁ne) (by rw [hw₁', S.w₁Y]; simp; omega)
        (by rw [hw₁, S.w₁X]; simp)
      Z₁_mem := fun X Y => mem_V_of F (S.h1.vert _ S.z₁ne) (by split <;> omega) rfl
      x₁_pos := by omega
      x₁_lt := by omega
      s_le_y₁ := l₁
      y₁_lt := S.z₁Y
      s_le_y₂ := l₂
      y₂_lt := S.z₂Y
      low := by
        obtain ⟨i, hi, hiY⟩ := hlow.2.2
        have c₁ := S.z₁Y
        have e₁ := S.w₁Y
        have e₂ := S.w₂Y
        rcases S.all i with rfl | rfl | rfl | rfl | rfl
        · exact absurd rfl hi
        · omega
        · omega
        · exact Or.inl hiY
        · exact Or.inr hiY }

end Setting38

/-- The two top tiles and the non-top tiles of Proposition 38, with a given non-top
tile as `Z_2`. -/
theorem exists_setting38 {a b d : ℤ} {t : Fin 5 → Finset Cell} {i₀ : Fin 5}
    {κ : Fin 5 → GridIso} (H : TypeH1 a b d t i₀ κ) (hda : d < a) (hh : b - a ≤ d)
    (hcard : (topTiles b t i₀).card = 2) {w₁ z₂ : Fin 5} (hw₁ : w₁ ≠ i₀)
    (hw₁Y : (κ w₁).boxY a = b - a) (hw₁X : (κ w₁).boxX d = 0) (hz₂ : z₂ ≠ i₀)
    (hz₂Y : (κ z₂).boxY a < b - a) :
    ∃ w₂ z₁, Setting38 a b d t i₀ κ w₁ w₂ z₁ z₂ ∧ (a - 1, b - 1) ∈ t w₂ := by
  have F := H.frame
  have hB := H.bounds (by norm_num)
  -- the tile on the corner `(a - 1, b - 1)`
  obtain ⟨w₂, hw₂c⟩ := cover F (x := a - 1) (y := b - 1) (by omega) (by omega) (by omega) (by omega)
  have hw₂ : w₂ ≠ i₀ := by
    rintro rfl
    have := box_T F hw₂c
    omega
  have bw₂ := bounds_V F (H.vert w₂ hw₂)
  have cw₂ := box_V F (H.vert w₂ hw₂) hw₂c
  have hw₂X : (κ w₂).boxX d = a - d := by omega
  have hw₂Y : (κ w₂).boxY a = b - a := by omega
  have hww : w₁ ≠ w₂ := by
    rintro rfl
    omega
  have hw₁z₂ : w₁ ≠ z₂ := by
    rintro rfl
    omega
  have hw₂z₂ : w₂ ≠ z₂ := by
    rintro rfl
    omega
  have hnd : [i₀, w₁, w₂, z₂].Nodup := by
    simp [hw₁.symm, hw₂.symm, hz₂.symm, hww, hw₁z₂, hw₂z₂]
  obtain ⟨z₁, ⟨e1, e2, e3, e4⟩, hall⟩ := exists_fifth hnd
  have hz₁Y : (κ z₁).boxY a < b - a := by
    have b₁ := bounds_V F (H.vert z₁ e1)
    by_contra hc
    have htop : ({w₁, w₂, z₁} : Finset (Fin 5)) ⊆ topTiles b t i₀ := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact (mem_topTiles H (by norm_num) hw₁).2 hw₁Y
      · exact (mem_topTiles H (by norm_num) hw₂).2 hw₂Y
      · exact (mem_topTiles H (by norm_num) e1).2 (by omega)
    have h3 : ({w₁, w₂, z₁} : Finset (Fin 5)).card = 3 :=
      Finset.card_eq_three.2 ⟨w₁, w₂, z₁, hww, e2.symm, e3.symm, rfl⟩
    have := Finset.card_le_card htop
    omega
  refine ⟨w₂, z₁, ⟨H, hda, hh, ?_, fun i => ?_, hw₁X, hw₁Y, hw₂X, hw₂Y, hz₁Y, hz₂Y⟩, hw₂c⟩
  · simp [hw₁.symm, hw₂.symm, hz₂.symm, hww, hw₁z₂, hw₂z₂, e1.symm, e2.symm, e3.symm, e4]
  · have := hall i
    tauto

/-- Proposition 38 with the left wall in state alpha. Source: `report-4.md`, Steps 1
and 2 (lines 284, 286): with alpha' Step 1 is a contradiction, with beta' it gives the
normal form for Step 4, and with gamma' Step 2 gives the normal form for Step 3. -/
theorem proposition38_alpha {a b d : ℤ} {t : Fin 5 → Finset Cell} {i₀ : Fin 5}
    {κ : Fin 5 → GridIso} (H : TypeH1 a b d t i₀ κ) (hda : d < a) (hh : b - a ≤ d)
    (hcard : (topTiles b t i₀).card = 2) (hα : WallAlpha a b d t i₀ κ 0 0 false) : False := by
  have F := H.frame
  have hB := H.bounds (by norm_num)
  obtain ⟨s, hs1, hsd, hs⟩ := F.exists_fullRows
  obtain ⟨w₁, hw₁, hw₁Y, hw₁X, hw₁n, hw₁u, hu0⟩ := hα
  rcases wall_right H (by norm_num) hda hh with ⟨w, hw, hwY, hwX, hwn, hwu, hu1⟩ |
      ⟨w, z, hw, hz, hwY, hzY, hwX, hzX, hwn, hzn, hwu, hu1, hcol⟩ |
      ⟨w, z, hw, hz, hwY, hzY, hwX, hzX, hwn, hzn, hwu, hu1, hcol⟩
  · -- alpha, alpha'
    obtain ⟨z₂, hz₂, hz₂t⟩ := H.proposition28 (by norm_num) hda
    have b₂ := bounds_V F (H.vert z₂ hz₂)
    rw [mem_topTiles H (by norm_num) hz₂] at hz₂t
    obtain ⟨w₂, z₁, S, -⟩ := exists_setting38 H hda hh hcard hw₁ hw₁Y hw₁X hz₂ (by omega)
    have hw₂ : w₂ = w := hwu _ S.w₂ne S.w₂X
    subst hw₂
    have h1 := S.step1 hs hs1 hw₁n hwn
    omega
  · -- alpha, beta'
    obtain ⟨w₂, z₁, S, -⟩ := exists_setting38 H hda hh hcard hw₁ hw₁Y hw₁X hz (by omega)
    have hnd := S.nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      not_false_eq_true, List.nodup_nil, and_true] at hnd
    obtain ⟨⟨n1, n2, n3, n4⟩, ⟨nw, nw₁z₁, nw₁z₂⟩, ⟨nw₂z₁, nw₂z₂⟩, nz⟩ := hnd
    have hw₂ : w₂ = w := by
      rcases hwu _ S.w₂ne S.w₂X with h | h
      · exact h
      · exact absurd h nw₂z₂
    subst hw₂
    obtain ⟨h1, h2⟩ := S.step1 hs hs1 hw₁n hwn
    rcases h2 with ⟨o₁, o₂, h2⟩ | ⟨o₁, o₂, h2⟩
    · have ha : a = 2 * (b - a) := by omega
      have N := S.nf hs hs1 ha hu0 hu1 hw₁n o₁ (fun h => nw₁z₁ (hw₁u _ S.z₁ne h).symm) (fun h => by
        rcases hwu _ S.z₁ne h with h | h
        · exact nw₂z₁ h.symm
        · exact nz h)
      refine N.step4 (m₂ := (κ z).negY) (by omega) ?_ ?_ ?_ ?_
      · intro y
        rw [show 2 * (b - a) - 1 = a - 1 by omega]
        exact col_last H (by norm_num) y
      · intro X Y
        exact mem_V_of F (H.vert _ hw) (by rw [o₂, hwY]; simp; omega)
          (by rw [hwn, hwX]; simp; omega)
      · intro X Y
        exact mem_V_of F (H.vert _ hz) (by split <;> omega) (by rw [hzn, hzX]; simp; omega)
      · intro Y
        rw [show 2 * (b - a) - 1 = a - 1 by omega]
        exact hcol Y
    · omega
  · -- alpha, gamma'
    obtain ⟨w₂, z₁, S, hcorner⟩ := exists_setting38 H hda hh hcard hw₁ hw₁Y hw₁X hz (by omega)
    have hnd := S.nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      not_false_eq_true, List.nodup_nil, and_true] at hnd
    obtain ⟨⟨n1, n2, n3, n4⟩, ⟨nw, nw₁z₁, nw₁z₂⟩, ⟨nw₂z₁, nw₂z₂⟩, nz⟩ := hnd
    have hw₂ : w₂ = w := by
      rcases hwu _ S.w₂ne S.w₂X with h | h
      · exact h
      · exact absurd h nw₂z₂
    subst hw₂
    simp only [Bool.not_true] at hwn
    have hc0 := col_zero H (by norm_num)
    have hc1 := col_last H (by norm_num)
    -- Step 2: `W_2` has `d` cells in row `b - 1`, the image of column 0
    have e1 : ((if (κ w₂).negY then 0 else a - 1), d - 1) ∈ t i₀ := by
      refine (mem_V_of F (H.vert _ hw) ?_ ?_).1 hcorner
      · rw [hwY]
        split <;> omega
      · rw [hwn, hwX]
        simp
    have o₂ : (κ w₂).negY = true := by
      by_contra hn
      rw [Bool.not_eq_true] at hn
      rw [hn] at e1
      have := (hc1 _).1 e1
      omega
    rw [o₂] at e1
    have hhd : b - a = d := by
      have := (hc0 _).1 e1
      omega
    -- `a = 2d`
    have a1 : d ≤ a - d := by
      by_contra hc
      obtain ⟨Y, hY⟩ := col_V F (H.vert _ hw₁) (X := a - d) (by omega) (by omega)
      have hYb := box_V F (H.vert _ hw₁) hY
      have h3 := spine_V F (H.vert _ hw) (Y := Y) (by omega) (by omega)
      rw [shift_eq (κ w₂) d, hwn, hwX] at h3
      exact S.apart nw _ _ hY (by simpa using h3)
    have a2 : a - d ≤ d := by
      by_contra hc
      rcases S.top_row d (by omega) hda with h | h
      · have := box_V F (H.vert _ hw₁) h
        omega
      · have := box_V F (H.vert _ hw) h
        omega
    -- `W_1` reverses the order
    have o₁ : (κ w₁).negY = true := by
      by_contra hn
      rw [Bool.not_eq_true] at hn
      rcases S.top_row (d - 1) (by omega) (by omega) with h | h
      · have h3 : (a - 1, d - 1) ∈ t i₀ := by
          refine (mem_V_of F (H.vert _ hw₁) ?_ ?_).1 h
          · rw [hn, hw₁Y]
            simp
          · rw [hw₁n, hw₁X]
            simp
        have := (hc1 _).1 h3
        omega
      · have := box_V F (H.vert _ hw) h
        omega
    have ha : a = 2 * (b - a) := by omega
    have N := S.nf hs hs1 ha hu0 hu1 hw₁n o₁ (fun h => nw₁z₁ (hw₁u _ S.z₁ne h).symm) (fun h => by
      rcases hwu _ S.z₁ne h with h | h
      · exact nw₂z₁ h.symm
      · exact nz h)
    refine N.step3 (m₂ := (κ z).negY) hhd hzY ?_ ?_ ?_
    · intro X Y
      exact mem_V_of F (H.vert _ hw) (by rw [o₂, hwY]; simp; omega) (by rw [hwn, hwX]; simp; omega)
    · intro X Y
      exact mem_V_of F (H.vert _ hz) (by split <;> omega) (by rw [hzn, hzX]; simp; omega)
    · intro Y
      rw [show 2 * (b - a) - 1 = a - 1 by omega]
      have := hcol Y
      rw [this]
      omega

/-! ## Proposition 38: the other states -/

section Others

variable {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell} {i₀ : Fin k} {κ : Fin k → GridIso}

/-- The top tiles of the mirror image. -/
theorem topTiles_mirror (a b : ℤ) {k : ℕ} (t : Fin k → Finset Cell) (i₀ : Fin k) :
    topTiles b (fun i => (t i).image (GridIso.flipX a).apply) i₀ = topTiles b t i₀ := by
  ext i
  simp only [topTiles, Finset.mem_filter, Finset.mem_univ, true_and]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩
    exact ⟨a - 1 - x, (mem_mirror a _ _ _).1 hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨a - 1 - x, (mem_mirror a _ _ _).2 ?_⟩
    rw [show a - 1 - (a - 1 - x) = x by ring]
    exact hx

/-- The far column of a vertical tile has as many cells as the top row of `T`. -/
theorem far_count (F : Frame a b d t i₀ κ) {i : Fin k} (hi : (κ i).swap = true) :
    colCount (t i) (if (κ i).negX then (κ i).boxX d else (κ i).boxX d + d - 1) =
      rowCount (t i₀) (d - 1) := by
  rw [← F.vertical_colCount hi, shift_eq (κ i) d]
  congr 1
  cases (κ i).negX <;> simp
  ring

/-- In state gamma of a wall the cell `(0, d - 1)` or the cell `(a - 1, d - 1)` is in
`T` (Lemma 36 (e): the top tile has `d` cells in row `b - 1`). -/
theorem gamma_corner (H : TypeH1 a b d t i₀ κ)
    (h : WallGamma a b d t i₀ κ 0 0 false ∨ WallGamma a b d t i₀ κ (a - d) (a - 1) true) :
    (0, d - 1) ∈ t i₀ ∨ (a - 1, d - 1) ∈ t i₀ := by
  have key : ∀ w, w ≠ i₀ → (κ w).boxY a = b - a →
      ∀ X, (X, b - 1) ∈ t w → d - 1 = (if (κ w).negX then (κ w).boxX d + d - 1 - X
        else X - (κ w).boxX d) → (0, d - 1) ∈ t i₀ ∨ (a - 1, d - 1) ∈ t i₀ := by
    intro w hw hwY X hX hj
    have h1 := (mem_V_of H.frame (H.vert w hw)
      (x := if (κ w).negY then 0 else a - 1) (by rw [hwY]; split <;> omega) hj).1 hX
    cases hn : (κ w).negY <;> rw [hn] at h1
    · exact Or.inr h1
    · exact Or.inl h1
  rcases h with ⟨w, z, hw, hz, hwY, hzY, hwX, hzX, hwn, hzn, hwu, hu, hcol⟩ |
      ⟨w, z, hw, hz, hwY, hzY, hwX, hzX, hwn, hzn, hwu, hu, hcol⟩
  · have hb := bounds_V H.frame (H.vert z hz)
    refine key w hw hwY 0 ((hcol _).2 ⟨by omega, by omega⟩) ?_
    rw [hwn, hwX]
    simp
  · have hb := bounds_V H.frame (H.vert z hz)
    refine key w hw hwY (a - 1) ((hcol _).2 ⟨by omega, by omega⟩) ?_
    rw [hwn, hwX]
    simp

end Others

/-! ## Proposition 37: two lemmas -/

/-- A family of three tiles has two tiles of the same type. -/
theorem three_types {k : ℕ} (κ : Fin k → GridIso) {J : Finset (Fin k)} (hJ : J.card = 3) :
    ∃ p q r, p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ J = {p, q, r} ∧ (κ p).negX = (κ q).negX := by
  obtain ⟨p, q, r, h1, h2, h3, h⟩ := Finset.card_eq_three.1 hJ
  by_cases e1 : (κ p).negX = (κ q).negX
  · exact ⟨p, q, r, h1, h2, h3, h, e1⟩
  · by_cases e2 : (κ p).negX = (κ r).negX
    · refine ⟨p, r, q, h2, h1, h3.symm, ?_, e2⟩
      rw [h]
      ext i
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    · refine ⟨q, r, p, h3, h1.symm, h2.symm, ?_, ?_⟩
      · rw [h]
        ext i
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      · cases h4 : (κ p).negX <;> cases h5 : (κ q).negX <;> cases h6 : (κ r).negX <;>
          simp_all

/-- Three top tiles: a block of the top row holds one tile, and there are at least two
blocks. Source: `report-4.md`, Proposition 37 (line 276): "With three top tiles a
block of Lemma 25 holds one tile, there are at least two blocks". -/
theorem one_tile_block {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell} {i₀ : Fin k}
    {κ : Fin k → GridIso} (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k)
    (hcard : (topTiles b t i₀).card = 3) :
    2 * d ≤ a ∧ ((∀ y : ℤ, 0 ≤ y → y < d → (0, y) ∈ t i₀) ∨
      (∀ y : ℤ, 0 ≤ y → y < d → (a - 1, y) ∈ t i₀)) := by
  have F := H.frame
  have hB := H.bounds hk
  have hJ : ∀ i ∈ topTiles b t i₀, (κ i).swap = true := fun i hi =>
    H.vert i (ne_of_top hi)
  have hsep := (H.lemma25a hk).2.2
  obtain ⟨p, q, r, hpq, hpr, hqr, hset, hneg⟩ := three_types κ hcard
  have hp : p ∈ topTiles b t i₀ := by rw [hset]; simp
  have hq : q ∈ topTiles b t i₀ := by rw [hset]; simp
  have hmem : ∀ i, i ∈ topTiles b t i₀ → i = p ∨ i = q ∨ i = r := by
    intro i hi
    rw [hset] at hi
    simpa using hi
  obtain ⟨e₁, e₁', c₁, l₁, l₁', -⟩ := F.column_blocks _ hJ hsep p hp
  obtain ⟨e₂, e₂', c₂, l₂, l₂', -⟩ := F.column_blocks _ hJ hsep q hq
  have bp := bounds_V F (hJ p hp)
  have bq := bounds_V F (hJ q hq)
  -- the two blocks are different, so they have no column in common
  have hdis : e₁' ≤ e₂ ∨ e₂' ≤ e₁ := by
    by_contra hc
    have hee : e₁ = e₂ := by
      have h1 := c₁.2.2.2 e₂ c₂.1
      have h2 := c₂.2.2.2 e₁ c₁.1
      omega
    subst hee
    exact hpq (F.column_blocks_unique _ hJ hsep c₁ hp hq ⟨l₁, l₁'⟩
      ⟨l₂, by
        have h1 := c₁.2.2.1
        have h2 := c₂.2.2.1
        have h3 := c₂.2.2.2 e₁' c₁.2.1
        have h4 := c₁.2.2.2 e₂' c₂.2.1
        omega⟩ hneg)
  refine ⟨by omega, ?_⟩
  by_cases hr : e₁ ≤ (κ r).boxX d ∧ (κ r).boxX d + d ≤ e₁'
  · refine (H.lemma25c hk c₂ hq (fun i hi hie => ?_)).2.2
    rcases hmem i hi with rfl | rfl | rfl
    · omega
    · rfl
    · omega
  · refine (H.lemma25c hk c₁ hp (fun i hi hie => ?_)).2.2
    rcases hmem i hi with rfl | rfl | rfl
    · rfl
    · omega
    · exact absurd hie hr

/-- Proposition 37 when column 0 of `T` is full. Source: `report-4.md`, Proposition 37
(line 276). In place of the count of full rows at the end: a row `r >= d` that is full
in `Z` comes from a column of `T` outside the window, and the row `r` of the top tile
`W'` from a column inside it; two such rows are `d` apart, while the window has `d`
columns. -/
theorem proposition37_full {a b d : ℤ} {t : Fin 5 → Finset Cell} {i₀ : Fin 5}
    {κ : Fin 5 → GridIso} (H : TypeH1 a b d t i₀ κ) (hda : d < a) (hh : b - a ≤ d)
    (hcard : (topTiles b t i₀).card = 3) (ha : 2 * d ≤ a)
    (hfull : ∀ y : ℤ, 0 ≤ y → y < d → (0, y) ∈ t i₀) : False := by
  have F := H.frame
  have hB := H.bounds (by norm_num)
  obtain ⟨s, hs1, hsd, hs⟩ := F.exists_fullRows
  have hlow := H.lemma30a (by norm_num) hs
  -- `h = d`, and the left wall is in state alpha
  have hu0 : d - 1 < colCount (t i₀) 0 :=
    ((col_zero H (by norm_num) _).1 (hfull (d - 1) (by omega) (by omega))).2
  have hle := col_le H (by norm_num) hda hh
  have hd : b - a = d := by omega
  -- the fourth vertical tile
  obtain ⟨z, hz, hzt⟩ := H.proposition28 (by norm_num) hda
  have bz := bounds_V F (H.vert z hz)
  have hzY : (κ z).boxY a < b - a := by
    rw [mem_topTiles H (by norm_num) hz] at hzt
    omega
  have hothers : ∀ i, i ≠ i₀ → i ≠ z → (κ i).boxY a = b - a := by
    intro i hi hiz
    have hsub : topTiles b t i₀ ⊆ ({i₀, z} : Finset (Fin 5))ᶜ := by
      intro j hj
      rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl)
      · exact ne_of_top hj rfl
      · exact hzt hj
    have hc : (({i₀, z} : Finset (Fin 5))ᶜ).card = 3 := by
      rw [Finset.card_compl, Finset.card_pair hz.symm]
      rfl
    have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
    rw [← mem_topTiles H (by norm_num) hi, heq]
    simp [hi, hiz]
  have hzs : (κ z).boxY a = s := by
    obtain ⟨i, hi, hiY⟩ := hlow.2.2
    by_cases hiz : i = z
    · rw [← hiz]
      exact hiY
    · have := hothers i hi hiz
      omega
  have hzX0 : (κ z).boxX d ≠ 0 := by
    rcases wall_left H (by norm_num) hda hh with ⟨w, hw, hwY, hwX, hwn, hwu, -⟩ |
        ⟨w, w', h⟩ | ⟨w, w', h⟩
    · intro h0
      have := hwu z hz h0
      rw [this] at hzY
      omega
    · have := h.2.2.2.2.2.2.2.2.2.1
      omega
    · have := h.2.2.2.2.2.2.2.2.2.1
      omega
  -- `T` is full outside the window `[x_Z, x_Z + d)`
  have hwin : ∀ x y, 0 ≤ x → x < a → 0 ≤ y → y < d →
      (x < (κ z).boxX d ∨ (κ z).boxX d + d ≤ x) → (x, y) ∈ t i₀ := by
    intro x y h1 h2 h3 h4 h5
    obtain ⟨i, hi⟩ := cover F h1 h2 h3 (by omega : y < b)
    by_cases hi0 : i = i₀
    · rw [← hi0]
      exact hi
    · have hb := box_V F (H.vert i hi0) hi
      by_cases hiz : i = z
      · subst hiz
        omega
      · have := hothers i hi0 hiz
        omega
  -- the right wall is in state alpha'
  have hright : (κ z).boxX d ≠ a - d ∧ colCount (t i₀) (a - 1) = b - a := by
    rcases wall_right H (by norm_num) hda hh with ⟨w, hw, hwY, hwX, hwn, hwu, hu1⟩ |
        ⟨w, z', hw, hz', hwY, hzY', hwX, hzX', hwn, hzn', hwu, hu1, hcol⟩ |
        ⟨w, z', hw, hz', hwY, hzY', hwX, hzX', hwn, hzn', hwu, hu1, hcol⟩
    · refine ⟨fun h0 => ?_, hu1⟩
      have := hwu z hz h0
      rw [this] at hzY
      omega
    · -- beta'
      exfalso
      have hz'z : z' = z := by
        by_contra hne
        have := hothers z' hz' hne
        omega
      subst hz'z
      have hu1' : 1 ≤ colCount (t i₀) (a - 1) := by
        have := (col_last H (by norm_num) 0).1 (F.row0 (a - 1) (by omega) (by omega))
        omega
      have hfar : ∀ x, (a - 1, if (κ z').negY then (κ z').boxY a + a - 1 - x
          else x + (κ z').boxY a) ∈ t z' ↔ (x, d - 1) ∈ t i₀ := fun x =>
        mem_V_of F (H.vert _ hz') (by split <;> omega) (by rw [hzn', hzX']; simp)
      have f1 := (hcol _).1 ((hfar 0).2
        (hwin 0 (d - 1) le_rfl (by omega) (by omega) (by omega) (by omega)))
      have f2 := (hcol _).1 ((hfar (a - d - 1)).2
        (hwin (a - d - 1) (d - 1) (by omega) (by omega) (by omega) (by omega) (by omega)))
      cases hn : (κ z').negY <;> rw [hn] at f1 f2 <;> simp at f1 f2 <;> omega
    · -- gamma'
      exfalso
      have hz'z : z' = z := by
        by_contra hne
        have := hothers z' hz' hne
        omega
      subst hz'z
      have hu1' : 1 ≤ colCount (t i₀) (a - 1) := by
        have := (col_last H (by norm_num) 0).1 (F.row0 (a - 1) (by omega) (by omega))
        omega
      have hfar : ∀ x, (a - 1, if (κ w).negY then (κ w).boxY a + a - 1 - x
          else x + (κ w).boxY a) ∈ t w ↔ (x, d - 1) ∈ t i₀ := fun x =>
        mem_V_of F (H.vert _ hw) (by split <;> omega) (by rw [hwn, hwX]; simp)
      have f1 := (hcol _).1 ((hfar 0).2
        (hwin 0 (d - 1) le_rfl (by omega) (by omega) (by omega) (by omega)))
      have f2 := (hcol _).1 ((hfar (a - d - 1)).2
        (hwin (a - d - 1) (d - 1) (by omega) (by omega) (by omega) (by omega) (by omega)))
      cases hn : (κ w).negY <;> rw [hn] at f1 f2 <;> simp at f1 f2 <;> omega
  obtain ⟨hzXr, hu1⟩ := hright
  -- `a = 3d`: every top tile has `d` cells in row `b - 1`
  have ha3 : a = 3 * d := by
    have hsum := sum_rowCount_of_cover t F.disjoint F.cover (by omega) (y := b - 1) (by omega)
      (by omega)
    have hrow : ∀ i, rowCount (t i) (b - 1) = if i ∈ topTiles b t i₀ then d else 0 := by
      intro i
      split
      · rename_i hi
        have hi0 := ne_of_top hi
        have hiY := (mem_topTiles H (by norm_num) hi0).1 hi
        have hv := F.vertical_rowCount (H.vert i hi0) (if (κ i).negY then 0 else a - 1)
        have e1 : (if (κ i).negY then -(if (κ i).negY then 0 else a - 1)
            else (if (κ i).negY then 0 else a - 1)) + (κ i).shift.2 = b - 1 := by
          unfold GridIso.boxY at hiY
          cases hn : (κ i).negY <;> rw [hn] at hiY <;> simp at hiY ⊢ <;> omega
        rw [e1] at hv
        rw [hv]
        split <;> omega
      · rename_i hi
        unfold rowCount
        rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro ⟨x, y⟩ hc hy
        simp only at hy
        rw [hy] at hc
        by_cases hi0 : i = i₀
        · rw [hi0] at hc
          have := box_T F hc
          omega
        · exact hi (top_of_cell hi0 hc)
    rw [Finset.sum_congr rfl (fun i _ => hrow i), Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, hcard] at hsum
    simp at hsum
    omega
  -- a top tile whose box meets the window
  obtain ⟨w, hw⟩ := cover F (x := (κ z).boxX d) (y := b - 1) (by omega) (by omega) (by omega)
    (by omega)
  have hw0 : w ≠ i₀ := by
    rintro rfl
    have := box_T F hw
    omega
  have hwz : w ≠ z := by
    rintro rfl
    have := box_V F (H.vert w hw0) hw
    omega
  have bw := box_V F (H.vert w hw0) hw
  have hwY := hothers w hw0 hwz
  -- a full row of `Z` in the rows of `w` is not a full row of `w`
  have hkey : ∀ r, d ≤ r → r < s + a →
      (let x := if (κ z).negY then s + a - 1 - r else r - s
       x < (κ z).boxX d ∨ (κ z).boxX d + d ≤ x) →
      let x' := if (κ w).negY then d + a - 1 - r else r - d
      (κ z).boxX d ≤ x' ∧ x' < (κ z).boxX d + d := by
    intro r h1 h2 hx
    have hZ : ((κ z).boxX d, r) ∈ t z := by
      rw [mem_V_of F (H.vert z hz) (x := if (κ z).negY then s + a - 1 - r else r - s)
        (j := if (κ z).negX then (κ z).boxX d + d - 1 - (κ z).boxX d
          else (κ z).boxX d - (κ z).boxX d) (by rw [hzs]) rfl]
      refine hwin _ _ ?_ ?_ ?_ ?_ hx <;> split <;> omega
    by_contra hc
    refine hwz (uniq F ?_ hZ)
    rw [mem_V_of F (H.vert w hw0) (x := if (κ w).negY then d + a - 1 - r else r - d)
      (by rw [hwY]; split <;> omega) rfl]
    refine hwin _ _ ?_ ?_ ?_ ?_ ?_
    · split <;> omega
    · split <;> omega
    · split <;> omega
    · split <;> omega
    · simp only [not_and_or, not_le, not_lt] at hc
      exact hc
  -- two such rows are `d` apart
  have k1 := hkey (s + a - 1) (by omega) (by omega)
  have k2 := hkey d (by omega) (by omega)
  have k3 := hkey ((if (κ z).negY then s + a - (κ z).boxX d - d else s + (κ z).boxX d) + d)
    (by split <;> omega) (by split <;> omega)
  cases hn : (κ z).negY <;> cases hm : (κ w).negY <;> rw [hn, hm] at k1 k2 k3 <;>
    simp at k1 k2 k3 <;> omega

end CaseII2

open CaseII2

/-! ## Section 5c: `b - a <= d` -/

/-- Lemma 36 (a). Source: `report-4.md`, Lemma 36 (a) (line 259): "Every vertical
tile has s <= y_i <= h ... The four spines lie in four distinct columns". -/
theorem lemma36a {a b d : ℤ} {t : Fin 5 → Finset Cell} {i₀ : Fin 5} {κ : Fin 5 → GridIso}
    (H : TypeH1 a b d t i₀ κ) (hh : b - a ≤ d) {s : ℤ} (hs : FullRows (t i₀) a s) :
    (∀ i, i ≠ i₀ → s ≤ (κ i).boxY a ∧ (κ i).boxY a ≤ b - a) ∧
      ∀ i j, i ≠ i₀ → j ≠ i₀ → i ≠ j → (κ i).shift.1 ≠ (κ j).shift.1 := by
  refine ⟨fun i hi => ⟨(H.lemma30a (by norm_num) hs).1 i hi, ?_⟩, fun i j hi hj hij =>
    spine_ne H hh hi hj hij⟩
  have := bounds_V H.frame (H.vert i hi)
  omega

/-- Lemma 36 (b). Source: `report-4.md`, Lemma 36 (b) (line 260): "T meets column 0
in the rows [0, u_0) exactly, and column a - 1 in [0, u_1)." The argument is
`CaseII2.col_zero_closed`. -/
theorem lemma36b {a b d : ℤ} {t : Fin 5 → Finset Cell} {i₀ : Fin 5} {κ : Fin 5 → GridIso}
    (H : TypeH1 a b d t i₀ κ) :
    (∀ y : ℤ, (0, y) ∈ t i₀ ↔ 0 ≤ y ∧ y < colCount (t i₀) 0) ∧
      ∀ y : ℤ, (a - 1, y) ∈ t i₀ ↔ 0 ≤ y ∧ y < colCount (t i₀) (a - 1) :=
  ⟨col_zero H (by norm_num), col_last H (by norm_num)⟩

/-- Lemma 36 (c). Source: `report-4.md`, Lemma 36 (c) (line 261): the top row of the
box of a vertical tile is an interval starting at the spine cell, "the image of
column 0 of T if V reverses the order and of column a - 1 if V keeps it"; the
bottom row is the image of the other end column. -/
theorem lemma36c {a b d : ℤ} {t : Fin 5 → Finset Cell} {i₀ : Fin 5} {κ : Fin 5 → GridIso}
    (H : TypeH1 a b d t i₀ κ) {i : Fin 5} (hi : i ≠ i₀) (j : ℤ) :
    (((if (κ i).negX then -j else j) + (κ i).shift.1, (κ i).boxY a + a - 1) ∈ t i ↔
        0 ≤ j ∧ j < (if (κ i).negY then colCount (t i₀) 0 else colCount (t i₀) (a - 1))) ∧
      (((if (κ i).negX then -j else j) + (κ i).shift.1, (κ i).boxY a) ∈ t i ↔
        0 ≤ j ∧ j < (if (κ i).negY then colCount (t i₀) (a - 1) else colCount (t i₀) 0)) := by
  have h0 := (lemma36b H).1 j
  have h1 := (lemma36b H).2 j
  have hj : j = if (κ i).negX then (κ i).boxX d + d - 1 -
      ((if (κ i).negX then -j else j) + (κ i).shift.1)
      else (if (κ i).negX then -j else j) + (κ i).shift.1 - (κ i).boxX d := by
    rw [shift_eq (κ i) d]
    cases (κ i).negX <;> simp
  constructor
  · rw [mem_V_of H.frame (H.vert i hi) (x := if (κ i).negY then 0 else a - 1) (j := j)
      (by split <;> omega) hj]
    cases (κ i).negY
    · exact h1
    · exact h0
  · rw [mem_V_of H.frame (H.vert i hi) (x := if (κ i).negY then a - 1 else 0) (j := j)
      (by split <;> omega) hj]
    cases (κ i).negY
    · exact h0
    · exact h1

/-- Lemma 36 (d), the three states at column 0: the numeric part of each state.
Source: `report-4.md`, Lemma 36 (d) (lines 262-265): alpha (one tile at the wall, a
top tile with spine column 0, `u_0 = h`), beta (a top tile with spine column 0 and
a non-top tile with spine column `d - 1`, `u_0 < h`, `t = h - u_0`), gamma (a
non-top tile with spine column 0 and `y = u_0 < h`, and a top tile with spine column
`d - 1`, `t = h - u_0`). The states at column `a - 1` are those of the mirror image
(`TypeH1.mirror`). The states with the rows of column 0 that each tile holds are
`CaseII2.wall_left` and `CaseII2.wall_right`. -/
theorem lemma36d {a b d : ℤ} {t : Fin 5 → Finset Cell} {i₀ : Fin 5} {κ : Fin 5 → GridIso}
    (H : TypeH1 a b d t i₀ κ) (hh : b - a ≤ d) :
    (∃ w, w ∈ topTiles b t i₀ ∧ (κ w).boxX d = 0 ∧ (κ w).negX = false ∧
        (∀ i, i ≠ i₀ → (κ i).boxX d = 0 → i = w) ∧ colCount (t i₀) 0 = b - a) ∨
      (∃ w z, w ∈ topTiles b t i₀ ∧ z ≠ i₀ ∧ z ∉ topTiles b t i₀ ∧
        (κ w).boxX d = 0 ∧ (κ z).boxX d = 0 ∧ (κ w).negX = false ∧ (κ z).negX = true ∧
        colCount (t i₀) 0 < b - a ∧ rowCount (t i₀) (d - 1) = b - a - colCount (t i₀) 0) ∨
      (∃ w z, w ∈ topTiles b t i₀ ∧ z ≠ i₀ ∧ z ∉ topTiles b t i₀ ∧
        (κ w).boxX d = 0 ∧ (κ z).boxX d = 0 ∧ (κ w).negX = true ∧ (κ z).negX = false ∧
        (κ z).boxY a = colCount (t i₀) 0 ∧ colCount (t i₀) 0 < b - a ∧
        rowCount (t i₀) (d - 1) = b - a - colCount (t i₀) 0) := by
  have F := H.frame
  have h23 := H.corollary23 (by norm_num) (by decide)
  rcases wall_left H (by norm_num) h23.2.1 hh with ⟨w, hw, hwY, hwX, hwn, hwu, hu0⟩ |
      ⟨w, z, hw, hz, hwY, hzY, hwX, hzX, hwn, hzn, hwu, hu0, hcol⟩ |
      ⟨w, z, hw, hz, hwY, hzY, hwX, hzX, hwn, hzn, hwu, hu0, hcol⟩
  · exact Or.inl ⟨w, (mem_topTiles H (by norm_num) hw).2 hwY, hwX, hwn, hwu, hu0⟩
  · refine Or.inr (Or.inl ⟨w, z, (mem_topTiles H (by norm_num) hw).2 hwY, hz, ?_, hwX, hzX, hwn,
      hzn, hu0, ?_⟩)
    · rw [mem_topTiles H (by norm_num) hz]
      omega
    · have h1 := far_count F (H.vert z hz)
      rw [hzn, hzX] at h1
      simp only [Bool.not_false, ite_true] at h1
      rw [← h1, colCount_of_interval hcol hu0.le]
  · refine Or.inr (Or.inr ⟨w, z, (mem_topTiles H (by norm_num) hw).2 hwY, hz, ?_, hwX, hzX, hwn,
      hzn, hzY, hu0, ?_⟩)
    · rw [mem_topTiles H (by norm_num) hz]
      omega
    · have h1 := far_count F (H.vert w hw)
      rw [hwn, hwX] at h1
      simp only [Bool.not_false, ite_true] at h1
      rw [← h1, colCount_of_interval hcol (by omega)]
      omega

/-- Lemma 36 (e), first sentence. Source: `report-4.md`, Lemma 36 (e) (line 266):
"u_0 <= h and u_1 <= h." The other sentences are `CaseII2.gamma_corner`. -/
theorem lemma36e {a b d : ℤ} {t : Fin 5 → Finset Cell} {i₀ : Fin 5} {κ : Fin 5 → GridIso}
    (H : TypeH1 a b d t i₀ κ) (hh : b - a ≤ d) :
    colCount (t i₀) 0 ≤ b - a ∧ colCount (t i₀) (a - 1) ≤ b - a :=
  col_le H (by norm_num) (H.corollary23 (by norm_num) (by decide)).2.1 hh

/-- Lemma 36 (f), first sentence. Source: `report-4.md`, Lemma 36 (f) (line 267): "No
spine column of a non-top tile is in Top." -/
theorem lemma36f {a b d : ℤ} {t : Fin 5 → Finset Cell} {i₀ : Fin 5} {κ : Fin 5 → GridIso}
    (H : TypeH1 a b d t i₀ κ) (hh : b - a ≤ d) {z : Fin 5} (hz : z ≠ i₀)
    (hzt : z ∉ topTiles b t i₀) : ((κ z).shift.1, d - 1) ∉ t i₀ :=
  spine_not_top H (by norm_num) (H.corollary23 (by norm_num) (by decide)).2.1 hh hz hzt

/-- Proposition 37. Source: `report-4.md`, section 5c, Proposition 37 (line 274):
"In the setting of this section there are not three top tiles." The setting is
type H1 with `k = 5`, `d < a`, `1 <= h <= d`. -/
theorem proposition37 {a b d : ℤ} {t : Fin 5 → Finset Cell} {i₀ : Fin 5}
    {κ : Fin 5 → GridIso} (H : TypeH1 a b d t i₀ κ) (hda : d < a) (hh : b - a ≤ d) :
    (topTiles b t i₀).card ≠ 3 := by
  intro hcard
  obtain ⟨ha, hfull | hfull⟩ := one_tile_block H (by norm_num) hcard
  · exact proposition37_full H hda hh hcard ha hfull
  · refine proposition37_full H.mirror hda hh ?_ ha fun y h1 h2 => ?_
    · rw [topTiles_mirror]
      exact hcard
    · rw [mem_mirror, sub_zero]
      exact hfull y h1 h2

/-- Proposition 38. Source: `report-4.md`, section 5c, Proposition 38 (line 280):
"In the setting of this section there are not two top tiles." Proof: Steps 1 to
4 and the tail for `h = d` (lines 282-299). Step 1 is `Setting38.step1`, Step 2 is
in `proposition38_alpha`, the normal form of line 288 is `NF38`, and the tail and
Steps 3 and 4 are `NF38.tail`, `NF38.step3`, `NF38.step4`. -/
theorem proposition38 {a b d : ℤ} {t : Fin 5 → Finset Cell} {i₀ : Fin 5}
    {κ : Fin 5 → GridIso} (H : TypeH1 a b d t i₀ κ) (hda : d < a) (hh : b - a ≤ d) :
    (topTiles b t i₀).card ≠ 2 := by
  intro hcard
  have F := H.frame
  have hk : 2 ≤ 5 := by norm_num
  have hl := wall_left H hk hda hh
  have hr := wall_right H hk hda hh
  -- one wall in state alpha
  by_cases hα : WallAlpha a b d t i₀ κ 0 0 false
  · exact proposition38_alpha H hda hh hcard hα
  by_cases hα' : WallAlpha a b d t i₀ κ (a - d) (a - 1) true
  · refine proposition38_alpha H.mirror hda hh ?_ ((wallAlpha_mirror H).2 hα')
    rw [topTiles_mirror]
    exact hcard
  -- otherwise `u_0 < h` and `u_1 < h`, so no wall is in state gamma
  have hu0 : colCount (t i₀) 0 < b - a := by
    rcases hl with h | ⟨w, z, h⟩ | ⟨w, z, h⟩
    · exact absurd h hα
    · exact h.2.2.2.2.2.2.2.2.2.1
    · exact h.2.2.2.2.2.2.2.2.2.1
  have hu1 : colCount (t i₀) (a - 1) < b - a := by
    rcases hr with h | ⟨w, z, h⟩ | ⟨w, z, h⟩
    · exact absurd h hα'
    · exact h.2.2.2.2.2.2.2.2.2.1
    · exact h.2.2.2.2.2.2.2.2.2.1
  have hγ : ¬ (WallGamma a b d t i₀ κ 0 0 false ∨ WallGamma a b d t i₀ κ (a - d) (a - 1) true) := by
    intro h
    rcases gamma_corner H h with h | h
    · have := (col_zero H hk _).1 h
      omega
    · have := (col_last H hk _).1 h
      omega
  rcases hl with h | hβ | h
  · exact hα h
  rcases hr with h | hβ' | h
  · exact hα' h
  · -- beta, beta': `t = h - u_0 = h - u_1`, against Step 1
    obtain ⟨w₁, z₁, hw₁, hz₁, hwY, hzY, hwX, hzX, hwn, hzn, -, -, hcol⟩ := hβ
    obtain ⟨w, z₂, hw, hz₂, hwY', hzY', hwX', hzX', hwn', hzn', hwu', -, hcol'⟩ := hβ'
    have e1 := far_count F (H.vert z₁ hz₁)
    have e2 := far_count F (H.vert z₂ hz₂)
    rw [hzn, hzX] at e1
    rw [hzn', hzX'] at e2
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false] at e1 e2
    rw [colCount_of_interval hcol hu0.le] at e1
    rw [show a - d + d - 1 = a - 1 by ring, colCount_of_interval hcol' hu1.le] at e2
    obtain ⟨s, hs1, -, hs⟩ := F.exists_fullRows
    obtain ⟨w₂, z, S, -⟩ := exists_setting38 H hda hh hcard hw₁ hwY hwX hz₂ (by omega)
    have hw₂ : w₂ = w := by
      rcases hwu' _ S.w₂ne S.w₂X with h | h
      · exact h
      · have h1 := S.w₂Y
        rw [h] at h1
        omega
    subst hw₂
    have := S.step1 hs hs1 hwn hwn'
    omega
  · exact hγ (Or.inr h)
  · exact hγ (Or.inl h)

/-- Corollary 39. Source: `report-4.md`, Corollary 39 (line 303): "Case (II.2) of
Theorem 6 does not occur." Proof (line 305): Corollary 35, Corollary 29,
Propositions 37 and 38. -/
theorem corollary39 {a b d : ℤ} {t : Fin 5 → Finset Cell} {i₀ : Fin 5}
    {κ : Fin 5 → GridIso} (H : TypeH1 a b d t i₀ κ) : False := by
  have h35 := corollary35 H
  rcases H.corollary29 with h2 | h3
  · exact proposition38 H h35.2.1 (by omega) h2
  · exact proposition37 H h35.2.1 (by omega) h3

end PolyominoOddOrder
