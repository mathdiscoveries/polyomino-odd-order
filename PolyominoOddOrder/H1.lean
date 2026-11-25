module

public import PolyominoOddOrder.Spine

/-!
# Type H1: one tile on row 0, every other tile vertical (`H1.lean`)

Blueprint unit HA. Type H1 for a general number of tiles, first part: the column
blocks of a family of vertical tiles, Theorem 10 (`report-2.md` section 1),
Theorem 22 and Corollary 23 (`report-4.md` section 1). The second part (the top
row, Propositions 27 and 28, Lemma 30) is `H1Top.lean`.

Notation of the reports, in the coordinates of `Spine.lean`: `u[x]` is
`colCount (t i₀) x`, `v[y]` is `rowCount (t i₀) y`; a vertical tile `t i` has
spine column `(κ i).shift.1`, box `[boxX, boxX + d) x [boxY, boxY + a)`, is
right-type when `(κ i).negX = false` and keeps the order when
`(κ i).negY = false`.

Commit `e5ca51d`.
-/

@[expose] public section

namespace PolyominoOddOrder

/-! ## Column blocks of a family of vertical tiles -/

/-- The numbers attached to a family `J` of vertical tiles, with `0` and `a`: the
spine column `c` of a right-type tile, `c + 1` for a left-type tile. Source:
`report-2.md`, Theorem 10, Step 3 (lines 78-80); `report-4.md`, Lemma 25 (b). -/
def colMarks (a : ℤ) {k : ℕ} (κ : Fin k → GridIso) (J : Finset (Fin k)) : Finset ℤ :=
  insert 0 (insert a (J.image fun i =>
    if (κ i).negX then (κ i).shift.1 + 1 else (κ i).shift.1))

/-- The block of a finite set `E` of lines that holds the interval `[u, v)`, when no
line of `E` cuts the interval. -/
private theorem exists_block {E : Finset ℤ} {lo hi u v : ℤ} (hlo : lo ∈ E) (hhi : hi ∈ E)
    (h1 : lo ≤ u) (h2 : v ≤ hi) (huv : u < v) (h : ∀ m ∈ E, m ≤ u ∨ v ≤ m) :
    ∃ e e' : ℤ, Consecutive E e e' ∧ e ≤ u ∧ v ≤ e' := by
  obtain ⟨e, he, hmax⟩ := Finset.exists_max_image (E.filter fun m => m ≤ u) id
    ⟨lo, Finset.mem_filter.2 ⟨hlo, h1⟩⟩
  obtain ⟨e', he', hmin⟩ := Finset.exists_min_image (E.filter fun m => v ≤ m) id
    ⟨hi, Finset.mem_filter.2 ⟨hhi, h2⟩⟩
  simp only [Finset.mem_filter, id] at he he' hmax hmin
  refine ⟨e, e', ⟨he.1, he'.1, by omega, fun m hm => ?_⟩, he.2, he'.2⟩
  rcases h m hm with hmu | hvm
  · exact Or.inl (hmax m ⟨hm, hmu⟩)
  · exact Or.inr (hmin m ⟨hm, hvm⟩)

/-- The columns of a set whose box has the columns `[u, v)`. -/
private theorem col_bounds {S : Finset Cell} {u v : ℤ} (h : xSpan S = Finset.Ico u v) {c : Cell}
    (hc : c ∈ S) : u ≤ c.1 ∧ c.1 < v := by
  rw [← Finset.mem_Ico, ← h, mem_xSpan]
  exact ⟨c, hc, c, hc, le_rfl, le_rfl⟩

/-- The rows of a set whose box has the rows `[u, v)`. -/
private theorem row_bounds {S : Finset Cell} {u v : ℤ} (h : ySpan S = Finset.Ico u v) {c : Cell}
    (hc : c ∈ S) : u ≤ c.2 ∧ c.2 < v := by
  rw [← Finset.mem_Ico, ← h, mem_ySpan]
  exact ⟨c, hc, c, hc, le_rfl, le_rfl⟩

/-- A set has a cell in the first and in the last column of its box. -/
private theorem exists_end_cols {S : Finset Cell} {u v : ℤ} (h : xSpan S = Finset.Ico u v)
    (huv : u < v) : (∃ y : ℤ, (u, y) ∈ S) ∧ ∃ y : ℤ, (v - 1, y) ∈ S := by
  have hu : u ∈ xSpan S := by rw [h, Finset.mem_Ico]; omega
  have hv : v - 1 ∈ xSpan S := by rw [h, Finset.mem_Ico]; omega
  obtain ⟨c, hc, _, _, hcu, _⟩ := mem_xSpan.1 hu
  obtain ⟨_, _, c', hc', _, hcv⟩ := mem_xSpan.1 hv
  have h1 := col_bounds h hc
  have h2 := col_bounds h hc'
  refine ⟨⟨c.2, ?_⟩, ⟨c'.2, ?_⟩⟩
  · obtain rfl : c.1 = u := by omega
    exact hc
  · have h3 : c'.1 = v - 1 := by omega
    rw [← h3]
    exact hc'

/-- A set has a cell in the first and in the last row of its box. -/
private theorem exists_end_rows {S : Finset Cell} {u v : ℤ} (h : ySpan S = Finset.Ico u v)
    (huv : u < v) : (∃ x : ℤ, (x, u) ∈ S) ∧ ∃ x : ℤ, (x, v - 1) ∈ S := by
  have hu : u ∈ ySpan S := by rw [h, Finset.mem_Ico]; omega
  have hv : v - 1 ∈ ySpan S := by rw [h, Finset.mem_Ico]; omega
  obtain ⟨c, hc, _, _, hcu, _⟩ := mem_ySpan.1 hu
  obtain ⟨_, _, c', hc', _, hcv⟩ := mem_ySpan.1 hv
  have h1 := row_bounds h hc
  have h2 := row_bounds h hc'
  refine ⟨⟨c.1, ?_⟩, ⟨c'.1, ?_⟩⟩
  · obtain rfl : c.2 = u := by omega
    exact hc
  · have h3 : c'.2 = v - 1 := by omega
    rw [← h3]
    exact hc'

/-- Two cells of a row count at least 2. -/
private theorem two_le_rowCount {S : Finset Cell} {x x' y : ℤ} (h : (x, y) ∈ S)
    (h' : (x', y) ∈ S) (hne : x ≠ x') : 2 ≤ rowCount S y := by
  have hc : 1 < (S.filter fun c => c.2 = y).card :=
    Finset.one_lt_card.2 ⟨(x, y), by simp [h], (x', y), by simp [h'], by simp [hne]⟩
  unfold rowCount
  omega

/-- Two cells of a column count at least 2. -/
private theorem two_le_colCount {S : Finset Cell} {x y y' : ℤ} (h : (x, y) ∈ S)
    (h' : (x, y') ∈ S) (hne : y ≠ y') : 2 ≤ colCount S x := by
  have hc : 1 < (S.filter fun c => c.1 = x).card :=
    Finset.one_lt_card.2 ⟨(x, y), by simp [h], (x, y'), by simp [h'], by simp [hne]⟩
  unfold colCount
  omega

/-- The spine column of a vertical tile is one of the two end columns of its box. -/
private theorem spine_end (g : GridIso) (d : ℤ) :
    (g.negX = false ∧ g.shift.1 = g.boxX d) ∨
      (g.negX = true ∧ g.shift.1 = g.boxX d + d - 1) := by
  unfold GridIso.boxX
  cases g.negX
  · exact Or.inl ⟨rfl, rfl⟩
  · refine Or.inr ⟨rfl, ?_⟩
    simp only [ite_true]
    omega

/-- The spine of a vertical tile starts in row `boxY` (order kept) or in the last
row of the box (order reversed). -/
private theorem spine_start (g : GridIso) (a : ℤ) :
    (g.negY = false ∧ g.shift.2 = g.boxY a) ∨
      (g.negY = true ∧ g.shift.2 = g.boxY a + a - 1) := by
  unfold GridIso.boxY
  cases g.negY
  · exact Or.inl ⟨rfl, rfl⟩
  · refine Or.inr ⟨rfl, ?_⟩
    simp only [ite_true]
    omega

/-- A mark is `0`, `a` or the mark of a tile of the family, which is the first
column of its box (right-type) or the column after the last (left-type). -/
private theorem mem_colMarks {a d : ℤ} {k : ℕ} {κ : Fin k → GridIso} {J : Finset (Fin k)}
    {m : ℤ} : m ∈ colMarks a κ J ↔ m = 0 ∨ m = a ∨ ∃ i ∈ J,
      ((κ i).negX = false ∧ m = (κ i).boxX d) ∨ ((κ i).negX = true ∧ m = (κ i).boxX d + d) := by
  unfold colMarks
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_image]
  refine or_congr Iff.rfl (or_congr Iff.rfl (exists_congr fun i => and_congr Iff.rfl ?_))
  rcases spine_end (κ i) d with ⟨hn, hs⟩ | ⟨hn, hs⟩
  · simp only [hn, hs, Bool.false_eq_true, ite_false, true_and, false_and, or_false]
    exact eq_comm
  · simp only [hn, hs, ite_true, true_and, Bool.true_eq_false, false_and, false_or]
    omega

/-- No mark of the family cuts the box of a tile of the family. Source:
`report-2.md`, Theorem 10, Step 3: "No vertical tile has cells both in columns <
e_l and in columns >= e_l". -/
private theorem Frame.mark_side {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell} {i₀ : Fin k}
    {κ : Fin k → GridIso} (F : Frame a b d t i₀ κ) (J : Finset (Fin k))
    (hJ : ∀ i ∈ J, (κ i).swap = true)
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      (∀ c ∈ t j, c.1 < (κ i).shift.1) ∨ (∀ c ∈ t j, (κ i).shift.1 < c.1))
    {i : Fin k} (hi : i ∈ J) {m : ℤ} (hm : m ∈ colMarks a κ J) :
    m ≤ (κ i).boxX d ∨ (κ i).boxX d + d ≤ m := by
  have hd := F.two_le_d
  obtain ⟨-, hxs, -, ⟨hx0, hxa⟩, -⟩ := F.vertical_spine (hJ i hi)
  rcases (mem_colMarks (d := d)).1 hm with rfl | rfl | ⟨j, hj, hjm⟩
  · exact Or.inl hx0
  · exact Or.inr hxa
  · by_cases hij : j = i
    · subst hij
      rcases hjm with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inl h.le
      · exact Or.inr h.ge
    · obtain ⟨⟨y, hy⟩, y', hy'⟩ := exists_end_cols hxs (by omega)
      have hsj := spine_end (κ j) d
      rcases hsep j hj i hi hij with hl | hr
      · have := hl _ hy'
        dsimp only at this
        refine Or.inr ?_
        rcases hjm with ⟨hn, h⟩ | ⟨hn, h⟩ <;> rw [hn] at hsj <;> simp at hsj <;> omega
      · have := hr _ hy
        dsimp only at this
        refine Or.inl ?_
        rcases hjm with ⟨hn, h⟩ | ⟨hn, h⟩ <;> rw [hn] at hsj <;> simp at hsj <;> omega


/-- Column blocks. Source: `report-2.md`, Theorem 10, Step 3 (lines 78-93), used
"word for word" in `report-4.md`, Lemma 25 (b), and again in Lemma 43 (c). If each
tile of a family `J` of vertical tiles lies on one side of the spine column of
every other, then each lies in one block, with its spine in the first column of
the block (right-type) or the last (left-type). -/
theorem Frame.column_blocks {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell} {i₀ : Fin k}
    {κ : Fin k → GridIso} (F : Frame a b d t i₀ κ) (J : Finset (Fin k))
    (hJ : ∀ i ∈ J, (κ i).swap = true)
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      (∀ c ∈ t j, c.1 < (κ i).shift.1) ∨ (∀ c ∈ t j, (κ i).shift.1 < c.1)) :
    ∀ i ∈ J, ∃ e e' : ℤ, Consecutive (colMarks a κ J) e e' ∧
      e ≤ (κ i).boxX d ∧ (κ i).boxX d + d ≤ e' ∧
      ((κ i).negX = false → (κ i).shift.1 = e) ∧
      ((κ i).negX = true → (κ i).shift.1 = e' - 1) := by
  intro i hi
  have hd := F.two_le_d
  obtain ⟨-, -, -, ⟨hx0, hxa⟩, -⟩ := F.vertical_spine (hJ i hi)
  obtain ⟨e, e', hee', he, he'⟩ := exists_block (E := colMarks a κ J) (lo := 0) (hi := a)
    (u := (κ i).boxX d) (v := (κ i).boxX d + d) (by simp [colMarks]) (by simp [colMarks]) hx0 hxa
    (by omega) fun m hm => F.mark_side J hJ hsep hi hm
  refine ⟨e, e', hee', he, he', fun hn => ?_, fun hn => ?_⟩
  · have hs : (κ i).shift.1 = (κ i).boxX d := by
      rcases spine_end (κ i) d with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · rw [hn] at h
        exact absurd h (by decide)
    have := hee'.2.2.2 _ ((mem_colMarks (d := d)).2 (Or.inr (Or.inr ⟨i, hi, Or.inl ⟨hn, rfl⟩⟩)))
    omega
  · have hs : (κ i).shift.1 = (κ i).boxX d + d - 1 := by
      rcases spine_end (κ i) d with ⟨h, -⟩ | ⟨-, h⟩
      · rw [hn] at h
        exact absurd h (by decide)
      · exact h
    have := hee'.2.2.2 _ ((mem_colMarks (d := d)).2 (Or.inr (Or.inr ⟨i, hi, Or.inr ⟨hn, rfl⟩⟩)))
    omega

/-- A block holds at most one right-type and at most one left-type tile of the
family. Source: `report-2.md`, Theorem 10, Step 3, last sentence. -/
theorem Frame.column_blocks_unique {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell}
    {i₀ : Fin k} {κ : Fin k → GridIso} (F : Frame a b d t i₀ κ) (J : Finset (Fin k))
    (hJ : ∀ i ∈ J, (κ i).swap = true)
    (hsep : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      (∀ c ∈ t j, c.1 < (κ i).shift.1) ∨ (∀ c ∈ t j, (κ i).shift.1 < c.1))
    {e e' : ℤ} (hee' : Consecutive (colMarks a κ J) e e') {i j : Fin k} (hi : i ∈ J)
    (hj : j ∈ J) (hie : e ≤ (κ i).boxX d ∧ (κ i).boxX d + d ≤ e')
    (hje : e ≤ (κ j).boxX d ∧ (κ j).boxX d + d ≤ e') (hneg : (κ i).negX = (κ j).negX) :
    i = j := by
  by_contra hij
  have hd := F.two_le_d
  have key : ∀ l ∈ J, e ≤ (κ l).boxX d → (κ l).boxX d + d ≤ e' →
      (κ l).shift.1 = if (κ l).negX then e' - 1 else e := by
    intro l hl h1 h2
    rcases spine_end (κ l) d with ⟨hn, hs⟩ | ⟨hn, hs⟩
    · have := hee'.2.2.2 _
        ((mem_colMarks (d := d)).2 (Or.inr (Or.inr ⟨l, hl, Or.inl ⟨hn, rfl⟩⟩)))
      rw [hn, ite_eq_right (by decide)]
      omega
    · have := hee'.2.2.2 _
        ((mem_colMarks (d := d)).2 (Or.inr (Or.inr ⟨l, hl, Or.inr ⟨hn, rfl⟩⟩)))
      rw [hn, ite_eq_left rfl]
      omega
  have hs : (κ i).shift.1 = (κ j).shift.1 := by
    rw [key i hi hie.1 hie.2, key j hj hje.1 hje.2, hneg]
  have ha := F.two_le
  have hcell := (F.vertical_spine (hJ j hj)).1 ((κ j).boxY a) le_rfl (by omega)
  rcases hsep i hi j hj hij with h | h
  · have := h _ hcell
    dsimp only at this
    omega
  · have := h _ hcell
    dsimp only at this
    omega

namespace TypeH1

variable {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell} {i₀ : Fin k} {κ : Fin k → GridIso}

/-- In type H1 with at least two tiles, `2 <= d <= a <= b - 1` (Lemma 4). -/
theorem bounds (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) : 2 ≤ d ∧ d ≤ a ∧ a ≤ b - 1 := by
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 hk
  obtain ⟨i, hi⟩ := exists_ne i₀
  exact ⟨H.frame.two_le_d.1, H.frame.vertical_bounds (H.vert i hi)⟩

/-! ## Theorem 10 (`b = a + 1`) -/

/-- Theorem 10, Steps 1 and 2. Source: `report-2.md`, Theorem 10 (lines 60-76): for
`b = a + 1` every spine fills its column above row 0, so the spine columns are
bare positions of `T`, pairwise distinct, and every other vertical tile lies on
one side of a spine column. -/
theorem theorem10_spines (H : TypeH1 a b d t i₀ κ) (hb : b = a + 1) {i : Fin k}
    (hi : i ≠ i₀) :
    (κ i).boxY a = 1 ∧ colCount (t i₀) (κ i).shift.1 = 1 ∧
      ∀ j, j ≠ i₀ → j ≠ i →
        (∀ c ∈ t j, c.1 < (κ i).shift.1) ∨ (∀ c ∈ t j, (κ i).shift.1 < c.1) := by
  have hF := H.frame
  have ha := hF.two_le
  have ht := hF.isTiling
  have hd := hF.two_le_d
  obtain ⟨hsp, hxs, -, ⟨hx0, hxa⟩, hy1, hyb⟩ := hF.vertical_spine (H.vert i hi)
  have hY : (κ i).boxY a = 1 := by omega
  have hs := spine_end (κ i) d
  have hc0 : 0 ≤ (κ i).shift.1 := by omega
  have hca : (κ i).shift.1 < a := by omega
  -- a cell of the spine column is the bottom cell, in `T`, or a spine cell
  have hcol : ∀ y : ℤ, ((κ i).shift.1, y) ∈ R a b → y ≠ 0 → ((κ i).shift.1, y) ∈ t i := by
    intro y hy hy0
    have := mem_R.1 hy
    dsimp only at this
    exact hsp y (by omega) (by omega)
  refine ⟨hY, ?_, fun j hj hji => ?_⟩
  · unfold colCount
    have h1 : ((t i₀).filter fun c => c.1 = (κ i).shift.1) = {((κ i).shift.1, 0)} := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨hxy, rfl⟩
        refine ⟨rfl, ?_⟩
        by_contra hy0
        exact hi (ht.tile_unique (hcol y (ht.subset_R _ hxy) hy0) hxy)
      · rintro ⟨rfl, rfl⟩
        exact ⟨hF.row0 _ hc0 hca, rfl⟩
    rw [h1]
    simp
  · by_contra hcon
    push Not at hcon
    obtain ⟨⟨p, hp, hp1⟩, q, hq, hq1⟩ := hcon
    obtain ⟨y, hy⟩ := (ht.tile_isPolyomino hF.poly j).2.exists_in_col hq hp hq1 hp1
    by_cases hy0 : y = 0
    · subst hy0
      exact hj (ht.tile_unique hy (hF.row0 _ hc0 hca))
    · exact hji (ht.tile_unique hy (hcol y (ht.subset_R _ hy) hy0))

/-- In type H1 a cell in a row `>= d` is in a vertical tile. -/
private theorem exists_vertical_above (H : TypeH1 a b d t i₀ κ) {x y : ℤ} (hx0 : 0 ≤ x)
    (hxa : x < a) (hy : d ≤ y) (hyb : y < b) : ∃ i, i ≠ i₀ ∧ (x, y) ∈ t i := by
  have hd := H.frame.two_le_d
  obtain ⟨i, hi⟩ := H.frame.isTiling.exists_tile (c := (x, y))
    (mem_R.2 ⟨⟨hx0, hxa⟩, by dsimp only; omega, hyb⟩)
  refine ⟨i, ?_, hi⟩
  rintro rfl
  have := row_bounds H.frame.rows hi
  dsimp only at this
  omega

/-- The spine columns of type H1 for `b = a + 1` separate the vertical tiles: the
hypothesis of `Frame.column_blocks` for all of them. -/
private theorem sep_of_eq (H : TypeH1 a b d t i₀ κ) (hb : b = a + 1) (J : Finset (Fin k))
    (hJ : ∀ i, i ∈ J ↔ i ≠ i₀) : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      (∀ c ∈ t j, c.1 < (κ i).shift.1) ∨ (∀ c ∈ t j, (κ i).shift.1 < c.1) :=
  fun i hi j hj hij =>
    (H.theorem10_spines hb ((hJ i).1 hi)).2.2 j ((hJ j).1 hj) (Ne.symm hij)

/-- Distinct vertical tiles of type H1 have distinct spine columns (`b = a + 1`). -/
private theorem spine_injective (H : TypeH1 a b d t i₀ κ) (hb : b = a + 1) {i j : Fin k}
    (hi : i ≠ i₀) (hj : j ≠ i₀) (h : (κ i).shift.1 = (κ j).shift.1) : i = j := by
  by_contra hij
  have ha := H.frame.two_le
  have hcell := (H.frame.vertical_spine (H.vert j hj)).1 ((κ j).boxY a) le_rfl (by omega)
  rcases (H.theorem10_spines hb hi).2.2 j hj (Ne.symm hij) with h' | h'
  · have := h' _ hcell
    dsimp only at this
    omega
  · have := h' _ hcell
    dsimp only at this
    omega

/-- Theorem 10, Step 4: every block has at least `d` columns. -/
private theorem block_width (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) (hb : b = a + 1)
    (J : Finset (Fin k)) (hJ : ∀ i, i ∈ J ↔ i ≠ i₀) {e e' : ℤ}
    (hee' : Consecutive (colMarks a κ J) e e') :
    (0 ≤ e ∧ e' ≤ a) ∧ d ≤ e' - e ∧
      ∀ i, i ≠ i₀ → (∃ c ∈ t i, e ≤ c.1 ∧ c.1 < e') →
        e ≤ (κ i).boxX d ∧ (κ i).boxX d + d ≤ e' := by
  have hF := H.frame
  have hbd := H.bounds hk
  have hJv : ∀ i ∈ J, (κ i).swap = true := fun i hi => H.vert i ((hJ i).1 hi)
  have hsep := H.sep_of_eq hb J hJ
  have hrange : ∀ m ∈ colMarks a κ J, 0 ≤ m ∧ m ≤ a := by
    intro m hm
    rcases (mem_colMarks (d := d)).1 hm with rfl | rfl | ⟨j, hj, hjm⟩
    · omega
    · omega
    · have := (hF.vertical_spine (hJv j hj)).2.2.2.1
      omega
  have he := hrange e hee'.1
  have he' := hrange e' hee'.2.1
  have hlt := hee'.2.2.1
  have hin : ∀ i, i ≠ i₀ → (∃ c ∈ t i, e ≤ c.1 ∧ c.1 < e') →
      e ≤ (κ i).boxX d ∧ (κ i).boxX d + d ≤ e' := by
    rintro i hi ⟨c, hc, h1, h2⟩
    have hiJ := (hJ i).2 hi
    have hcb := col_bounds (hF.vertical_spine (hJv i hiJ)).2.1 hc
    have m1 := hF.mark_side J hJv hsep hiJ hee'.1
    have m2 := hF.mark_side J hJv hsep hiJ hee'.2.1
    omega
  refine ⟨⟨he.1, he'.2⟩, ?_, hin⟩
  obtain ⟨i, hi, hc⟩ := H.exists_vertical_above (x := e) (y := a) he.1 (by omega) hbd.2.1
    (by omega)
  have := hin i hi ⟨_, hc, le_rfl, hlt⟩
  omega

/-- Theorem 10, the consequences of Step 4: at most one spine column is `<= d - 2`,
namely 0, and at most one is `>= a - d + 1`, namely `a - 1`. -/
private theorem spine_range (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) (hb : b = a + 1) {j : Fin k}
    (hj : j ≠ i₀) :
    ((κ j).shift.1 ≤ d - 2 → (κ j).shift.1 = 0) ∧
      (a - d + 1 ≤ (κ j).shift.1 → (κ j).shift.1 = a - 1) := by
  have hbd := H.bounds hk
  obtain ⟨J, hJ⟩ : ∃ J : Finset (Fin k), ∀ i, i ∈ J ↔ i ≠ i₀ := ⟨Finset.univ.erase i₀, by simp⟩
  have hjJ := (hJ j).2 hj
  have hbox := (H.frame.vertical_spine (H.vert j hj)).2.2.2.1
  have h0 : (0 : ℤ) ∈ colMarks a κ J := by simp [colMarks]
  have hA : a ∈ colMarks a κ J := by simp [colMarks]
  -- the distance of a mark from the two ends
  have hlow : ∀ m ∈ colMarks a κ J, 0 < m → d ≤ m := by
    intro m hm hpos
    obtain ⟨e, e', hee', h1, h2⟩ := exists_block (u := m - 1) (v := m) h0 hm (by omega) le_rfl
      (by omega) fun n _ => by omega
    have hw := H.block_width hk hb J hJ hee'
    have := hee'.2.2.2 m hm
    omega
  have hhigh : ∀ m ∈ colMarks a κ J, m < a → m ≤ a - d := by
    intro m hm hlt
    obtain ⟨e, e', hee', h1, h2⟩ := exists_block (u := m) (v := m + 1) hm hA le_rfl (by omega)
      (by omega) fun n _ => by omega
    have hw := H.block_width hk hb J hJ hee'
    have := hee'.2.2.2 m hm
    omega
  rcases spine_end (κ j) d with ⟨hn, hs⟩ | ⟨hn, hs⟩
  · have hm := (mem_colMarks (d := d)).2
      (Or.inr (Or.inr ⟨j, hjJ, Or.inl ⟨hn, rfl⟩⟩) : _ ∨ (κ j).boxX d = a ∨ _)
    have m1 := hlow _ hm
    omega
  · have hm := (mem_colMarks (d := d)).2
      (Or.inr (Or.inr ⟨j, hjJ, Or.inr ⟨hn, rfl⟩⟩) : _ ∨ (κ j).boxX d + d = a ∨ _)
    have m1 := hhigh _ hm
    omega


/-- Theorem 10, Steps 4 and 5. Source: `report-2.md`, Theorem 10 (lines 95-116):
every block of the vertical tiles has at least `d` columns and holds exactly two
vertical tiles. `J` is the set of all tiles other than `T`. -/
theorem theorem10_blocks (H : TypeH1 a b d t i₀ κ) (hk : 3 ≤ k) (hb : b = a + 1)
    (J : Finset (Fin k)) (hJ : ∀ i, i ∈ J ↔ i ≠ i₀) {e e' : ℤ}
    (hee' : Consecutive (colMarks a κ J) e e') :
    d ≤ e' - e ∧
      (J.filter fun i => e ≤ (κ i).boxX d ∧ (κ i).boxX d + d ≤ e').card = 2 := by
  classical
  have hF := H.frame
  have hbd := H.bounds (by omega)
  have hJv : ∀ i ∈ J, (κ i).swap = true := fun i hi => H.vert i ((hJ i).1 hi)
  have hsep := H.sep_of_eq hb J hJ
  obtain ⟨⟨he0, hea⟩, hw, hin⟩ := H.block_width (by omega) hb J hJ hee'
  refine ⟨hw, ?_⟩
  set S := J.filter fun i => e ≤ (κ i).boxX d ∧ (κ i).boxX d + d ≤ e' with hS
  have hmemS : ∀ {i}, i ∈ S ↔ i ∈ J ∧ e ≤ (κ i).boxX d ∧ (κ i).boxX d + d ≤ e' := by
    intro i
    rw [hS, Finset.mem_filter]
  -- at most one tile of each type
  have hle : S.card ≤ 2 := by
    have huniq : ∀ n : Bool, (S.filter fun i => (κ i).negX = n).card ≤ 1 := by
      intro n
      refine Finset.card_le_one.2 fun i hi j hj => ?_
      rw [Finset.mem_filter, hmemS] at hi hj
      exact hF.column_blocks_unique J hJv hsep hee' hi.1.1 hj.1.1 hi.1.2 hj.1.2
        (hi.2.trans hj.2.symm)
    have hsub : S ⊆ (S.filter fun i => (κ i).negX = true) ∪
        (S.filter fun i => (κ i).negX = false) := by
      intro i hi
      cases h : (κ i).negX
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hi, h⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hi, h⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (S.filter fun i => (κ i).negX = true)
      (S.filter fun i => (κ i).negX = false)
    have h3 := huniq true
    have h4 := huniq false
    omega
  -- a cell of the block in a row `>= d` is in a tile of the block
  have hcell : ∀ x y : ℤ, e ≤ x → x < e' → d ≤ y → y < b → ∃ i ∈ S, (x, y) ∈ t i := by
    intro x y hx hx' hy hy'
    obtain ⟨i, hi, hc⟩ := H.exists_vertical_above (x := x) (y := y) (by omega) (by omega) hy hy'
    exact ⟨i, hmemS.2 ⟨(hJ i).2 hi, hin i hi ⟨_, hc, hx, hx'⟩⟩, hc⟩
  have hpos : 0 < S.card := by
    obtain ⟨i, hi, -⟩ := hcell e a le_rfl (by omega) hbd.2.1 (by omega)
    exact Finset.card_pos.2 ⟨i, hi⟩
  have hne : S.card ≠ 1 := by
    intro h1
    obtain ⟨i, hSi⟩ := Finset.card_eq_one.1 h1
    have hiS : i ∈ S := by simp [hSi]
    have hiJ := (hmemS.1 hiS).1
    have hi := (hJ i).1 hiJ
    have hall : ∀ x y : ℤ, e ≤ x → x < e' → d ≤ y → y < b → (x, y) ∈ t i := by
      intro x y hx hx' hy hy'
      obtain ⟨j, hj, hc⟩ := hcell x y hx hx' hy hy'
      rw [hSi, Finset.mem_singleton] at hj
      exact hj ▸ hc
    have hY := (H.theorem10_spines hb hi).1
    -- the rows with one cell of the tile are below row `d`
    have hlow : ∀ j, j ≠ i₀ →
        (if (κ i).negY then -(κ j).shift.1 else (κ j).shift.1) + (κ i).shift.2 < d := by
      intro j hj
      have hbare := (H.theorem10_spines hb hj).2.1
      have hrow := hF.vertical_rowCount (H.vert i hi) (κ j).shift.1
      rw [hbare] at hrow
      by_contra hcon
      rw [not_lt] at hcon
      have hbox := (hF.vertical_spine (H.vert j hj)).2.2.2.1
      have hsj := spine_end (κ j) d
      have hupper :
          (if (κ i).negY then -(κ j).shift.1 else (κ j).shift.1) + (κ i).shift.2 < b := by
        rcases spine_start (κ i) a with ⟨hn, hs⟩ | ⟨hn, hs⟩ <;> rw [hn] <;> simp <;> omega
      have h2 := two_le_rowCount (hall e _ le_rfl (by omega) hcon hupper)
        (hall (e + 1) _ (by omega) (by omega) hcon hupper) (by omega)
      omega
    -- so two distinct spine columns lie where Step 4 allows one
    have hcard : 1 < (Finset.univ.erase i₀).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨j₁, hj₁, j₂, hj₂, hne⟩ := Finset.one_lt_card.1 hcard
    rw [Finset.mem_erase] at hj₁ hj₂
    have l₁ := hlow j₁ hj₁.1
    have l₂ := hlow j₂ hj₂.1
    have r₁ := H.spine_range (by omega) hb hj₁.1
    have r₂ := H.spine_range (by omega) hb hj₂.1
    refine hne (H.spine_injective hb hj₁.1 hj₂.1 ?_)
    rcases spine_start (κ i) a with ⟨hn, hs⟩ | ⟨hn, hs⟩
    · rw [hn, ite_eq_right (by decide)] at l₁ l₂
      rw [r₁.1 (by omega), r₂.1 (by omega)]
    · rw [hn, ite_eq_left rfl] at l₁ l₂
      rw [r₁.2 (by omega), r₂.2 (by omega)]
  omega

/-- Theorem 10, Step 6, first sentence: in every block the first column is the
spine column of a right-type tile and the last one that of a left-type tile. -/
private theorem block_spines (H : TypeH1 a b d t i₀ κ) (hk : 3 ≤ k) (hb : b = a + 1)
    (J : Finset (Fin k)) (hJ : ∀ i, i ∈ J ↔ i ≠ i₀) {e e' : ℤ}
    (hee' : Consecutive (colMarks a κ J) e e') :
    (∃ i, i ≠ i₀ ∧ (κ i).shift.1 = e) ∧ ∃ i, i ≠ i₀ ∧ (κ i).shift.1 = e' - 1 := by
  have hbd := H.bounds (by omega)
  have hJv : ∀ i ∈ J, (κ i).swap = true := fun i hi => H.vert i ((hJ i).1 hi)
  have hsep := H.sep_of_eq hb J hJ
  obtain ⟨i, j, hij, hS⟩ := Finset.card_eq_two.1 (H.theorem10_blocks hk hb J hJ hee').2
  have hi : i ∈ J.filter fun i => e ≤ (κ i).boxX d ∧ (κ i).boxX d + d ≤ e' := by simp [hS]
  have hj : j ∈ J.filter fun i => e ≤ (κ i).boxX d ∧ (κ i).boxX d + d ≤ e' := by simp [hS]
  rw [Finset.mem_filter] at hi hj
  have hneg : (κ i).negX ≠ (κ j).negX := fun h =>
    hij (H.frame.column_blocks_unique J hJv hsep hee' hi.1 hj.1 hi.2 hj.2 h)
  have key : ∀ l ∈ J, e ≤ (κ l).boxX d → (κ l).boxX d + d ≤ e' →
      ((κ l).negX = false ∧ (κ l).shift.1 = e) ∨ ((κ l).negX = true ∧ (κ l).shift.1 = e' - 1) := by
    intro l hl h1 h2
    rcases spine_end (κ l) d with ⟨hn, hs⟩ | ⟨hn, hs⟩
    · have := hee'.2.2.2 _
        ((mem_colMarks (d := d)).2 (Or.inr (Or.inr ⟨l, hl, Or.inl ⟨hn, rfl⟩⟩)))
      exact Or.inl ⟨hn, by omega⟩
    · have := hee'.2.2.2 _
        ((mem_colMarks (d := d)).2 (Or.inr (Or.inr ⟨l, hl, Or.inr ⟨hn, rfl⟩⟩)))
      exact Or.inr ⟨hn, by omega⟩
  have hi0 := (hJ i).1 hi.1
  have hj0 := (hJ j).1 hj.1
  rcases key i hi.1 hi.2.1 hi.2.2 with ⟨ni, si⟩ | ⟨ni, si⟩ <;>
    rcases key j hj.1 hj.2.1 hj.2.2 with ⟨nj, sj⟩ | ⟨nj, sj⟩
  · exact absurd (ni.trans nj.symm) hneg
  · exact ⟨⟨i, hi0, si⟩, j, hj0, sj⟩
  · exact ⟨⟨j, hj0, sj⟩, i, hi0, si⟩
  · exact absurd (ni.trans nj.symm) hneg


/-- Theorem 10. Source: `report-2.md`, section 1, Theorem 10 (lines 53-55):

> Let k >= 3 and b = a + 1. There is no k-copy tiling of R(a, a + 1) by a non-rectangular
> polyomino in which a tile T contains row 0 and, for some choice of the isometries in
> Lemma 4, every other tile is vertical.

Proof idea (Step 6): columns 0 and `a - 1` are spine columns, so by Lemma 9 every
vertical tile has only its spine cell in row `a`; then every column is a spine
column and `T` is row 0. -/
theorem theorem10 (H : TypeH1 a b d t i₀ κ) (hk : 3 ≤ k) (hb : b = a + 1) : False := by
  have hF := H.frame
  have hbd := H.bounds (by omega)
  obtain ⟨J, hJ⟩ : ∃ J : Finset (Fin k), ∀ i, i ∈ J ↔ i ≠ i₀ := ⟨Finset.univ.erase i₀, by simp⟩
  have h0 : (0 : ℤ) ∈ colMarks a κ J := by simp [colMarks]
  have hA : a ∈ colMarks a κ J := by simp [colMarks]
  -- columns 0 and `a - 1` are spine columns, so they are bare
  have hfirst : colCount (t i₀) 0 = 1 := by
    obtain ⟨e, e', hee', h1, h2⟩ := exists_block (u := 0) (v := 1) h0 hA le_rfl (by omega)
      (by omega) fun n _ => by omega
    have hw := H.block_width (by omega) hb J hJ hee'
    obtain ⟨⟨i, hi, hs⟩, -⟩ := H.block_spines hk hb J hJ hee'
    have := (H.theorem10_spines hb hi).2.1
    rwa [hs, show e = 0 by omega] at this
  have hlast : colCount (t i₀) (a - 1) = 1 := by
    obtain ⟨e, e', hee', h1, h2⟩ := exists_block (u := a - 1) (v := a) h0 hA (by omega) le_rfl
      (by omega) fun n _ => by omega
    have hw := H.block_width (by omega) hb J hJ hee'
    obtain ⟨-, i, hi, hs⟩ := H.block_spines hk hb J hJ hee'
    have := (H.theorem10_spines hb hi).2.1
    rwa [hs, show e' = a by omega] at this
  -- so a vertical tile has one cell in the top row
  have htop : ∀ i, i ≠ i₀ → rowCount (t i) a = 1 := by
    intro i hi
    have hY := (H.theorem10_spines hb hi).1
    rcases spine_start (κ i) a with ⟨hn, hs⟩ | ⟨hn, hs⟩
    · have := hF.vertical_rowCount (H.vert i hi) (a - 1)
      rw [hn, ite_eq_right (by decide), hlast, show a - 1 + (κ i).shift.2 = a by omega] at this
      exact this
    · have := hF.vertical_rowCount (H.vert i hi) 0
      rw [hn, ite_eq_left rfl, hfirst, show -0 + (κ i).shift.2 = a by omega] at this
      exact this
  -- so every column is a spine column and `T` is row 0
  obtain ⟨x, hx⟩ := hF.exists_in_row (y := 1) (by omega) (by omega)
  have hxR := mem_R.1 (hF.isTiling.subset_R _ hx)
  dsimp only at hxR
  obtain ⟨i, hi, hc⟩ := H.exists_vertical_above (x := x) (y := a) hxR.1.1 hxR.1.2 hbd.2.1
    (by omega)
  have hY := (H.theorem10_spines hb hi).1
  have hsp := (hF.vertical_spine (H.vert i hi)).1 a (by omega) (by omega)
  have hxs : x = (κ i).shift.1 := by
    by_contra hne
    have := two_le_rowCount hc hsp hne
    have := htop i hi
    omega
  have h1 := (H.theorem10_spines hb hi).2.1
  rw [← hxs] at h1
  have h2 := two_le_colCount hx (hF.row0 x hxR.1.1 hxR.1.2) (by omega)
  omega

/-! ## Theorem 22 and Corollary 23 (the square box) -/

/-- Theorem 22, Step 1. Source: `report-4.md`, Theorem 22 (line 43): for `d = a`
one tile holds the top row. Proof idea: the tiles on the two top corners have the
same box, the square `[0, a) x [b - a, b)`; `crossing_translate` makes them one
tile; `adjacent_corners_full_top`. -/
theorem theorem22_top_row (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) (hd : d = a) :
    ∃ i, i ≠ i₀ ∧ ∀ x : ℤ, 0 ≤ x → x < a → (x, b - 1) ∈ t i := by
  have hF := H.frame
  have ht := hF.isTiling
  have hbd := H.bounds hk
  have hbox : ∀ i, i ≠ i₀ → (∃ x : ℤ, (x, b - 1) ∈ t i) →
      xSpan (t i) = Finset.Ico 0 a ∧ ySpan (t i) = Finset.Ico (b - a) b := by
    rintro i hi ⟨x, hx⟩
    obtain ⟨-, hxs, hys, ⟨h1, h2⟩, h3, h4⟩ := hF.vertical_spine (H.vert i hi)
    have hr := row_bounds hys hx
    dsimp only at hr
    refine ⟨?_, ?_⟩
    · rw [hxs]
      congr 1 <;> omega
    · rw [hys]
      congr 1 <;> omega
  obtain ⟨i, hi, hl⟩ := H.exists_vertical_above (x := 0) (y := b - 1) le_rfl (by omega) (by omega)
    (by omega)
  obtain ⟨j, hj, hr⟩ := H.exists_vertical_above (x := a - 1) (y := b - 1) (by omega) (by omega)
    (by omega) (by omega)
  obtain ⟨hxi, hyi⟩ := hbox i hi ⟨_, hl⟩
  obtain ⟨hxj, hyj⟩ := hbox j hj ⟨_, hr⟩
  have hsub : ∀ l, xSpan (t l) = Finset.Ico 0 a → ySpan (t l) = Finset.Ico (b - a) b →
      t l ⊆ Finset.Ico 0 (0 + a) ×ˢ Finset.Ico (b - a) (b - a + a) := by
    intro l h1 h2 c hc
    have hc1 := col_bounds h1 hc
    have hc2 := row_bounds h2 hc
    rw [Finset.mem_product, Finset.mem_Ico, Finset.mem_Ico]
    omega
  obtain ⟨⟨y, hy⟩, y', hy'⟩ := exists_end_cols hxi (by omega)
  obtain ⟨⟨x, hx⟩, x', hx'⟩ := exists_end_rows hyj (by omega)
  obtain ⟨c, hci, hcj⟩ := crossing_translate 0 (b - a) a a (by omega) (by omega) (t i) (t j)
    (hsub i hxi hyi) (ht.tile_isPolyomino hF.poly i).2 ⟨y, hy⟩
    ⟨y', by rwa [show (0 : ℤ) + a - 1 = a - 1 by omega]⟩
    (hsub j hxj hyj) (ht.tile_isPolyomino hF.poly j).2 ⟨x, hx⟩
    ⟨x', by rwa [show b - a + a - 1 = b - 1 by omega]⟩
  obtain rfl := ht.tile_unique hci hcj
  exact ⟨i, hi, fun x hx0 hxa =>
    adjacent_corners_full_top (t i₀) hF.poly k hk a b t ht i hl hr x hx0 hxa⟩

/-- Theorem 22, Step 2. Source: `report-4.md`, Theorem 22 (line 45): `T` contains a
vertical side of its square box in full. -/
theorem theorem22_full_column (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) (hd : d = a) :
    (∀ y : ℤ, 0 ≤ y → y < a → (0, y) ∈ t i₀) ∨
      (∀ y : ℤ, 0 ≤ y → y < a → (a - 1, y) ∈ t i₀) := by
  have hF := H.frame
  have hbd := H.bounds hk
  obtain ⟨i, hi, htop⟩ := H.theorem22_top_row hk hd
  obtain ⟨-, hxs, hys, ⟨h1, h2⟩, h3, h4⟩ := hF.vertical_spine (H.vert i hi)
  have hr := row_bounds hys (htop 0 le_rfl (by omega))
  dsimp only at hr
  -- the cell `(x₀, y)` of `T` goes to the top row, for the right `x₀`
  have key : ∀ x₀ : ℤ, (if (κ i).negY then -x₀ else x₀) + (κ i).shift.2 = b - 1 →
      ∀ y : ℤ, 0 ≤ y → y < a → (x₀, y) ∈ t i₀ := by
    intro x₀ hx₀ y hy0 hya
    rw [← hF.vertical_mem (H.vert i hi) x₀ y, hx₀]
    refine htop _ ?_ ?_ <;>
      rcases spine_end (κ i) d with ⟨hn, hs⟩ | ⟨hn, hs⟩ <;> rw [hn] <;> simp <;> omega
  rcases spine_start (κ i) a with ⟨hn, hs⟩ | ⟨hn, hs⟩
  · refine Or.inr (key (a - 1) ?_)
    rw [hn, ite_eq_right (by decide)]
    omega
  · refine Or.inl (key 0 ?_)
    rw [hn, ite_eq_left rfl]
    omega

end TypeH1

/-- A rectangle of cells is rectangular. -/
private theorem isRectangular_product {u u' v v' : ℤ} :
    IsRectangular (Finset.Ico u u' ×ˢ Finset.Ico v v') := by
  refine Finset.Subset.antisymm (subset_boundingBox _) fun c hc => ?_
  rw [mem_boundingBox, mem_xSpan, mem_ySpan] at hc
  obtain ⟨⟨p, hp, q, hq, h1, h2⟩, p', hp', q', hq', h3, h4⟩ := hc
  rw [Finset.mem_product, Finset.mem_Ico, Finset.mem_Ico] at *
  omega

/-- Blocks of two, for any tiling: if every tile contains a full row of `R a b` that
is the bottom row of the tile (`up`) or its top row, then the number of tiles is
even. Source: `report-4.md`, Theorem 22, Step 3, after the choice of the row of
each tile. The up-type tiles are in bijection with the lines `0 = c_0 < ... <
c_t = b` without `b` (the bottom row of their block), the down-type tiles with
the lines without `0`. -/
private theorem even_of_end_rows {P : Finset Cell} {a b : ℤ} {k : ℕ} {t : Fin k → Finset Cell}
    (hP : IsPolyomino P) (hnr : ¬ IsRectangular P) (ht : IsTiling P a b t) (ha : 0 < a)
    (hb : 0 < b) (r : Fin k → ℤ) (up : Fin k → Bool)
    (hfull : ∀ i, ∀ x : ℤ, 0 ≤ x → x < a → (x, r i) ∈ t i)
    (hside : ∀ i, ∀ c ∈ t i, if up i then r i ≤ c.2 else c.2 ≤ r i) : Even k := by
  classical
  have hr : ∀ i, 0 ≤ r i ∧ r i < b := fun i =>
    (mem_R.1 (ht.subset_R i (hfull i 0 le_rfl ha))).2
  have hrinj : ∀ i j, r i = r j → i = j := fun i j h =>
    ht.tile_unique (hfull i 0 le_rfl ha) (h ▸ hfull j 0 le_rfl ha)
  -- a tile other than `i` lies above or below row `r i`
  have hsep : ∀ i j, j ≠ i → (∀ c ∈ t j, c.2 < r i) ∨ ∀ c ∈ t j, r i < c.2 := by
    intro i j hji
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨p, hp, hp1⟩, q, hq, hq1⟩ := hcon
    obtain ⟨x, hx⟩ := (ht.tile_isPolyomino hP j).2.exists_in_row hq hp hq1 hp1
    have hxR := mem_R.1 (ht.subset_R _ hx)
    exact hji (ht.tile_unique hx (hfull i x hxR.1.1 hxR.1.2))
  -- the lines
  let m : Fin k → ℤ := fun i => if up i then r i else r i + 1
  let E : Finset ℤ := insert 0 (insert b (Finset.univ.image m))
  have hmE : ∀ i, m i ∈ E := fun i => by simp [E]
  have h0E : (0 : ℤ) ∈ E := by simp [E]
  have hbE : b ∈ E := by simp [E]
  have hup : ∀ {i}, up i = true → m i = r i := fun {i} h => by simp [m, h]
  have hdown : ∀ {i}, up i = false → m i = r i + 1 := fun {i} h => by simp [m, h]
  have hE : ∀ e ∈ E, e = 0 ∨ e = b ∨ ∃ i, m i = e := fun e he => by simpa [E] using he
  have hEr : ∀ e ∈ E, 0 ≤ e ∧ e ≤ b := by
    intro e he
    rcases hE e he with rfl | rfl | ⟨i, rfl⟩
    · omega
    · omega
    · have := hr i
      cases h : up i
      · rw [hdown h]
        omega
      · rw [hup h]
        omega
  -- the lines are clean
  have hclean : ∀ e ∈ E, ∀ j, (∀ c ∈ t j, c.2 < e) ∨ ∀ c ∈ t j, e ≤ c.2 := by
    intro e he j
    rcases hE e he with rfl | rfl | ⟨i, rfl⟩
    · exact Or.inr fun c hc => (mem_R.1 (ht.subset_R j hc)).2.1
    · exact Or.inl fun c hc => (mem_R.1 (ht.subset_R j hc)).2.2
    · by_cases hji : j = i
      · subst hji
        cases h : up j
        · rw [hdown h]
          refine Or.inl fun c hc => ?_
          have := hside j c hc
          rw [h, ite_eq_right (by decide)] at this
          omega
        · rw [hup h]
          refine Or.inr fun c hc => ?_
          have := hside j c hc
          rwa [h, ite_eq_left rfl] at this
      · cases h : up i
        · rw [hdown h]
          rcases hsep i j hji with h' | h'
          · exact Or.inl fun c hc => (h' c hc).trans (lt_add_one _)
          · exact Or.inr fun c hc => h' c hc
        · rw [hup h]
          rcases hsep i j hji with h' | h'
          · exact Or.inl h'
          · exact Or.inr fun c hc => (h' c hc).le
  -- the tiles of a block: an up-type one has its bottom row, a down-type one its top row
  have hblock : ∀ e e', Consecutive E e e' → ∀ j, (∃ c ∈ t j, e ≤ c.2 ∧ c.2 < e') →
      (up j = true → r j = e) ∧ (up j = false → r j = e' - 1) ∧
        ∀ c ∈ t j, e ≤ c.2 ∧ c.2 < e' := by
    rintro e e' hee' j ⟨c, hc, h1, h2⟩
    have hin : ∀ p ∈ t j, e ≤ p.2 ∧ p.2 < e' := by
      intro p hp
      constructor
      · rcases hclean e hee'.1 j with h | h
        · have := h c hc
          omega
        · exact h p hp
      · rcases hclean e' hee'.2.1 j with h | h
        · exact h p hp
        · have := h c hc
          omega
    have hrj := hin _ (hfull j 0 le_rfl ha)
    dsimp only at hrj
    have hm := hee'.2.2.2 _ (hmE j)
    refine ⟨fun h => ?_, fun h => ?_, hin⟩
    · rw [hup h] at hm
      omega
    · rw [hdown h] at hm
      omega
  -- every block holds an up-type and a down-type tile
  have hboth : ∀ e e', Consecutive E e e' →
      (∃ i, up i = true ∧ r i = e) ∧ ∃ i, up i = false ∧ r i = e' - 1 := by
    intro e e' hee'
    have he := hEr e hee'.1
    have he' := hEr e' hee'.2.1
    have hlt := hee'.2.2.1
    obtain ⟨i, hi⟩ := ht.exists_tile (c := (0, e))
      (mem_R.2 ⟨⟨le_rfl, ha⟩, he.1, by dsimp only; omega⟩)
    have hbi := hblock e e' hee' i ⟨_, hi, le_rfl, hlt⟩
    -- the block is not one tile
    obtain ⟨c, hcB, hci⟩ : ∃ c ∈ Finset.Ico 0 a ×ˢ Finset.Ico e e', c ∉ t i := by
      by_contra hno
      push Not at hno
      refine ht.tile_not_isRectangular hnr i ?_
      have heq : t i = Finset.Ico 0 a ×ˢ Finset.Ico e e' := by
        refine Finset.Subset.antisymm (fun c hc => ?_) hno
        have h1 := (mem_R.1 (ht.subset_R i hc)).1
        have h2 := hbi.2.2 c hc
        rw [Finset.mem_product, Finset.mem_Ico, Finset.mem_Ico]
        exact ⟨h1, h2⟩
      rw [heq]
      exact isRectangular_product
    rw [Finset.mem_product, Finset.mem_Ico, Finset.mem_Ico] at hcB
    obtain ⟨j, hj⟩ := ht.exists_tile (c := c) (mem_R.2 ⟨hcB.1, by omega, by omega⟩)
    have hbj := hblock e e' hee' j ⟨_, hj, hcB.2.1, hcB.2.2⟩
    have hij : i ≠ j := by
      rintro rfl
      exact hci hj
    cases hui : up i <;> cases huj : up j
    · exact absurd (hrinj i j ((hbi.2.1 hui).trans (hbj.2.1 huj).symm)) hij
    · exact ⟨⟨j, huj, hbj.1 huj⟩, i, hui, hbi.2.1 hui⟩
    · exact ⟨⟨i, hui, hbi.1 hui⟩, j, huj, hbj.2.1 huj⟩
    · exact absurd (hrinj i j ((hbi.1 hui).trans (hbj.1 huj).symm)) hij
  -- count: up-type tiles against `E` without `b`, down-type tiles against `E` without 0
  have hinj : ∀ n : Bool, Set.InjOn m ↑(Finset.univ.filter fun i => up i = n) := by
    intro n i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
    refine hrinj i j ?_
    cases n
    · rw [hdown hi, hdown hj] at hij
      omega
    · rwa [hup hi, hup hj] at hij
  have hUp : (Finset.univ.filter fun i => up i = true).image m = E.erase b := by
    ext e
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨?_, hmE i⟩
      have := hr i
      rw [hup hi]
      omega
    · rintro ⟨hne, he⟩
      have := hEr e he
      obtain ⟨f, f', hff', h1, h2⟩ := exists_block (u := e) (v := e + 1) h0E hbE (by omega)
        (by omega) (by omega) fun n _ => by omega
      have hfe := hff'.2.2.2 e he
      obtain ⟨⟨i, hi, hri⟩, -⟩ := hboth f f' hff'
      exact ⟨i, hi, by rw [hup hi]; omega⟩
  have hDown : (Finset.univ.filter fun i => up i = false).image m = E.erase 0 := by
    ext e
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨?_, hmE i⟩
      have := hr i
      rw [hdown hi]
      omega
    · rintro ⟨hne, he⟩
      have := hEr e he
      obtain ⟨f, f', hff', h1, h2⟩ := exists_block (u := e - 1) (v := e) h0E hbE (by omega)
        (by omega) (by omega) fun n _ => by omega
      have hfe := hff'.2.2.2 e he
      obtain ⟨-, i, hi, hri⟩ := hboth f f' hff'
      exact ⟨i, hi, by rw [hdown hi]; omega⟩
  have h1 := Finset.card_image_of_injOn (hinj true)
  have h2 := Finset.card_image_of_injOn (hinj false)
  rw [hUp, Finset.card_erase_of_mem hbE] at h1
  rw [hDown, Finset.card_erase_of_mem h0E] at h2
  have h3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
    (fun i => up i = true)
  have h4 : (Finset.univ.filter fun i : Fin k => ¬ up i = true) =
      Finset.univ.filter fun i => up i = false := by simp
  rw [h4, Finset.card_univ, Fintype.card_fin, ← h1, ← h2] at h3
  exact ⟨_, h3.symm⟩


/-- Theorem 22, Step 3: blocks of two. Source: `report-4.md`, Theorem 22 (line 47),
and Theorem 41 (line 321): "Step 3 of Theorem 22 applies as it stands (it uses only
that T contains row 0 and a perpendicular full side of its square box)". So it is
stated for any frame, not only for type H1. -/
theorem Frame.even_of_full_column {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell}
    {i₀ : Fin k} {κ : Fin k → GridIso} (F : Frame a b d t i₀ κ) (hd : d = a)
    (hcol : (∀ y : ℤ, 0 ≤ y → y < a → (0, y) ∈ t i₀) ∨
      (∀ y : ℤ, 0 ≤ y → y < a → (a - 1, y) ∈ t i₀)) :
    Even k := by
  have ha := F.two_le
  have hd2 := F.two_le_d
  -- each tile has a full row of `R` on the bottom or the top side of its box
  have hrow : ∀ i, ∃ (r : ℤ) (u : Bool), (∀ x : ℤ, 0 ≤ x → x < a → (x, r) ∈ t i) ∧
      ∀ c ∈ t i, if u then r ≤ c.2 else c.2 ≤ r := by
    intro i
    cases hsw : (κ i).swap
    · obtain ⟨-, -, hfull, hside⟩ := F.horizontal_spine hsw
      refine ⟨(κ i).shift.2, !(κ i).negY, hfull, fun c hc => ?_⟩
      have := hside c hc
      cases hn : (κ i).negY
      · rw [hn, ite_eq_right (by decide)] at this
        exact this.1
      · rw [hn, ite_eq_left rfl] at this
        exact this.2
    · obtain ⟨-, -, hys, ⟨hx0, hxa⟩, -⟩ := F.vertical_spine hsw
      have hfull : ∀ x₀ : ℤ, (∀ y : ℤ, 0 ≤ y → y < a → (x₀, y) ∈ t i₀) →
          ∀ x : ℤ, 0 ≤ x → x < a →
            (x, (if (κ i).negY then -x₀ else x₀) + (κ i).shift.2) ∈ t i := by
        intro x₀ hx₀ x hx hx'
        rcases spine_end (κ i) d with ⟨hn, hs⟩ | ⟨hn, hs⟩
        · have := (F.vertical_mem hsw x₀ x).2 (hx₀ x hx hx')
          rwa [hn, ite_eq_right (by decide), show x + (κ i).shift.1 = x by omega] at this
        · have := (F.vertical_mem hsw x₀ (a - 1 - x)).2 (hx₀ _ (by omega) (by omega))
          rwa [hn, ite_eq_left rfl, show -(a - 1 - x) + (κ i).shift.1 = x by omega] at this
      rcases hcol with h | h <;> rcases spine_start (κ i) a with ⟨hn, hs⟩ | ⟨hn, hs⟩ <;>
        have hf := hfull _ h <;> rw [hn] at hf
      · refine ⟨_, true, hf, fun c hc => ?_⟩
        have := row_bounds hys hc
        simp
        omega
      · refine ⟨_, false, hf, fun c hc => ?_⟩
        have := row_bounds hys hc
        simp
        omega
      · refine ⟨_, false, hf, fun c hc => ?_⟩
        have := row_bounds hys hc
        simp
        omega
      · refine ⟨_, true, hf, fun c hc => ?_⟩
        have := row_bounds hys hc
        simp
        omega
  choose r up h using hrow
  exact even_of_end_rows F.poly F.nonrect F.isTiling (by omega) (by omega) r up
    (fun i => (h i).1) fun i => (h i).2

namespace TypeH1

variable {a b d : ℤ} {k : ℕ} {t : Fin k → Finset Cell} {i₀ : Fin k} {κ : Fin k → GridIso}

/-- Theorem 22. Source: `report-4.md`, section 1, Theorem 22 (line 41): "In this
setting, if d = a then k is even." -/
theorem theorem22 (H : TypeH1 a b d t i₀ κ) (hk : 2 ≤ k) (hd : d = a) : Even k :=
  H.frame.even_of_full_column hd (H.theorem22_full_column hk hd)

/-- Corollary 23, for every odd `k >= 3`. Source: `report-4.md`, Corollary 23
(line 53): "In case (II.2) of Theorem 6: 2 <= d < a and b >= a + 2. The same holds
for a 3-copy tiling in which a tile contains row 0 and the other two are
vertical." Proof: Theorem 22 excludes `d = a`, Theorem 10 excludes `b = a + 1`. -/
theorem corollary23 (H : TypeH1 a b d t i₀ κ) (hk : 3 ≤ k) (hodd : Odd k) :
    2 ≤ d ∧ d < a ∧ a + 2 ≤ b := by
  have hb := H.bounds (by omega)
  have h1 : d ≠ a := fun hd => (Nat.not_even_iff_odd.2 hodd) (H.theorem22 (by omega) hd)
  have h2 : b ≠ a + 1 := fun hb' => H.theorem10 hk hb'
  omega

end TypeH1

end PolyominoOddOrder
