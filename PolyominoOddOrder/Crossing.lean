module

public import PolyominoOddOrder.Tiling

/-!
# The crossing argument on the grid (`Crossing.lean`)

Blueprint unit X. The discrete replacement of the topological fact (F) of
`report.md` section 2, and with it Lemma 1 (interlacing), Corollary 1a
(crossing) and the Remark after Lemma 56 of `report-4.md` (the boundary of a
cut-off region). No topology is used: (F) is replaced by a parity count.

**The count.** Let `l` be a chain of cells of `R a b` from a boundary cell `p` to a
boundary cell `p'`. For a cell `c = (x, y)` not on `l`, count the steps of `l`
that go between the columns `x - 1` and `x` in a row below `y` (`crossCount`),
and add a correction for each end of `l` that lies in column 0 or in row 0
(`endCorr`). The parity `walkPot` of the total is the same at two adjacent
cells of `R a b` off `l` (`walkPot_adj`): a step of `l` enters or leaves the
part of column `x` below `c` only sideways, since `c` is not on `l`. On the
boundary of `R a b` the parity counts the ends of `l` passed on the way round
from the corner `(0, 0)` (`walkPot_boundary`). So two boundary cells off `l`
that are separated by exactly one end of `l` lie in different components of
`R a b` minus `l`: that is Lemma 1.

The three binding statements of this file, used by every other unit, are
`interlace` (Lemma 1), `crossing` (Corollary 1a) and `component_boundary`
(the Remark). The definitions `crossCount`, `endCorr`, `walkPot` and the two
statements about them are a proposed route, marked PROVISIONAL: the owner of
this file may replace them, as long as the binding statements stay.

Sources: `report.md` section 2, fact (F) (lines 54-66), Lemma 1 (lines 68-113),
Corollary 1a (lines 115-132); `report-4.md` section 7, Remark after Lemma 56
(line 503). Commit `e5ca51d`.
-/

@[expose] public section

namespace PolyominoOddOrder

/-! ## Boundary cells and their order round the rectangle -/

/-- `c` is a boundary cell of `R a b`. Source: `report.md`, Lemma 1 ("each
boundary cell c of R"). -/
def OnBoundary (a b : ℤ) (c : Cell) : Prop :=
  c ∈ R a b ∧ (c.1 = 0 ∨ c.1 = a - 1 ∨ c.2 = 0 ∨ c.2 = b - 1)

/-- The position of a boundary cell on the way round `R a b`, counterclockwise from
the corner `(0, 0)`: along the bottom row, up the right column, back along the
top row, down the left column. For `a, b >= 2` it is injective on boundary cells
and has the order of the exit points `e(c)` of `report.md`, Lemma 1, along the
boundary of `D`. -/
def bpos (a b : ℤ) (c : Cell) : ℤ :=
  if c.2 = 0 then c.1
  else if c.1 = a - 1 then (a - 1) + c.2
  else if c.2 = b - 1 then (a - 1) + (b - 1) + (a - 1 - c.1)
  else 2 * (a - 1) + (b - 1) + (b - 1 - c.2)

/-- Positions on the bottom row. -/
theorem bpos_bottom (a b x : ℤ) : bpos a b (x, 0) = x := by
  simp [bpos]

/-- Positions on the right column. -/
theorem bpos_right (a b y : ℤ) : bpos a b (a - 1, y) = a - 1 + y := by
  simp only [bpos]
  split_ifs <;> omega

/-- Positions on the top row. -/
theorem bpos_top {a b : ℤ} (hb : 2 ≤ b) (x : ℤ) :
    bpos a b (x, b - 1) = 2 * (a - 1) + (b - 1) - x := by
  simp only [bpos]
  split_ifs <;> omega

/-- Positions on the left column, without the corner `(0, 0)`. -/
theorem bpos_left {a b : ℤ} (ha : 2 ≤ a) {y : ℤ} (hy : y ≠ 0) :
    bpos a b (0, y) = 2 * (a - 1) + 2 * (b - 1) - y := by
  simp only [bpos]
  split_ifs <;> omega

/-- The four sides, as cases: a boundary cell is `(x, 0)`, `(a - 1, y)`, `(x, b - 1)`
or `(0, y)`, in this order of preference. -/
theorem OnBoundary.cases {a b : ℤ} {c : Cell} (hc : OnBoundary a b c) :
    (∃ x, c = (x, 0) ∧ 0 ≤ x ∧ x ≤ a - 1) ∨
      (∃ y, c = (a - 1, y) ∧ 0 < y ∧ y ≤ b - 1) ∨
      (∃ x, c = (x, b - 1) ∧ 0 ≤ x ∧ x < a - 1) ∨
      (∃ y, c = (0, y) ∧ 0 < y ∧ y < b - 1) := by
  obtain ⟨x, y⟩ := c
  obtain ⟨hR, h⟩ := hc
  rw [mem_R] at hR
  simp only [Prod.mk.injEq] at *
  by_cases h0 : y = 0
  · exact Or.inl ⟨x, ⟨rfl, h0⟩, by omega, by omega⟩
  by_cases h1 : x = a - 1
  · exact Or.inr (Or.inl ⟨y, ⟨h1, rfl⟩, by omega, by omega⟩)
  by_cases h2 : y = b - 1
  · exact Or.inr (Or.inr (Or.inl ⟨x, ⟨rfl, h2⟩, by omega, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨y, ⟨by omega, rfl⟩, by omega, by omega⟩))

/-- Positions are between `0` and `2 (a - 1) + 2 (b - 1)`. -/
theorem bpos_nonneg {a b : ℤ} (ha : 2 ≤ a) (hb : 2 ≤ b) {c : Cell} (hc : OnBoundary a b c) :
    0 ≤ bpos a b c := by
  rcases hc.cases with ⟨x, rfl, h⟩ | ⟨y, rfl, h⟩ | ⟨x, rfl, h⟩ | ⟨y, rfl, h⟩
  · rw [bpos_bottom]; omega
  · rw [bpos_right]; omega
  · rw [bpos_top hb]; omega
  · rw [bpos_left ha (by omega)]; omega

theorem bpos_le {a b : ℤ} (ha : 2 ≤ a) (hb : 2 ≤ b) {c : Cell} (hc : OnBoundary a b c) :
    bpos a b c ≤ 2 * (a - 1) + 2 * (b - 1) := by
  rcases hc.cases with ⟨x, rfl, h⟩ | ⟨y, rfl, h⟩ | ⟨x, rfl, h⟩ | ⟨y, rfl, h⟩
  · rw [bpos_bottom]; omega
  · rw [bpos_right]; omega
  · rw [bpos_top hb]; omega
  · rw [bpos_left ha (by omega)]; omega

/-- Distinct boundary cells have distinct positions ("Exit points of distinct
boundary cells are distinct", `report.md`, Lemma 1). -/
theorem bpos_injective {a b : ℤ} (ha : 2 ≤ a) (hb : 2 ≤ b) {p q : Cell}
    (hp : OnBoundary a b p) (hq : OnBoundary a b q) (h : bpos a b p = bpos a b q) : p = q := by
  rcases hp.cases with ⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩ | ⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩ <;>
    rcases hq.cases with ⟨x', rfl, hx'⟩ | ⟨y', rfl, hy'⟩ | ⟨x', rfl, hx'⟩ | ⟨y', rfl, hy'⟩ <;>
    (try simp only [bpos_bottom, bpos_right, bpos_top hb] at h) <;>
    (try rw [bpos_left ha (by omega : y ≠ 0)] at h) <;>
    (try rw [bpos_left ha (by omega : y' ≠ 0)] at h) <;>
    rw [Prod.mk.injEq] <;> omega

/-! ## The parity count (PROVISIONAL route to `exists_separation`) -/

/-- PROVISIONAL. The number of steps of the chain `l` that go between the columns
`x - 1` and `x`, in either direction, in a row below `y`. -/
def crossCount (l : List Cell) (x y : ℤ) : ℕ :=
  ((l.zip l.tail).filter fun uv =>
    decide (uv.1.2 = uv.2.2 ∧ uv.1.2 < y ∧
      ((uv.1.1 + 1 = x ∧ uv.2.1 = x) ∨ (uv.1.1 = x ∧ uv.2.1 + 1 = x)))).length

/-- PROVISIONAL. The correction for an end `e` of the chain: an end in column 0
counts for the cells of column 0 above it, an end in row 0 (outside column 0)
for the cells in the columns to its right. -/
def endCorr (e c : Cell) : ℕ :=
  if e.1 = 0 then (if c.1 = 0 ∧ e.2 < c.2 then 1 else 0)
  else if e.2 = 0 then (if e.1 < c.1 then 1 else 0)
  else 0

/-- PROVISIONAL. The count whose parity separates the two sides of the chain `l`
from `p` to `p'`. -/
def walkPot (l : List Cell) (p p' c : Cell) : ℕ :=
  crossCount l c.1 c.2 + endCorr p c + endCorr p' c

/-- The count of a chain, one step at a time. -/
theorem crossCount_cons_cons (u v : Cell) (l : List Cell) (x y : ℤ) :
    crossCount (u :: v :: l) x y = crossCount (v :: l) x y +
      (if u.2 = v.2 ∧ u.2 < y ∧ ((u.1 + 1 = x ∧ v.1 = x) ∨ (u.1 = x ∧ v.1 + 1 = x))
        then 1 else 0) := by
  simp only [crossCount, List.tail_cons, List.zip_cons_cons, List.filter_cons,
    decide_eq_true_eq]
  split_ifs <;> simp

theorem crossCount_singleton (u : Cell) (x y : ℤ) : crossCount [u] x y = 0 := by
  simp [crossCount]

/-- The count is 0 when no pair of cells of the chain is a step that counts. -/
theorem crossCount_eq_zero {l : List Cell} {x y : ℤ}
    (h : ∀ u ∈ l, ∀ v ∈ l, ¬ (u.2 = v.2 ∧ u.2 < y ∧
      ((u.1 + 1 = x ∧ v.1 = x) ∨ (u.1 = x ∧ v.1 + 1 = x)))) :
    crossCount l x y = 0 := by
  induction l with
  | nil => simp [crossCount]
  | cons u l ih =>
    cases l with
    | nil => exact crossCount_singleton u x y
    | cons v l =>
      rw [crossCount_cons_cons, ite_eq_right (h u (by simp) v (by simp)),
        ih fun u' hu' v' hv' => h u' (List.mem_cons_of_mem _ hu') v' (List.mem_cons_of_mem _ hv')]

/-- Going up by one past a cell off the chain does not change the count: a step in
row `y` between the columns `x - 1` and `x` has an end at `(x, y)`. -/
theorem crossCount_succ {l : List Cell} {x y : ℤ} (hc : (x, y) ∉ l) :
    crossCount l x (y + 1) = crossCount l x y := by
  induction l with
  | nil => simp [crossCount]
  | cons u l ih =>
    cases l with
    | nil => simp only [crossCount_singleton]
    | cons v l =>
      have hu : ¬ (u.1 = x ∧ u.2 = y) := fun h => hc (by
        rw [show (x, y) = u from Prod.ext h.1.symm h.2.symm]; simp)
      have hv : ¬ (v.1 = x ∧ v.2 = y) := fun h => hc (by
        rw [show (x, y) = v from Prod.ext h.1.symm h.2.symm]; simp)
      rw [crossCount_cons_cons, crossCount_cons_cons,
        ih fun h => hc (List.mem_cons_of_mem _ h)]
      congr 1
      split_ifs <;> omega

/-- A step of the chain enters or leaves the part of column `x` below `(x, y)` only
sideways, if `(x, y)` is off the chain; so the sideways steps on its two sides
together have the parity of the number of ends of the chain in that part. -/
theorem crossCount_column {l : List Cell} (hl : l.IsChain Adj) {x y : ℤ} (hc : (x, y) ∉ l)
    {p p' : Cell} (hhead : l.head? = some p) (hlast : l.getLast? = some p') :
    (crossCount l x y + crossCount l (x + 1) y) % 2 =
      ((if p.1 = x ∧ p.2 < y then 1 else 0) + (if p'.1 = x ∧ p'.2 < y then 1 else 0)) % 2 := by
  induction l generalizing p with
  | nil => simp at hhead
  | cons u l ih =>
    obtain rfl : u = p := by simpa using hhead
    cases l with
    | nil =>
      obtain rfl : u = p' := by simpa using hlast
      simp only [crossCount_singleton]
      split_ifs <;> rfl
    | cons v l =>
      have hu : ¬ (u.1 = x ∧ u.2 = y) := fun h => hc (by
        rw [show (x, y) = u from Prod.ext h.1.symm h.2.symm]; simp)
      have hv : ¬ (v.1 = x ∧ v.2 = y) := fun h => hc (by
        rw [show (x, y) = v from Prod.ext h.1.symm h.2.symm]; simp)
      rw [List.isChain_cons_cons] at hl
      have huv := hl.1
      have ih' := ih hl.2 (fun h => hc (List.mem_cons_of_mem _ h)) (p := v) rfl
        (by simpa using hlast)
      rw [crossCount_cons_cons, crossCount_cons_cons]
      generalize (if p'.1 = x ∧ p'.2 < y then 1 else 0) = k at ih' ⊢
      unfold Adj at huv
      split_ifs at ih' ⊢ <;> omega

/-- The same for the half plane right of the line between the columns `x - 1` and
`x`: if the chain stays in the rows up to `y` and avoids `(x, y)`, every step across
that line counts. -/
theorem crossCount_halfPlane {l : List Cell} (hl : l.IsChain Adj) {x y : ℤ}
    (hy : ∀ c ∈ l, c.2 ≤ y) (hc : (x, y) ∉ l) {p p' : Cell} (hhead : l.head? = some p)
    (hlast : l.getLast? = some p') :
    crossCount l x y % 2 =
      ((if x ≤ p.1 then 1 else 0) + (if x ≤ p'.1 then 1 else 0)) % 2 := by
  induction l generalizing p with
  | nil => simp at hhead
  | cons u l ih =>
    obtain rfl : u = p := by simpa using hhead
    cases l with
    | nil =>
      obtain rfl : u = p' := by simpa using hlast
      simp only [crossCount_singleton]
      split_ifs <;> rfl
    | cons v l =>
      have hu : ¬ (u.1 = x ∧ u.2 = y) := fun h => hc (by
        rw [show (x, y) = u from Prod.ext h.1.symm h.2.symm]; simp)
      have hv : ¬ (v.1 = x ∧ v.2 = y) := fun h => hc (by
        rw [show (x, y) = v from Prod.ext h.1.symm h.2.symm]; simp)
      have huy := hy u (by simp)
      rw [List.isChain_cons_cons] at hl
      have huv := hl.1
      have ih' := ih hl.2 (fun c h => hy c (List.mem_cons_of_mem _ h))
        (fun h => hc (List.mem_cons_of_mem _ h)) (p := v) rfl (by simpa using hlast)
      rw [crossCount_cons_cons]
      generalize (if x ≤ p'.1 then 1 else 0) = k at ih' ⊢
      unfold Adj at huv
      split_ifs at ih' ⊢ <;> omega

/-- The correction of an end at two horizontal neighbours: it changes exactly when
the end is in the part of column `x` below `(x, y)`. -/
theorem endCorr_column {a b : ℤ} {e : Cell} (he : OnBoundary a b e) {x y : ℤ}
    (hc : (x, y) ∈ R a b) (hd : (x + 1, y) ∈ R a b) (hne : e ≠ (x, y)) :
    (endCorr e (x, y) + endCorr e (x + 1, y)) % 2 =
      (if e.1 = x ∧ e.2 < y then 1 else 0) := by
  obtain ⟨e1, e2⟩ := e
  obtain ⟨heR, he⟩ := he
  rw [mem_R] at hc hd heR
  simp only [ne_eq, Prod.mk.injEq, endCorr] at *
  split_ifs <;> omega

/-- `walkPot_adj` for a cell and the cell above it. -/
theorem walkPot_up {l : List Cell} {p p' : Cell} (hp : p ∈ l) (hp' : p' ∈ l) {x y : ℤ}
    (hc : (x, y) ∉ l) : walkPot l p p' (x, y) = walkPot l p p' (x, y + 1) := by
  have key : ∀ e ∈ l, endCorr e (x, y) = endCorr e (x, y + 1) := by
    intro e he
    have hne : ¬ (e.1 = x ∧ e.2 = y) := fun h => hc (by
      rw [show (x, y) = e from Prod.ext h.1.symm h.2.symm]; exact he)
    simp only [endCorr]
    split_ifs <;> omega
  simp only [walkPot]
  rw [crossCount_succ hc, key p hp, key p' hp']

/-- `walkPot_adj` for a cell and the cell to its right. -/
theorem walkPot_right {a b : ℤ} {l : List Cell} (hl : l.IsChain Adj) {p p' : Cell}
    (hhead : l.head? = some p) (hlast : l.getLast? = some p') (hp : OnBoundary a b p)
    (hp' : OnBoundary a b p') {x y : ℤ} (hc : (x, y) ∈ R a b) (hd : (x + 1, y) ∈ R a b)
    (hcl : (x, y) ∉ l) : walkPot l p p' (x, y) % 2 = walkPot l p p' (x + 1, y) % 2 := by
  have h0 := crossCount_column hl hcl hhead hlast
  have h1 := endCorr_column hp hc hd fun h => hcl (h ▸ List.mem_of_mem_head? hhead)
  have h2 := endCorr_column hp' hc hd fun h => hcl (h ▸ List.mem_of_mem_getLast? hlast)
  simp only [walkPot]
  omega

/-- PROVISIONAL. The parity is the same at adjacent cells off the chain. This is
the step that replaces fact (F). Only the two cells and the two ends have to be in
`R a b`; the chain between its ends may be anywhere. -/
theorem walkPot_adj {a b : ℤ} {l : List Cell} (hl : l.IsChain Adj)
    {p p' : Cell} (hhead : l.head? = some p)
    (hlast : l.getLast? = some p') (hp : OnBoundary a b p) (hp' : OnBoundary a b p')
    {c d : Cell} (hc : c ∈ R a b) (hd : d ∈ R a b) (hcl : c ∉ l) (hdl : d ∉ l)
    (hcd : Adj c d) :
    walkPot l p p' c % 2 = walkPot l p p' d % 2 := by
  obtain ⟨x, y⟩ := c
  obtain ⟨x', y'⟩ := d
  have hpl := List.mem_of_mem_head? hhead
  have hpl' := List.mem_of_mem_getLast? hlast
  rw [adj_iff] at hcd
  rcases hcd with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩
  · rw [walkPot_up hpl hpl' hcl]
  · rw [walkPot_up hpl hpl' hdl]
  · exact walkPot_right hl hhead hlast hp hp' hc hd hcl
  · exact (walkPot_right hl hhead hlast hp hp' hd hc hdl).symm

/-- Whether the end `e` of the chain is passed before `q` on the way round, with
the corner `(0, 0)` passed last: the two summands of `walkPot_boundary`. -/
def passed (a b : ℤ) (e q : Cell) : ℕ :=
  if (if e = (0, 0) then 2 * (a - 1) + 2 * (b - 1) else bpos a b e) < bpos a b q
    then 1 else 0

/-- The end corrections on the bottom row. -/
theorem endCorr_bottom {a b : ℤ} (ha : 2 ≤ a) (hb : 2 ≤ b) {e : Cell} (he : OnBoundary a b e)
    {x : ℤ} (hx : 0 ≤ x) (hxa : x ≤ a - 1) : endCorr e (x, 0) = passed a b e (x, 0) := by
  simp only [passed, bpos_bottom]
  rcases he.cases with ⟨z, rfl, hz⟩ | ⟨z, rfl, hz⟩ | ⟨z, rfl, hz⟩ | ⟨z, rfl, hz⟩ <;>
    simp only [endCorr, bpos_bottom, bpos_right, bpos_top hb, Prod.mk.injEq, true_and,
      and_true, ↓reduceIte] <;>
    (try rw [bpos_left ha (by omega : z ≠ 0)]) <;>
    (try split_ifs) <;> omega

/-- The end corrections on the right column. -/
theorem endCorr_right {a b : ℤ} (ha : 2 ≤ a) (hb : 2 ≤ b) {e : Cell} (he : OnBoundary a b e)
    {y : ℤ} (hy : 0 < y) (hyb : y ≤ b - 1) :
    ((if e.1 = a - 1 ∧ e.2 < y then 1 else 0) + endCorr e (a - 1, y)) % 2 =
      passed a b e (a - 1, y) := by
  simp only [passed, bpos_right]
  rcases he.cases with ⟨z, rfl, hz⟩ | ⟨z, rfl, hz⟩ | ⟨z, rfl, hz⟩ | ⟨z, rfl, hz⟩ <;>
    simp only [endCorr, bpos_bottom, bpos_right, bpos_top hb, Prod.mk.injEq, true_and,
      and_true, ↓reduceIte] <;>
    (try rw [bpos_left ha (by omega : z ≠ 0)]) <;>
    (try split_ifs) <;> omega

/-- The end corrections on the top row. -/
theorem endCorr_top {a b : ℤ} (ha : 2 ≤ a) (hb : 2 ≤ b) {e : Cell} (he : OnBoundary a b e)
    {x : ℤ} (hx : 0 ≤ x) (hxa : x < a - 1) (hne : e ≠ (x, b - 1)) :
    ((if x ≤ e.1 then 1 else 0) + endCorr e (x, b - 1)) % 2 = passed a b e (x, b - 1) := by
  simp only [passed, bpos_top hb]
  rcases he.cases with ⟨z, rfl, hz⟩ | ⟨z, rfl, hz⟩ | ⟨z, rfl, hz⟩ | ⟨z, rfl, hz⟩ <;>
    simp only [ne_eq, endCorr, bpos_bottom, bpos_right, bpos_top hb, Prod.mk.injEq, true_and,
      and_true, ↓reduceIte] at hne ⊢ <;>
    (try rw [bpos_left ha (by omega : z ≠ 0)]) <;>
    (try split_ifs) <;> omega

/-- The end corrections on the left column: here both ends are counted on the other
side, which does not change the parity of the sum. -/
theorem endCorr_left {a b : ℤ} (ha : 2 ≤ a) (hb : 2 ≤ b) {e : Cell} (he : OnBoundary a b e)
    {y : ℤ} (hy : 0 < y) (hyb : y < b - 1) (hne : e ≠ (0, y)) :
    endCorr e (0, y) + passed a b e (0, y) = 1 := by
  simp only [passed, bpos_left ha (by omega : y ≠ 0)]
  rcases he.cases with ⟨z, rfl, hz⟩ | ⟨z, rfl, hz⟩ | ⟨z, rfl, hz⟩ | ⟨z, rfl, hz⟩ <;>
    simp only [ne_eq, endCorr, bpos_bottom, bpos_right, bpos_top hb, Prod.mk.injEq, true_and,
      and_true, ↓reduceIte] at hne ⊢ <;>
    (try rw [bpos_left ha (by omega : z ≠ 0)]) <;>
    (try split_ifs) <;> omega

/-- PROVISIONAL. On the boundary the parity counts the ends of the chain passed on
the way round from `(0, 0)`, where an end at `(0, 0)` itself counts as passed last
(position `2 (a - 1) + 2 (b - 1)`). The two ends may be equal. -/
theorem walkPot_boundary {a b : ℤ} (ha : 2 ≤ a) (hb : 2 ≤ b) {l : List Cell}
    (hl : l.IsChain Adj) (hlR : ∀ x ∈ l, x ∈ R a b) {p p' : Cell} (hhead : l.head? = some p)
    (hlast : l.getLast? = some p') (hp : OnBoundary a b p) (hp' : OnBoundary a b p')
    {q : Cell} (hq : OnBoundary a b q) (hql : q ∉ l) :
    walkPot l p p' q % 2 =
      ((if (if p = (0, 0) then 2 * (a - 1) + 2 * (b - 1) else bpos a b p) < bpos a b q
          then 1 else 0) +
        (if (if p' = (0, 0) then 2 * (a - 1) + 2 * (b - 1) else bpos a b p') < bpos a b q
          then 1 else 0)) % 2 := by
  have hpl := List.mem_of_mem_head? hhead
  have hpl' := List.mem_of_mem_getLast? hlast
  have hne : ∀ e ∈ l, e ≠ q := fun e he h => hql (h ▸ he)
  change walkPot l p p' q % 2 = (passed a b p q + passed a b p' q) % 2
  rcases hq.cases with ⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩ | ⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩
  · have h0 : crossCount l x 0 = 0 := crossCount_eq_zero fun u hu v _ h => by
      have := mem_R.1 (hlR u hu)
      omega
    simp only [walkPot, h0, endCorr_bottom ha hb hp hx.1 hx.2,
      endCorr_bottom ha hb hp' hx.1 hx.2, zero_add]
  · have h0 : crossCount l (a - 1 + 1) y = 0 := crossCount_eq_zero fun u hu v hv h => by
      have := mem_R.1 (hlR u hu)
      have := mem_R.1 (hlR v hv)
      omega
    have h1 := crossCount_column hl hql hhead hlast
    have h2 := endCorr_right ha hb hp hy.1 hy.2
    have h3 := endCorr_right ha hb hp' hy.1 hy.2
    simp only [walkPot]
    omega
  · have h1 := crossCount_halfPlane hl
      (fun c hc => by have := mem_R.1 (hlR c hc); omega) hql hhead hlast
    have h2 := endCorr_top ha hb hp hx.1 hx.2 (hne p hpl)
    have h3 := endCorr_top ha hb hp' hx.1 hx.2 (hne p' hpl')
    simp only [walkPot]
    omega
  · have h0 : crossCount l 0 y = 0 := crossCount_eq_zero fun u hu v hv h => by
      have := mem_R.1 (hlR u hu)
      have := mem_R.1 (hlR v hv)
      omega
    have h2 := endCorr_left ha hb hp hy.1 hy.2 (hne p hpl)
    have h3 := endCorr_left ha hb hp' hy.1 hy.2 (hne p' hpl')
    simp only [walkPot]
    omega

/-! ## Binding statements -/

/-- A connected set through two boundary cells `p`, `p'` separates the boundary
cells strictly between them from the others: there is a two-valued function,
constant along adjacent cells off `S`, that is `true` on a boundary cell off `S`
exactly when its position is strictly between those of `p` and `p'`. This is
fact (F) and Lemma 1 of `report.md` in one grid statement. -/
theorem exists_separation {a b : ℤ} (ha : 2 ≤ a) (hb : 2 ≤ b) {S : Finset Cell}
    (hSR : S ⊆ R a b) (hS : EdgeConnected S) {p p' : Cell} (hp : OnBoundary a b p)
    (hp' : OnBoundary a b p') (hpS : p ∈ S) (hp'S : p' ∈ S)
    (hlt : bpos a b p < bpos a b p') :
    ∃ β : Cell → Bool,
      (∀ c d, c ∈ R a b → d ∈ R a b → c ∉ S → d ∉ S → Adj c d → β c = β d) ∧
      ∀ q, OnBoundary a b q → q ∉ S →
        (β q = true ↔ bpos a b p < bpos a b q ∧ bpos a b q < bpos a b p') := by
  obtain ⟨l, hhead, hlast, hlS, hl⟩ := Reach.exists_walk hpS (hS p hpS p' hp'S)
  have hlR : ∀ x ∈ l, x ∈ R a b := fun x hx => hSR (hlS x hx)
  have hoff : ∀ c, c ∉ S → c ∉ l := fun c hc h => hc (hlS c h)
  have h0 := bpos_nonneg ha hb hp
  have hp'0 : p' ≠ (0, 0) := by
    rintro rfl
    rw [bpos_bottom] at hlt
    omega
  have hadj : ∀ c d, c ∈ R a b → d ∈ R a b → c ∉ S → d ∉ S → Adj c d →
      walkPot l p p' c % 2 = walkPot l p p' d % 2 := fun c d hc hd hcS hdS hcd =>
    walkPot_adj hl hhead hlast hp hp' hc hd (hoff c hcS) (hoff d hdS) hcd
  have hbd : ∀ q, OnBoundary a b q → q ∉ S → bpos a b q ≠ bpos a b p ∧
      bpos a b q ≠ bpos a b p' := fun q hq hqS =>
    ⟨fun h => hqS (bpos_injective ha hb hq hp h ▸ hpS),
      fun h => hqS (bpos_injective ha hb hq hp' h ▸ hp'S)⟩
  by_cases hp0 : p = (0, 0)
  · refine ⟨fun c => decide (walkPot l p p' c % 2 = 0), fun c d hc hd hcS hdS hcd => ?_,
      fun q hq hqS => ?_⟩
    · simp only [hadj c d hc hd hcS hdS hcd]
    · have h1 := walkPot_boundary ha hb hl hlR hhead hlast hp hp' hq (hoff q hqS)
      have h2 := bpos_nonneg ha hb hq
      have h3 := hbd q hq hqS
      have h4 : bpos a b q ≤ 2 * (a - 1) + 2 * (b - 1) := bpos_le ha hb hq
      have h5 : bpos a b p = 0 := by rw [hp0, bpos_bottom]
      rw [ite_eq_left hp0, ite_eq_right hp'0] at h1
      rw [decide_eq_true_iff]
      generalize walkPot l p p' q = k at h1 ⊢
      split_ifs at h1 <;> omega
  · refine ⟨fun c => decide (walkPot l p p' c % 2 = 1), fun c d hc hd hcS hdS hcd => ?_,
      fun q hq hqS => ?_⟩
    · simp only [hadj c d hc hd hcS hdS hcd]
    · have h1 := walkPot_boundary ha hb hl hlR hhead hlast hp hp' hq (hoff q hqS)
      have h3 := hbd q hq hqS
      rw [ite_eq_right hp0, ite_eq_right hp'0] at h1
      rw [decide_eq_true_iff]
      generalize walkPot l p p' q = k at h1 ⊢
      split_ifs at h1 <;> omega

/-- Two boundary cells joined by a chain off `S` are on the same side of `S`: the
common form of Lemma 1 and of the Remark after Lemma 56. -/
theorem between_iff_of_reach {a b : ℤ} (ha : 2 ≤ a) (hb : 2 ≤ b) {S : Finset Cell}
    (hSR : S ⊆ R a b) (hS : EdgeConnected S) {p p' : Cell} (hp : OnBoundary a b p)
    (hp' : OnBoundary a b p') (hpS : p ∈ S) (hp'S : p' ∈ S)
    (hlt : bpos a b p < bpos a b p') {q q' : Cell} (hq : OnBoundary a b q)
    (hq' : OnBoundary a b q') (hqS : q ∉ S) (h : Reach (R a b \ S) q q') :
    (bpos a b p < bpos a b q ∧ bpos a b q < bpos a b p') ↔
      (bpos a b p < bpos a b q' ∧ bpos a b q' < bpos a b p') := by
  obtain ⟨β, hβ, hβb⟩ := exists_separation ha hb hSR hS hp hp' hpS hp'S hlt
  have hconst : ∀ {c : Cell}, Reach (R a b \ S) q c → β q = β c := by
    intro c hc
    induction hc with
    | refl => rfl
    | tail _ hbc ih =>
      obtain ⟨h1, h2, h3⟩ := hbc
      rw [Finset.mem_sdiff] at h1 h2
      exact ih.trans (hβ _ _ h1.1 h2.1 h1.2 h2.2 h3)
  have hq'S : q' ∉ S :=
    (Finset.mem_sdiff.1 (h.mem_right (Finset.mem_sdiff.2 ⟨hq.1, hqS⟩))).2
  rw [← hβb q hq hqS, ← hβb q' hq' hq'S, hconst h]

/-- The same for two cells of a connected set that does not meet `S`. -/
theorem between_iff_of_not_meets {a b : ℤ} (ha : 2 ≤ a) (hb : 2 ≤ b) {S S' : Finset Cell}
    (hSR : S ⊆ R a b) (hS : EdgeConnected S) (hS'R : S' ⊆ R a b) (hS' : EdgeConnected S')
    {p p' q q' : Cell} (hp : OnBoundary a b p) (hp' : OnBoundary a b p') (hpS : p ∈ S)
    (hp'S : p' ∈ S) (hlt : bpos a b p < bpos a b p') (hq : OnBoundary a b q)
    (hq' : OnBoundary a b q') (hqS' : q ∈ S') (hq'S' : q' ∈ S') (h : ¬ Meets S S') :
    (bpos a b p < bpos a b q ∧ bpos a b q < bpos a b p') ↔
      (bpos a b p < bpos a b q' ∧ bpos a b q' < bpos a b p') := by
  have hsub : S' ⊆ R a b \ S := fun c hc =>
    Finset.mem_sdiff.2 ⟨hS'R hc, fun hcS => h ⟨c, hcS, hc⟩⟩
  exact between_iff_of_reach ha hb hSR hS hp hp' hpS hp'S hlt hq hq'
    (fun hqS => h ⟨q, hqS, hqS'⟩) (Reach.mono hsub (hS' q hqS' q' hq'S'))

/-- Lemma 1 (interlacing). Source: `report.md`, section 2, Lemma 1 (lines 76-79):

> Let p, q, p', q' be four distinct boundary cells of R whose exit points
> occur in the cyclic order e(p), e(q), e(p'), e(q') along the boundary of D. If S and
> S' are connected subsets of R with p, p' in S and q, q' in S', then S and S' share a
> cell.

The cyclic order is given by positions: `p`, `q`, `p'`, `q'` in increasing
position. Every cyclic order of four distinct boundary cells in which the pairs
alternate is of this form after exchanging `S` with `S'` or `p` with `p'`. -/
theorem interlace {a b : ℤ} (ha : 2 ≤ a) (hb : 2 ≤ b) {S S' : Finset Cell}
    (hSR : S ⊆ R a b) (hS : EdgeConnected S) (hS'R : S' ⊆ R a b) (hS' : EdgeConnected S')
    {p q p' q' : Cell} (hp : OnBoundary a b p) (hq : OnBoundary a b q)
    (hp' : OnBoundary a b p') (hq' : OnBoundary a b q') (hpS : p ∈ S) (hp'S : p' ∈ S)
    (hqS' : q ∈ S') (hq'S' : q' ∈ S') (h1 : bpos a b p < bpos a b q)
    (h2 : bpos a b q < bpos a b p') (h3 : bpos a b p' < bpos a b q') :
    Meets S S' := by
  by_contra h
  have := between_iff_of_not_meets ha hb hSR hS hS'R hS' hp hp' hpS hp'S (h1.trans h2) hq hq'
    hqS' hq'S' h
  omega

/-- Corollary 1a (crossing): the internal statement behind the frozen
`corollary1a_crossing`. Source: `report.md`, section 2, Corollary 1a
(lines 117-119). -/
theorem crossing (a b : ℤ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (S S' : Finset Cell) (hSR : S ⊆ R a b) (hS : EdgeConnected S)
    (hSl : Meets S (leftCol a b)) (hSr : Meets S (rightCol a b))
    (hS'R : S' ⊆ R a b) (hS' : EdgeConnected S')
    (hS'b : Meets S' (bottomRow a b)) (hS't : Meets S' (topRow a b)) :
    Meets S S' := by
  obtain ⟨⟨xl, y₁⟩, hl, hl'⟩ := hSl
  obtain ⟨⟨xr, y₂⟩, hr, hr'⟩ := hSr
  obtain ⟨⟨x₁, yb⟩, hbo, hbo'⟩ := hS'b
  obtain ⟨⟨x₂, yt⟩, hto, hto'⟩ := hS't
  rw [mem_leftCol] at hl'
  rw [mem_rightCol] at hr'
  rw [mem_bottomRow] at hbo'
  rw [mem_topRow] at hto'
  obtain ⟨hlR, rfl⟩ := hl'
  obtain ⟨hrR, rfl⟩ := hr'
  obtain ⟨hbR, rfl⟩ := hbo'
  obtain ⟨htR, rfl⟩ := hto'
  have Hl : OnBoundary a b (0, y₁) := ⟨hlR, Or.inl rfl⟩
  have Hr : OnBoundary a b (a - 1, y₂) := ⟨hrR, Or.inr (Or.inl rfl)⟩
  have Hb : OnBoundary a b (x₁, 0) := ⟨hbR, Or.inr (Or.inr (Or.inl rfl))⟩
  have Ht : OnBoundary a b (x₂, b - 1) := ⟨htR, Or.inr (Or.inr (Or.inr rfl))⟩
  rw [mem_R] at hlR hrR hbR htR
  simp only at hlR hrR hbR htR
  by_contra hm
  have hne : ∀ c ∈ S, ∀ d ∈ S', c ≠ d := fun c hc d hd h => hm ⟨c, hc, h ▸ hd⟩
  have n1 := hne _ hl _ hbo
  have n2 := hne _ hl _ hto
  have n3 := hne _ hr _ hbo
  have n4 := hne _ hr _ hto
  simp only [ne_eq, Prod.mk.injEq] at n1 n2 n3 n4
  by_cases hy : y₁ = 0
  · subst hy
    refine hm (interlace ha hb hSR hS hS'R hS' Hl Hb Hr Ht hl hr hbo hto ?_ ?_ ?_) <;>
      simp only [bpos_bottom, bpos_right, bpos_top hb] <;> omega
  · refine hm (Meets.symm (interlace ha hb hS'R hS' hSR hS Hb Hr Ht Hl hbo hto hr hl ?_ ?_ ?_)) <;>
      simp only [bpos_bottom, bpos_right, bpos_top hb, bpos_left ha hy] <;> omega

/-- Corollary 1a in a rectangle that does not start at the origin. Source:
`report-4.md`, Theorem 22, Step 1 ("By Corollary 1a, applied to S", the square
`[0, a) x [b - a, b)`). -/
theorem crossing_translate (x₀ y₀ a b : ℤ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (S S' : Finset Cell) (hSR : S ⊆ Finset.Ico x₀ (x₀ + a) ×ˢ Finset.Ico y₀ (y₀ + b))
    (hS : EdgeConnected S) (hSl : ∃ y, (x₀, y) ∈ S) (hSr : ∃ y, (x₀ + a - 1, y) ∈ S)
    (hS'R : S' ⊆ Finset.Ico x₀ (x₀ + a) ×ˢ Finset.Ico y₀ (y₀ + b))
    (hS' : EdgeConnected S') (hS'b : ∃ x, (x, y₀) ∈ S') (hS't : ∃ x, (x, y₀ + b - 1) ∈ S') :
    Meets S S' := by
  obtain ⟨yl, hl⟩ := hSl
  obtain ⟨yr, hr⟩ := hSr
  obtain ⟨xb, hbo⟩ := hS'b
  obtain ⟨xt, hto⟩ := hS't
  have hsub : ∀ {A : Finset Cell}, A ⊆ Finset.Ico x₀ (x₀ + a) ×ˢ Finset.Ico y₀ (y₀ + b) →
      A.image (GridIso.translate (-x₀, -y₀)).apply ⊆ R a b := by
    intro A hA c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hc
    have := hA hd
    rw [Finset.mem_product, Finset.mem_Ico, Finset.mem_Ico] at this
    rw [GridIso.translate_apply, mem_R]
    simp only
    omega
  have hmem : ∀ {A : Finset Cell} {x y : ℤ}, (x, y) ∈ A →
      (x - x₀, y - y₀) ∈ A.image (GridIso.translate (-x₀, -y₀)).apply := by
    intro A x y h
    refine Finset.mem_image.2 ⟨(x, y), h, ?_⟩
    rw [GridIso.translate_apply]
    simp only [Prod.mk.injEq]
    omega
  have Hl := hmem hl
  have Hr := hmem hr
  have Hb := hmem hbo
  have Ht := hmem hto
  obtain ⟨c, hc, hc'⟩ := crossing a b ha hb _ _ (hsub hSR)
    (GridIso.edgeConnected_image (GridIso.translate (-x₀, -y₀)) hS)
    ⟨_, Hl, mem_leftCol.2 ⟨hsub hSR Hl, by simp only; omega⟩⟩
    ⟨_, Hr, mem_rightCol.2 ⟨hsub hSR Hr, by simp only; omega⟩⟩ (hsub hS'R)
    (GridIso.edgeConnected_image (GridIso.translate (-x₀, -y₀)) hS')
    ⟨_, Hb, mem_bottomRow.2 ⟨hsub hS'R Hb, by simp only; omega⟩⟩
    ⟨_, Ht, mem_topRow.2 ⟨hsub hS'R Ht, by simp only; omega⟩⟩
  obtain ⟨d, hd, hdc⟩ := Finset.mem_image.1 hc
  obtain ⟨d', hd', hdc'⟩ := Finset.mem_image.1 hc'
  have : d = d' := GridIso.apply_injective _ (hdc.trans hdc'.symm)
  exact ⟨d, hd, this ▸ hd'⟩

/-- Lemma 1 on one side, bottom: a connected set through `(x₁, 0)` and `(x₃, 0)`
meets every connected set through `(x₂, 0)`, `x₁ < x₂ < x₃`, and through a
boundary cell that is not on the bottom row strictly between `x₁` and `x₃`.
Source: `report.md`, Lemma 3 (i), (ii); `report-4.md`, Proposition 57 (a). -/
theorem interlace_bottom {a b : ℤ} (ha : 2 ≤ a) (hb : 2 ≤ b) {S S' : Finset Cell}
    (hSR : S ⊆ R a b) (hS : EdgeConnected S) (hS'R : S' ⊆ R a b) (hS' : EdgeConnected S')
    {x₁ x₂ x₃ : ℤ} (h12 : x₁ < x₂) (h23 : x₂ < x₃) (h1 : (x₁, 0) ∈ S) (h3 : (x₃, 0) ∈ S)
    (h2 : (x₂, 0) ∈ S') {q' : Cell} (hq' : OnBoundary a b q') (hq'S' : q' ∈ S')
    (hout : ¬ (q'.2 = 0 ∧ x₁ < q'.1 ∧ q'.1 < x₃)) :
    Meets S S' := by
  by_contra hm
  have hR1 := mem_R.1 (hSR h1)
  have hR3 := mem_R.1 (hSR h3)
  simp only at hR1 hR3
  have H : ∀ {x : ℤ}, 0 ≤ x → x < a → OnBoundary a b (x, 0) := fun h h' =>
    ⟨mem_R.2 ⟨⟨h, h'⟩, by simp only; omega, by simp only; omega⟩, Or.inr (Or.inr (Or.inl rfl))⟩
  have key := between_iff_of_not_meets ha hb hSR hS hS'R hS' (H hR1.1.1 hR1.1.2)
    (H hR3.1.1 hR3.1.2) h1 h3 (by simp only [bpos_bottom]; omega)
    (H (by omega : 0 ≤ x₂) (by omega)) hq' h2 hq'S' hm
  simp only [bpos_bottom] at key
  have hb' := key.1 ⟨h12, h23⟩
  rcases hq'.cases with ⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩ | ⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩
  · rw [bpos_bottom] at hb'
    exact hout ⟨rfl, hb'⟩
  · rw [bpos_right] at hb'
    omega
  · rw [bpos_top hb] at hb'
    omega
  · rw [bpos_left ha (by omega)] at hb'
    omega

/-- Lemma 1 on one side, left: the same on the left column. Source: `report-4.md`,
Lemma 32 (a), (b), Lemma 36 (b), Lemma 40 (a), Lemma 43 (a). -/
theorem interlace_left {a b : ℤ} (ha : 2 ≤ a) (hb : 2 ≤ b) {S S' : Finset Cell}
    (hSR : S ⊆ R a b) (hS : EdgeConnected S) (hS'R : S' ⊆ R a b) (hS' : EdgeConnected S')
    {y₁ y₂ y₃ : ℤ} (h12 : y₁ < y₂) (h23 : y₂ < y₃) (h1 : (0, y₁) ∈ S) (h3 : (0, y₃) ∈ S)
    (h2 : (0, y₂) ∈ S') {q' : Cell} (hq' : OnBoundary a b q') (hq'S' : q' ∈ S')
    (hout : ¬ (q'.1 = 0 ∧ y₁ < q'.2 ∧ q'.2 < y₃)) :
    Meets S S' := by
  by_contra hm
  have hR1 := mem_R.1 (hSR h1)
  have hR3 := mem_R.1 (hSR h3)
  simp only at hR1 hR3
  have H : ∀ {y : ℤ}, 0 ≤ y → y < b → OnBoundary a b (0, y) := fun h h' =>
    ⟨mem_R.2 ⟨by simp only; omega, h, h'⟩, Or.inl rfl⟩
  have B1 := H hR1.2.1 hR1.2.2
  have B2 := H (by omega : 0 ≤ y₂) (by omega)
  have B3 := H hR3.2.1 hR3.2.2
  have p2 := bpos_left (b := b) ha (by omega : y₂ ≠ 0)
  have p3 := bpos_left (b := b) ha (by omega : y₃ ≠ 0)
  have hne1 : q' ≠ (0, y₁) := fun h => hm ⟨_, h1, h ▸ hq'S'⟩
  have hne3 : q' ≠ (0, y₃) := fun h => hm ⟨_, h3, h ▸ hq'S'⟩
  by_cases hy1 : y₁ = 0
  · subst hy1
    have key := between_iff_of_not_meets ha hb hSR hS hS'R hS' B1 B3 h1 h3
      (by rw [bpos_bottom, p3]; omega) B2 hq' h2 hq'S' hm
    rw [bpos_bottom, p2, p3] at key
    have hb' : ¬ (0 < bpos a b q' ∧ bpos a b q' < 2 * (a - 1) + 2 * (b - 1) - y₃) := fun h => by
      have := key.2 h
      omega
    rcases hq'.cases with ⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩ | ⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩ <;>
      simp only [ne_eq, Prod.mk.injEq, true_and, and_true] at hne1 hne3 hout
    · rw [bpos_bottom] at hb'
      omega
    · rw [bpos_right] at hb'
      omega
    · rw [bpos_top hb] at hb'
      omega
    · rw [bpos_left ha (by omega)] at hb'
      omega
  · have p1 := bpos_left (b := b) ha hy1
    have key := between_iff_of_not_meets ha hb hSR hS hS'R hS' B3 B1 h3 h1
      (by rw [p1, p3]; omega) B2 hq' h2 hq'S' hm
    rw [p1, p2, p3] at key
    have hb' := key.1 (by omega)
    rcases hq'.cases with ⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩ | ⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩ <;>
      simp only [true_and] at hout
    · rw [bpos_bottom] at hb'
      omega
    · rw [bpos_right] at hb'
      omega
    · rw [bpos_top hb] at hb'
      omega
    · rw [bpos_left ha (by omega)] at hb'
      omega

/-- The boundary of a cut-off region. Source: `report-4.md`, section 7, Remark
after Lemma 56 (line 503):

> Every boundary cell of R in Omega lies in A: a boundary cell q' outside A and not
> on gamma has e(p), e(q), e(p'), e(q') in cyclic order, and a path in Omega from q to
> q' would be a connected set disjoint from the connected set gamma, against Lemma 1.

Here the path `gamma` is replaced by the whole connected set `S` (a tile): the
component of `q` in `R a b` minus `S` is smaller than in `R a b` minus `gamma`, and
the statement is what Lemma 56 needs. `q` is strictly between `p` and `p'`, and so
is every boundary cell of its component. -/
theorem component_boundary {a b : ℤ} (ha : 2 ≤ a) (hb : 2 ≤ b) {S : Finset Cell}
    (hSR : S ⊆ R a b) (hS : EdgeConnected S) {p p' q q' : Cell} (hp : OnBoundary a b p)
    (hp' : OnBoundary a b p') (hpS : p ∈ S) (hp'S : p' ∈ S) (hq : OnBoundary a b q)
    (hqS : q ∉ S) (h1 : bpos a b p < bpos a b q) (h2 : bpos a b q < bpos a b p')
    (hq' : OnBoundary a b q') (hq'c : q' ∈ component (R a b \ S) q) :
    bpos a b p < bpos a b q' ∧ bpos a b q' < bpos a b p' := by
  exact (between_iff_of_reach ha hb hSR hS hp hp' hpS hp'S (h1.trans h2) hq hq' hqS
    (mem_component.1 hq'c).2).1 ⟨h1, h2⟩

/-- The boundary of a cut-off region, the other arc: if `q` is not between `p` and
`p'`, neither is any boundary cell of its component. Used for the regions that
hold the corner `(0, 0)` (`report-4.md`, Corollary 59, with `p` on the bottom row
and `p'` on the left column). -/
theorem component_boundary_outer {a b : ℤ} (ha : 2 ≤ a) (hb : 2 ≤ b) {S : Finset Cell}
    (hSR : S ⊆ R a b) (hS : EdgeConnected S) {p p' q q' : Cell} (hp : OnBoundary a b p)
    (hp' : OnBoundary a b p') (hpS : p ∈ S) (hp'S : p' ∈ S) (hpp' : bpos a b p < bpos a b p')
    (hq : OnBoundary a b q) (hqS : q ∉ S)
    (h : bpos a b q < bpos a b p ∨ bpos a b p' < bpos a b q)
    (hq' : OnBoundary a b q') (hq'c : q' ∈ component (R a b \ S) q) :
    bpos a b q' < bpos a b p ∨ bpos a b p' < bpos a b q' := by
  have key := between_iff_of_reach ha hb hSR hS hp hp' hpS hp'S hpp' hq hq' hqS
    (mem_component.1 hq'c).2
  have hq'S : q' ∉ S := (Finset.mem_sdiff.1 (mem_component.1 hq'c).1).2
  have n1 : bpos a b q' ≠ bpos a b p := fun e => hq'S (bpos_injective ha hb hq' hp e ▸ hpS)
  have n2 : bpos a b q' ≠ bpos a b p' := fun e => hq'S (bpos_injective ha hb hq' hp' e ▸ hp'S)
  omega

end PolyominoOddOrder
