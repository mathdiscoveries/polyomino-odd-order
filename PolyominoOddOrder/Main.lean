module

public import PolyominoOddOrder.SearchBridge
public import PolyominoOddOrder.CaseIOpposite
public import PolyominoOddOrder.CaseIClosure

/-!
# The frozen statements, proved (`Main.lean`)

The frozen statements of `Spec.lean` under the Spec's names, each copied character
for character from the Spec by `tools/gen_main.py` (see `BLUEPRINT.md`, section
"Comparator") and proved from the internal statement of the library that
carries the mathematics. No proof unit edits this file: a unit proves the
internal statements, and the lines below do not change.

This module and `Spec.lean` declare the same names and are never imported
together.
-/

@[expose] public section

-- The statements are the Spec's, binder for binder; a statement may hold without
-- one of its hypotheses, which the linter would report.
set_option linter.unusedVariables false

namespace PolyominoOddOrder

/-- (a) Corollary 1a (crossing). Source: `report.md`, section 2, Corollary 1a
(lines 117-119), commit `e5ca51d`:

> Let a, b >= 2. If S is a connected subset of R meeting both the left and the right
> column, and S' is a connected subset of R meeting both the bottom and the top row,
> then S and S' share a cell.

"Connected subset of R" is read as `S ⊆ R a b` with `EdgeConnected S`; "meets the
left column" as `Meets S (leftCol a b)`, and so on. -/
theorem corollary1a_crossing (a b : ℤ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (S S' : Finset Cell) (hSR : S ⊆ R a b) (hS : EdgeConnected S)
    (hSl : Meets S (leftCol a b)) (hSr : Meets S (rightCol a b))
    (hS'R : S' ⊆ R a b) (hS' : EdgeConnected S')
    (hS'b : Meets S' (bottomRow a b)) (hS't : Meets S' (topRow a b)) :
    Meets S S' :=
  crossing a b ha hb S S' hSR hS hSl hSr hS'R hS' hS'b hS't

/-- (b) Lemma 2 (no tile holds two opposite corners). Source: `report.md`,
section 2, Lemma 2 (line 136), commit `e5ca51d`:

> No tile contains two opposite corner cells of R.

under the standing assumptions of sections 2 and 3 (`report.md`, lines 47-48):

> Standing assumptions for sections 2 and 3: P is a polyomino, k >= 2, and T_1, ..., T_k
> is a k-copy tiling of R(a, b) by P. Where P is assumed non-rectangular this is said.

The two pairs of opposite corner cells are `(0, 0)`, `(a - 1, b - 1)` and
`(a - 1, 0)`, `(0, b - 1)`. No bound on `a`, `b` is assumed beyond the tiling. -/
theorem lemma2_no_opposite_corners (P : Finset Cell) (hP : IsPolyomino P)
    (k : ℕ) (hk : 2 ≤ k) (a b : ℤ) (t : Fin k → Finset Cell) (ht : IsTiling P a b t)
    (i : Fin k) :
    ¬ ((0, 0) ∈ t i ∧ (a - 1, b - 1) ∈ t i) ∧ ¬ ((a - 1, 0) ∈ t i ∧ (0, b - 1) ∈ t i) :=
  no_opposite_corners P hP k hk a b t ht i

/-- (c) Lemma 3 (two adjacent corners force the whole side). Source: `report.md`,
section 2, Lemma 3 (lines 147-148), commit `e5ca51d`:

> Suppose a tile T contains the two corner cells (0, 0) and (a - 1, 0). Then T contains
> every cell of row 0.

under the standing assumptions of sections 2 and 3 (`report.md`, lines 47-48):
`P` is a polyomino, `k ≥ 2`, and `t` is a `k`-copy tiling of `R a b` by `P`.
"Every cell of row 0" of `R a b` is every `(x, 0)` with `0 ≤ x < a`. As in the
report, only the bottom side is stated; the other sides are its images under the
symmetries of the rectangle and are not separate statements here. -/
theorem lemma3_adjacent_corners_full_row (P : Finset Cell) (hP : IsPolyomino P)
    (k : ℕ) (hk : 2 ≤ k) (a b : ℤ) (t : Fin k → Finset Cell) (ht : IsTiling P a b t)
    (i : Fin k) (h0 : (0, 0) ∈ t i) (h1 : (a - 1, 0) ∈ t i)
    (x : ℤ) (hx0 : 0 ≤ x) (hxa : x < a) :
    (x, 0) ∈ t i :=
  adjacent_corners_full_row P hP k hk a b t ht i h0 h1 x hx0 hxa

/-- (d) Theorem 62 (three copies). Source: `report-4.md`, section 8, Theorem 62
(line 589), commit `e5ca51d`:

> No rectangle is tiled by exactly three congruent non-rectangular polyominoes (grid isometries, reflections included).

"A rectangle" is read as `R a b` for integers `a`, `b`: every rectangle of cells
is a translate of one of these, and congruence is invariant under translation.
"Three congruent non-rectangular polyominoes" is read as three tiles each
congruent to one non-rectangular polyomino `P`.

This is printed prior work, credited to S. J. Maltby, "Trisecting a rectangle",
J. Combin. Theory Ser. A 66 (1994). `report.md`, section 3 (lines 323-326),
commit `e5ca51d`:

> Maltby's paper has since been read in full: its Theorem (p. 40) is the statement above, for
> all rectangles, reflections allowed, and polyomino tiles meet its conditions on pieces
> (`prior-work/three-copy-theorem.md`). Report 4, Theorem 62, proves the polyomino case
> independently.

The statement is kept as `report-4.md` prints it; the pod's own proof is a
second route, not a new result. -/
theorem theorem62_no_three_copy_tiling (P : Finset Cell) (hP : IsPolyomino P)
    (hnr : ¬ IsRectangular P) (a b : ℤ) (t : Fin 3 → Finset Cell) :
    ¬ IsTiling P a b t :=
  three_copy P hP hnr a b t

/-- (h) Theorem 21 (what a search without hits proves): the bridge from the
search families to 3- and 5-copy tilings. Source: `report-3.md`, section 2,
Theorem 21 (lines 164-167), commit `e5ca51d`:

> Fix n. Suppose that, over all rectangles and boxes allowed in section 1, no tuple of
> I(5), H1(5), H2(5), H1(3), H2(3) has a proper solution that is not a rectangle. Then
> no rectangle is tiled by exactly 3, and none by exactly 5, congruent copies of a
> non-rectangular polyomino with n cells.

and its Remark (lines 175-177):

> *Remark.* The hypothesis of Theorem 21 is about proper solutions in the given
> families, with every box, not only B = box(P).

"Over all rectangles and boxes" is the quantifier over the integers `a`, `b`,
`w`, `h`; the families themselves say which rectangles and boxes have tuples.
"Not a rectangle" is `¬ IsRectangular X`. "A rectangle" in the conclusion is
read as `R a b`, as in `theorem62_no_three_copy_tiling`; "a polyomino with n
cells" is `IsPolyomino P` with `P.card = n`. The hypothesis is the finite
computation (a search without hits at this `n`), so the statement isolates the
computational part: it says nothing for an `n` at which the hypothesis has not
been established. The numbering `num` of the families is any injective
numbering of placements. -/
theorem theorem21_search_bridge (num : Placement → ℕ) (hnum : Function.Injective num)
    (n : ℕ)
    (hsearch : ¬ ∃ (a b w h : ℤ) (X : Finset Cell),
      IsSearchSolution num n a b w h X ∧ ¬ IsRectangular X)
    (P : Finset Cell) (hP : IsPolyomino P) (hnr : ¬ IsRectangular P) (hn : P.card = n) :
    (∀ (a b : ℤ) (t : Fin 3 → Finset Cell), ¬ IsTiling P a b t) ∧
      (∀ (a b : ℤ) (t : Fin 5 → Finset Cell), ¬ IsTiling P a b t) :=
  search_bridge num hnum n hsearch P hP hnr hn

/-- (i) Theorem A18 (case (I) does not occur). Source: `report-A2.md`, section 0,
Theorem A18 (lines 11-13), commit `076d663`:

> Let P be a polyomino that is not a rectangle. There is no 5-copy tiling
> T_1, ..., T_5 of a rectangle R(a, b) by P in which the four corner cells of R lie in four
> distinct tiles.

"A rectangle R(a, b)" is `R a b` for any integers `a`, `b`. "There is no 5-copy
tiling ... in which ..." is the negation of `IsTiling P a b t` together with
`CornersInDistinctTiles a b t` for every family `t` of five sets: a tiling covers
`R a b`, so each of its corner cells lies in a tile, and "in four distinct tiles"
is that no tile holds two of the four labelled corners (case (I) of `report.md`,
Theorem 6). -/
theorem theoremA18_no_case_one_tiling (P : Finset Cell) (hP : IsPolyomino P)
    (hnr : ¬ IsRectangular P) (a b : ℤ) (t : Fin 5 → Finset Cell) :
    ¬ (IsTiling P a b t ∧ CornersInDistinctTiles a b t) :=
  fun h => case_one_absurd P hP hnr a b t h.1 h.2

/-- (j) Corollary A19 (five copies). Source: `report-A2.md`, section 0,
Corollary A19 (lines 15-17), commit `076d663`:

> No rectangle is tiled by exactly five congruent copies of a non-rectangular
> polyomino (Theorem A18 with Corollary 63 of the parent's report-4: in such a tiling no tile holds
> two corner cells).

The form is that of `theorem62_no_three_copy_tiling`: "a rectangle" is `R a b`
for integers `a`, `b`, and the five copies are five tiles each congruent to one
non-rectangular polyomino `P`. The words in parentheses are the source's
derivation, not part of the statement. -/
theorem corollaryA19_no_five_copy_tiling (P : Finset Cell) (hP : IsPolyomino P)
    (hnr : ¬ IsRectangular P) (a b : ℤ) (t : Fin 5 → Finset Cell) :
    ¬ IsTiling P a b t :=
  no_five_copy P hP hnr a b t

end PolyominoOddOrder
