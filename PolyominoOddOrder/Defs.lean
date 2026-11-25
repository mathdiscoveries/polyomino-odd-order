module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.Interval
public import Mathlib.Logic.Relation

/-!
# Definitions of the proved library (`Defs.lean`)

A character-for-character copy of the definitions of `Spec.lean` (the trusted
surface), made by `tools/gen_defs.py` (see `BLUEPRINT.md`, section "Comparator").
The proved library declares the same names as the Spec, so no module of the
library imports `Spec.lean`; the Stage 3 comparator checks that the two sets of
kernel terms are identical. Never edit this file by hand: change `Spec.lean`
through its own process and regenerate.
-/

@[expose] public section

namespace PolyominoOddOrder

/-- A cell of the grid, named by its lower-left corner `(x, y)`. -/
abbrev Cell : Type := ℤ × ℤ

/-! ## Adjacency, connectivity, polyominoes -/

/-- Two cells share an edge: they agree in one coordinate and differ by exactly
one in the other. -/
def Adj (c d : Cell) : Prop :=
  (c.1 = d.1 ∧ (c.2 + 1 = d.2 ∨ d.2 + 1 = c.2)) ∨
    (c.2 = d.2 ∧ (c.1 + 1 = d.1 ∨ d.1 + 1 = c.1))

/-- `S` is edge-connected: any two cells of `S` are joined by a chain of cells
of `S` in which consecutive cells share an edge. (The empty set is connected.) -/
def EdgeConnected (S : Finset Cell) : Prop :=
  ∀ c ∈ S, ∀ d ∈ S,
    Relation.ReflTransGen (fun x y : Cell => x ∈ S ∧ y ∈ S ∧ Adj x y) c d

/-- A polyomino: a finite (it is a `Finset`), non-empty, edge-connected set of
cells. -/
def IsPolyomino (P : Finset Cell) : Prop :=
  P.Nonempty ∧ EdgeConnected P

/-! ## Grid isometries and congruence -/

/-- A grid isometry: one of the 8 symmetries of the square, given by three
switches (exchange the two coordinates; negate the first; negate the second),
followed by the translation by `shift`. The 8 settings of the switches are the
8 matrices `[[±1, 0], [0, ±1]]` and `[[0, ±1], [±1, 0]]`. -/
structure GridIso where
  /-- Exchange the two coordinates first. -/
  swap : Bool
  /-- Then negate the first coordinate. -/
  negX : Bool
  /-- Then negate the second coordinate. -/
  negY : Bool
  /-- Finally translate by this vector. -/
  shift : Cell

/-- The image of the cell `c` under `g`: exchange the coordinates if `g.swap`,
negate the first if `g.negX` and the second if `g.negY`, then add `g.shift`. -/
def GridIso.apply (g : GridIso) (c : Cell) : Cell :=
  ((if g.negX then -(if g.swap then c.2 else c.1) else (if g.swap then c.2 else c.1))
      + g.shift.1,
    (if g.negY then -(if g.swap then c.1 else c.2) else (if g.swap then c.1 else c.2))
      + g.shift.2)

/-- Some grid isometry carries `S` onto `T`. -/
def Congruent (S T : Finset Cell) : Prop :=
  ∃ g : GridIso, S.image g.apply = T

/-! ## Rectangles, boxes, sides and corners -/

/-- `R a b`: the cells `(x, y)` with `0 ≤ x < a` and `0 ≤ y < b`. -/
def R (a b : ℤ) : Finset Cell :=
  Finset.Ico 0 a ×ˢ Finset.Ico 0 b

/-- The integers lying between the first coordinates of two cells of `S`; for
non-empty `S` this is the interval from the least to the greatest first
coordinate. -/
def xSpan (S : Finset Cell) : Finset ℤ :=
  S.biUnion fun c => S.biUnion fun d => Finset.Icc c.1 d.1

/-- The integers lying between the second coordinates of two cells of `S`. -/
def ySpan (S : Finset Cell) : Finset ℤ :=
  S.biUnion fun c => S.biUnion fun d => Finset.Icc c.2 d.2

/-- `box(S)`: the smallest rectangle of cells containing `S` (empty for empty
`S`). -/
def boundingBox (S : Finset Cell) : Finset Cell :=
  xSpan S ×ˢ ySpan S

/-- `S` is rectangular: it equals its bounding box. -/
def IsRectangular (S : Finset Cell) : Prop :=
  S = boundingBox S

/-- The bottom row of `R a b`: its cells with `y = 0`. -/
def bottomRow (a b : ℤ) : Finset Cell :=
  (R a b).filter fun c => c.2 = 0

/-- The right column of `R a b`: its cells with `x = a - 1`. -/
def rightCol (a b : ℤ) : Finset Cell :=
  (R a b).filter fun c => c.1 = a - 1

/-- The top row of `R a b`: its cells with `y = b - 1`. -/
def topRow (a b : ℤ) : Finset Cell :=
  (R a b).filter fun c => c.2 = b - 1

/-- The left column of `R a b`: its cells with `x = 0`. -/
def leftCol (a b : ℤ) : Finset Cell :=
  (R a b).filter fun c => c.1 = 0

/-- The four sides of `R a b`, counterclockwise from the bottom:
`0` bottom row, `1` right column, `2` top row, `3` left column. -/
def side (a b : ℤ) : Fin 4 → Finset Cell :=
  ![bottomRow a b, rightCol a b, topRow a b, leftCol a b]

/-- The four corner cells of `R a b`, in the report's order:
`(0, 0)`, `(a - 1, 0)`, `(a - 1, b - 1)`, `(0, b - 1)`. -/
def corner (a b : ℤ) : Fin 4 → Cell :=
  ![(0, 0), (a - 1, 0), (a - 1, b - 1), (0, b - 1)]

/-- `S` and `T` share a cell. -/
def Meets (S T : Finset Cell) : Prop :=
  ∃ c, c ∈ S ∧ c ∈ T

/-- `S` meets row `y` in an interval of cells, possibly empty: with two cells of
row `y` it holds every cell of row `y` between them. -/
def RowInterval (S : Finset Cell) (y : ℤ) : Prop :=
  ∀ x₁ x₂ x₃ : ℤ, x₁ ≤ x₂ → x₂ ≤ x₃ → (x₁, y) ∈ S → (x₃, y) ∈ S → (x₂, y) ∈ S

/-- `S` meets column `x` in an interval of cells, possibly empty. -/
def ColInterval (S : Finset Cell) (x : ℤ) : Prop :=
  ∀ y₁ y₂ y₃ : ℤ, y₁ ≤ y₂ → y₂ ≤ y₃ → (x, y₁) ∈ S → (x, y₃) ∈ S → (x, y₂) ∈ S

/-! ## Tilings -/

/-- `t` is a `k`-copy tiling of `R a b` by `P`: every tile is congruent to `P`,
distinct tiles are disjoint, and the union of the tiles is `R a b`. -/
structure IsTiling (P : Finset Cell) (a b : ℤ) {k : ℕ} (t : Fin k → Finset Cell) : Prop where
  /-- Each tile is the image of `P` under a grid isometry. -/
  congruent : ∀ i, Congruent P (t i)
  /-- Distinct tiles share no cell. -/
  disjoint : ∀ i j, i ≠ j → Disjoint (t i) (t j)
  /-- The tiles together are exactly `R a b`. -/
  cover : Finset.univ.biUnion t = R a b

/-- Case (I) of Theorem 6 (`report.md`, section 2): the four corner cells of
`R a b` lie in four distinct tiles, that is, no tile holds two of the four
corners `corner a b 0`, ..., `corner a b 3`. -/
def CornersInDistinctTiles (a b : ℤ) {k : ℕ} (t : Fin k → Finset Cell) : Prop :=
  ∀ (i : Fin k) (j j' : Fin 4), corner a b j ∈ t i → corner a b j' ∈ t i → j = j'

/-! ## Tuples, solutions and the five search families (`report-3.md`, section 1)

The rectangle `R = R(a, b)` is `R a b` and the box `B = R(w, h)` is `R w h`,
with `a`, `b`, `w`, `h` integers as everywhere in this file. A tuple
`g_1, ..., g_k` is a function `g : Fin k → Placement`; the report's `g_m` is
`g ⟨m - 1, _⟩`, so the Lean index of `g_m` is `m - 1`. -/

/-- `boxSymm w h t` is the map `s_t` (`t = 0, ..., 7`) for the box `R w h`: the
`t`-th entry of the vector is the formula printed for `s_t`. Source:
`report-3.md`, section 1 (lines 30-41), commit `e5ca51d`:

> Conventions as in `report.md` section 1. Fix k >= 2, n >= 1, a rectangle
> R = R(a, b) with a b = k n, and a *box* B = R(w, h).

> The eight symmetries of the square, each followed by the translation that puts the
> image of B back with its lower-left cell at (0, 0), are named s_0, ..., s_7:
>
>     s_0 (x, y) = (x, y)                  s_4 (x, y) = (y, x)
>     s_1 (x, y) = (w - 1 - x, y)          s_5 (x, y) = (h - 1 - y, x)
>     s_2 (x, y) = (x, h - 1 - y)          s_6 (x, y) = (y, w - 1 - x)
>     s_3 (x, y) = (w - 1 - x, h - 1 - y)  s_7 (x, y) = (h - 1 - y, w - 1 - x)

> s_t(B) is R(w, h) for t <= 3 and R(h, w) for t >= 4.

The formula is applied to every cell; only cells of `B` are ever used. -/
def boxSymm (w h : ℤ) (t : Fin 8) (c : Cell) : Cell :=
  ![(c.1, c.2), (w - 1 - c.1, c.2), (c.1, h - 1 - c.2), (w - 1 - c.1, h - 1 - c.2),
    (c.2, c.1), (h - 1 - c.2, c.1), (c.2, w - 1 - c.1), (h - 1 - c.2, w - 1 - c.1)] t

/-- A triple `(t, x, y)`: the symmetry `s_t` followed by the translation by
`(x, y)`. Source: `report-3.md`, section 1 (lines 41-45), commit `e5ca51d`:

> A *placement* is a triple
> (t, x, y) with s_t(B) + (x, y) inside R; it stands for the injective map
> g(u) = s_t(u) + (x, y) from B to R. A placement is *vertical* if t >= 4. A *tuple* is
> a list of k placements g_1, ..., g_k.

The structure is the triple; the condition "s_t(B) + (x, y) inside R" is
`IsPlacement`, and each family below asks it of every entry of its tuples. -/
structure Placement where
  /-- The symmetry `s_t`, `t = 0, ..., 7`. -/
  t : Fin 8
  /-- The first coordinate of the translation. -/
  x : ℤ
  /-- The second coordinate of the translation. -/
  y : ℤ
deriving DecidableEq

/-- The map `g(u) = s_t(u) + (x, y)` of the placement `p = (t, x, y)` of the box
`R w h`. -/
def Placement.apply (p : Placement) (w h : ℤ) (u : Cell) : Cell :=
  ((boxSymm w h p.t u).1 + p.x, (boxSymm w h p.t u).2 + p.y)

/-- `p` is a placement of the box `R w h` in the rectangle `R a b`: the image
`s_t(B) + (x, y)` of `B = R w h` lies inside `R a b`. -/
def IsPlacement (a b w h : ℤ) (p : Placement) : Prop :=
  (R w h).image (p.apply w h) ⊆ R a b

/-- A placement is vertical if `t ≥ 4`. -/
def Placement.IsVertical (p : Placement) : Prop :=
  4 ≤ (p.t : ℕ)

/-- `X` is a solution of the tuple `g` (box `R w h`, rectangle `R a b`). Source:
`report-3.md`, section 1 (lines 44-45), commit `e5ca51d`:

> A *solution* of a tuple is a set X of cells of
> B such that g_1(X), ..., g_k(X) partition R. Then |X| = n.

"Partition R" is read as: the images are pairwise disjoint and their union is
`R a b` (the last sentence, `|X| = n`, is a consequence and is not part of the
definition). -/
structure IsSolution (a b w h : ℤ) {k : ℕ} (g : Fin k → Placement) (X : Finset Cell) :
    Prop where
  /-- `X` is a set of cells of `B = R w h`. -/
  sub : X ⊆ R w h
  /-- The images of `X` under two different entries of the tuple share no cell. -/
  disjoint : ∀ i j, i ≠ j → Disjoint (X.image ((g i).apply w h)) (X.image ((g j).apply w h))
  /-- The images of `X` together are exactly `R a b`. -/
  cover : Finset.univ.biUnion (fun i => X.image ((g i).apply w h)) = R a b

/-- `g^{-1}(c)` for the placement `p` of the box `R w h`: the cells `u` of
`R w h` with `g(u) = c`. The map is injective, so this is the one cell
`g^{-1}(c)` when `c` is in the image of the box, and empty otherwise. -/
def Placement.preimage (p : Placement) (w h : ℤ) (c : Cell) : Finset Cell :=
  (R w h).filter fun u => p.apply w h u = c

/-- `g_{m}^{-1}(c)` for the entry of Lean index `j = m - 1` of the tuple `g`
(empty when the tuple has no such entry). -/
def preimageAt (w h : ℤ) {k : ℕ} (g : Fin k → Placement) (j : ℕ) (c : Cell) :
    Finset Cell :=
  Finset.univ.biUnion fun i : Fin k => if (i : ℕ) = j then (g i).preimage w h c else ∅

/-- `X` is a proper solution of the tuple `g` with known cells `K`. Source:
`report-3.md`, section 1 (lines 55-56), commit `e5ca51d`:

> Each family below comes with a set K of *known cells* of B. A solution is *proper* if
> it is connected and contains K. In every family K contains (0, 0).

"Connected" is `EdgeConnected` (`report.md`, section 1). -/
def IsProperSolution (a b w h : ℤ) {k : ℕ} (g : Fin k → Placement) (K X : Finset Cell) :
    Prop :=
  IsSolution a b w h g X ∧ EdgeConnected X ∧ K ⊆ X

/-- The tuples of family `I(k)` at `n` for the rectangle `R a b` and the box
`R w h`. Source: `report-3.md`, section 1 (lines 30-31 and lines 58-63), commit
`e5ca51d`:

> Fix k >= 2, n >= 1, a rectangle
> R = R(a, b) with a b = k n, and a *box* B = R(w, h).

> **Family I(k)**, k >= 4. Rectangles with 2 <= a <= b. Boxes with w <= a, h <= b,
> w h > n, w + h - 1 <= n. Placements: g_1 = (0, 0, 0); g_2, g_3, g_4 are any
> placements whose image of B contains the corner cell (a - 1, 0), (a - 1, b - 1),
> (0, b - 1) respectively (for each t this fixes x and y); g_5, ..., g_k are any
> placements, listed in increasing order of a fixed numbering of all placements.

`k` is an explicit argument, so `I(5)` is `FamilyI 5` (likewise `FamilyH1 k`
and `FamilyH2 k` below). `num` is that fixed numbering; Theorem 21 below holds
for every injective `num`. The corner cells are `corner a b 1`,
`corner a b 2`, `corner a b 3`, and `g_2`, `g_3`, `g_4` have Lean indices 1,
2, 3. "Any placements" is `IsPlacement` for every entry. The box sides are integers: a box with a side at
most 0 is empty, and a tuple with such a box has no proper solution, since the
known cells contain `(0, 0)`. -/
def FamilyI (k : ℕ) (num : Placement → ℕ) (n : ℕ) (a b w h : ℤ)
    (g : Fin k → Placement) : Prop :=
  4 ≤ k ∧ 1 ≤ n ∧ a * b = (k : ℤ) * n ∧
  2 ≤ a ∧ a ≤ b ∧
  w ≤ a ∧ h ≤ b ∧ (n : ℤ) < w * h ∧ w + h - 1 ≤ n ∧
  (∀ i, IsPlacement a b w h (g i)) ∧
  (∀ i : Fin k, (i : ℕ) = 0 → g i = ⟨0, 0, 0⟩) ∧
  (∀ i : Fin k, (i : ℕ) = 1 → corner a b 1 ∈ (R w h).image ((g i).apply w h)) ∧
  (∀ i : Fin k, (i : ℕ) = 2 → corner a b 2 ∈ (R w h).image ((g i).apply w h)) ∧
  (∀ i : Fin k, (i : ℕ) = 3 → corner a b 3 ∈ (R w h).image ((g i).apply w h)) ∧
  (∀ i j : Fin k, 4 ≤ (i : ℕ) → i < j → num (g i) < num (g j))

/-- The known cells of a tuple of `I(k)`. Source: `report-3.md`, section 1
(line 63), commit `e5ca51d`:

> K = {(0, 0), g_2^{-1}(a - 1, 0), g_3^{-1}(a - 1, b - 1), g_4^{-1}(0, b - 1)}. -/
def knownI (a b w h : ℤ) {k : ℕ} (g : Fin k → Placement) : Finset Cell :=
  {(0, 0)} ∪ preimageAt w h g 1 (corner a b 1) ∪ preimageAt w h g 2 (corner a b 2) ∪
    preimageAt w h g 3 (corner a b 3)

/-- The tuples of family `H1(k)` at `n` for the rectangle `R a b` and the box
`R w h`, where `d` is `h`. Source: `report-3.md`, section 1 (lines 30-31 and
lines 65-69), commit `e5ca51d`:

> Fix k >= 2, n >= 1, a rectangle
> R = R(a, b) with a b = k n, and a *box* B = R(w, h).

> **Family H1(k)**, k >= 2. Rectangles with 2 <= a <= b - 1. Boxes w = a, h = d with
> 2 <= d <= a, a d > n, a + d - 1 <= n. g_1 = (0, 0, 0). Every other placement is
> vertical with 0 <= x <= a - d and 1 <= y <= b - a. g_2 = (t, 0, b - a). If d < a,
> also g_3 = (t', a - d, b - a) (so k >= 3 is needed). The remaining placements are in
> increasing order.

"Increasing order" is that of the fixed numbering `num` of `FamilyI`. The
remaining placements are those after `g_2` (Lean index 2 on) when `d = a`, and
after `g_3` (Lean index 3 on) when `d < a`. -/
def FamilyH1 (k : ℕ) (num : Placement → ℕ) (n : ℕ) (a b w h : ℤ)
    (g : Fin k → Placement) : Prop :=
  2 ≤ k ∧ 1 ≤ n ∧ a * b = (k : ℤ) * n ∧
  2 ≤ a ∧ a ≤ b - 1 ∧
  w = a ∧ 2 ≤ h ∧ h ≤ a ∧ (n : ℤ) < a * h ∧ a + h - 1 ≤ n ∧
  (∀ i, IsPlacement a b w h (g i)) ∧
  (∀ i : Fin k, (i : ℕ) = 0 → g i = ⟨0, 0, 0⟩) ∧
  (∀ i : Fin k, (i : ℕ) ≠ 0 → (g i).IsVertical ∧
    0 ≤ (g i).x ∧ (g i).x ≤ a - h ∧ 1 ≤ (g i).y ∧ (g i).y ≤ b - a) ∧
  (∀ i : Fin k, (i : ℕ) = 1 → (g i).x = 0 ∧ (g i).y = b - a) ∧
  (h < a → 3 ≤ k ∧ ∀ i : Fin k, (i : ℕ) = 2 → (g i).x = a - h ∧ (g i).y = b - a) ∧
  (∀ i j : Fin k, (if h < a then 3 else 2) ≤ (i : ℕ) → i < j → num (g i) < num (g j))

/-- The known cells of a tuple of `H1(k)`, where `d` is `h`. Source:
`report-3.md`, section 1 (lines 69-70), commit `e5ca51d`:

> K = the bottom row of B, the cell g_2^{-1}(0, b - 1), and, if
> d < a, the cell g_3^{-1}(a - 1, b - 1).

The bottom row of `B` is `bottomRow w h`; `(0, b - 1)` is `corner a b 3` and
`(a - 1, b - 1)` is `corner a b 2`. -/
def knownH1 (a b w h : ℤ) {k : ℕ} (g : Fin k → Placement) : Finset Cell :=
  bottomRow w h ∪ preimageAt w h g 1 (corner a b 3) ∪
    (if h < a then preimageAt w h g 2 (corner a b 2) else ∅)

/-- The tuples of family `H2(k)` at `n` for the rectangle `R a b` and the box
`R w h`, where `d` is `h`. Source: `report-3.md`, section 1 (lines 30-31 and
lines 72-76), commit `e5ca51d`:

> Fix k >= 2, n >= 1, a rectangle
> R = R(a, b) with a b = k n, and a *box* B = R(w, h).

> **Family H2(k)**, k >= 2. Rectangles with a >= 2. Boxes w = a, h = d with d >= 2,
> a d > n, a + d - 1 <= n. g_1 = (0, 0, 0) and g_2 = (t, 0, b - d) with t = 2 or 3. For
> k = 2: d <= b and there is no other placement. For k >= 3: a <= b - 2, d <= a, and
> g_3, ..., g_k are vertical with 0 <= x <= a - d and 1 <= y <= b - a - 1, in
> increasing order.

"Increasing order" is that of the fixed numbering `num` of `FamilyI`; `g_3`
has Lean index 2. -/
def FamilyH2 (k : ℕ) (num : Placement → ℕ) (n : ℕ) (a b w h : ℤ)
    (g : Fin k → Placement) : Prop :=
  2 ≤ k ∧ 1 ≤ n ∧ a * b = (k : ℤ) * n ∧
  2 ≤ a ∧
  w = a ∧ 2 ≤ h ∧ (n : ℤ) < a * h ∧ a + h - 1 ≤ n ∧
  (∀ i, IsPlacement a b w h (g i)) ∧
  (∀ i : Fin k, (i : ℕ) = 0 → g i = ⟨0, 0, 0⟩) ∧
  (∀ i : Fin k, (i : ℕ) = 1 → ((g i).t = 2 ∨ (g i).t = 3) ∧ (g i).x = 0 ∧ (g i).y = b - h) ∧
  (k = 2 → h ≤ b) ∧
  (3 ≤ k → a ≤ b - 2 ∧ h ≤ a ∧
    (∀ i : Fin k, 2 ≤ (i : ℕ) → (g i).IsVertical ∧
      0 ≤ (g i).x ∧ (g i).x ≤ a - h ∧ 1 ≤ (g i).y ∧ (g i).y ≤ b - a - 1) ∧
    (∀ i j : Fin k, 2 ≤ (i : ℕ) → i < j → num (g i) < num (g j)))

/-- The known cells of a tuple of `H2(k)`. Source: `report-3.md`, section 1
(line 76), commit `e5ca51d`:

> K = the bottom row of B.

The bottom row of `B = R w h` is `bottomRow w h`. -/
def knownH2 (w h : ℤ) : Finset Cell :=
  bottomRow w h

/-- `X` is a proper solution of some tuple of `I(5)`, `H1(5)`, `H2(5)`,
`H1(3)` or `H2(3)` at `n`, for the rectangle `R a b` and the box `R w h`, with
that family's known cells. Source: `report-3.md`, section 2, Theorem 21
(lines 164-165), commit `e5ca51d`:

> Suppose that, over all rectangles and boxes allowed in section 1, no tuple of
> I(5), H1(5), H2(5), H1(3), H2(3) has a proper solution that is not a rectangle. -/
def IsSearchSolution (num : Placement → ℕ) (n : ℕ) (a b w h : ℤ) (X : Finset Cell) : Prop :=
  (∃ g : Fin 5 → Placement,
    FamilyI 5 num n a b w h g ∧ IsProperSolution a b w h g (knownI a b w h g) X) ∨
  (∃ g : Fin 5 → Placement,
    FamilyH1 5 num n a b w h g ∧ IsProperSolution a b w h g (knownH1 a b w h g) X) ∨
  (∃ g : Fin 5 → Placement,
    FamilyH2 5 num n a b w h g ∧ IsProperSolution a b w h g (knownH2 w h) X) ∨
  (∃ g : Fin 3 → Placement,
    FamilyH1 3 num n a b w h g ∧ IsProperSolution a b w h g (knownH1 a b w h g) X) ∨
  (∃ g : Fin 3 → Placement,
    FamilyH2 3 num n a b w h g ∧ IsProperSolution a b w h g (knownH2 w h) X)

end PolyominoOddOrder
