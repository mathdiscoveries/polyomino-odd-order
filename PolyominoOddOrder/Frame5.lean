module

public import PolyominoOddOrder.SearchBridge
public import PolyominoOddOrder.CaseIOpposite

/-!
# Case (I), foundation 1: five-tile frames (`Frame5.lean`)

Blueprint unit A0a (third increment). The setting of `report-A2.md`, section 1: a
5-copy tiling of `R a b` by a non-rectangular polyomino `P` whose four corner
cells lie in four distinct tiles `T_1, ..., T_4`; `T_5` is the fifth tile.

The report chooses isometries `g_i` and speaks of marks, orientations and runs.
Here all of that is one orientation code per tile (`Orient`, 8 values) and two
integers. `P` is moved so that `box(P) = R p q`, and the cells of a tile are
read in *local coordinates* measured from the tile's own corner of `R a b`
(`loc`): for `T_1` the cell itself, for `T_2` the distances from the right and
the bottom side, for `T_3` from the right and the top side, for `T_4` from the
left and the top side, for `T_5` the offset from the lower left cell
`(x5, y5)` of its box. `Orient.back` turns a local position into a cell of
`box(P)`. A symmetry of the rectangle then only permutes the codes
(`Frame5.flipX`, `flipY`, `halfTurn`, `transpose`), and renaming the corners of
`box(P)` is a symmetry of `P` (`Frame5.flipPX`, `flipPY`, `transposeP`).

Lean indices: `t 0, ..., t 4` are `T_1, ..., T_5`, and `o i` is the code of
`T_{i+1}`.

| report | Lean |
|---|---|
| `T_i` wide / tall (for `p = q`: which direction of `box(P)` is horizontal) | `(o i).swap = false` / `true` |
| mark of `T_i` | the corner `(o i).back p q (0, 0)`, that is `((o i).negX, (o i).negY)` |
| `W_i`, `H_i` | `(o i).W p q`, `(o i).H p q` |
| `u_i`, `v_i`, `mu` | `(o i).rowLine p q P 0`, `(o i).colLine p q P 0`, `(o 4).rowLine p q P 0` |
| pattern N / O | `FrameN` / `FrameO` |
| line counts (2) | `Frame5.col_sum`, `Frame5.row_sum` |

Source: `theoretician/report-A2.md` (goals lab, commit `076d663`), sections 1
and 2. The statements of this file were tested outside Lean on random cell sets
and codes (`tools/frame5_check.py`).
-/

@[expose] public section

namespace PolyominoOddOrder

/-! ## Orientation codes -/

/-- The orientation of a tile, seen in the tile's local coordinates: exchange the
two local coordinates if `swap`, then reverse the first coordinate of `box(P)`
if `negX` and the second if `negY` (`Orient.back`). `swap = false` is "wide",
`swap = true` is "tall" (`report-A2.md`, section 1.2). -/
@[ext] structure Orient where
  /-- The local horizontal direction is the second direction of `box(P)`. -/
  swap : Bool
  /-- The first coordinate of `box(P)` runs against the local coordinate. -/
  negX : Bool
  /-- The second coordinate of `box(P)` runs against the local coordinate. -/
  negY : Bool
deriving DecidableEq, Fintype

namespace Orient

/-- The cell of `box(P) = R p q` that sits at the local position `c` of a tile
with orientation `o`. -/
def back (o : Orient) (p q : ℤ) (c : Cell) : Cell :=
  (if o.negX then p - 1 - (if o.swap then c.2 else c.1) else (if o.swap then c.2 else c.1),
    if o.negY then q - 1 - (if o.swap then c.1 else c.2) else (if o.swap then c.1 else c.2))

/-- The local position of the cell `d` of `box(P)`: the inverse of `back`. -/
def fwd (o : Orient) (p q : ℤ) (d : Cell) : Cell :=
  (if o.swap then (if o.negY then q - 1 - d.2 else d.2) else (if o.negX then p - 1 - d.1 else d.1),
    if o.swap then (if o.negX then p - 1 - d.1 else d.1) else (if o.negY then q - 1 - d.2 else d.2))

/-- The number of columns of the box of a tile with orientation `o` (`W_i`). -/
def W (o : Orient) (p q : ℤ) : ℤ := if o.swap then q else p

/-- The number of rows of the box of a tile with orientation `o` (`H_i`). -/
def H (o : Orient) (p q : ℤ) : ℤ := if o.swap then p else q

/-- The local horizontal direction runs against its direction of `box(P)`. -/
def revH (o : Orient) : Bool := if o.swap then o.negY else o.negX

/-- The local vertical direction runs against its direction of `box(P)`. -/
def revV (o : Orient) : Bool := if o.swap then o.negX else o.negY

/-- The code of the mirror image in a vertical line: the local horizontal
direction is reversed. -/
def reflX (o : Orient) : Orient :=
  ⟨o.swap, if o.swap then o.negX else !o.negX, if o.swap then !o.negY else o.negY⟩

/-- The code of the mirror image in a horizontal line. -/
def reflY (o : Orient) : Orient :=
  ⟨o.swap, if o.swap then !o.negX else o.negX, if o.swap then o.negY else !o.negY⟩

/-- The code of the half turn. -/
def turn (o : Orient) : Orient := ⟨o.swap, !o.negX, !o.negY⟩

/-- The code after the two axes of the rectangle are exchanged. -/
def tr (o : Orient) : Orient := ⟨!o.swap, o.negX, o.negY⟩

/-- The code with respect to the mirror image of `P` in a vertical line. -/
def pX (o : Orient) : Orient := ⟨o.swap, !o.negX, o.negY⟩

/-- The code with respect to the mirror image of `P` in a horizontal line. -/
def pY (o : Orient) : Orient := ⟨o.swap, o.negX, !o.negY⟩

/-- The code with respect to the transpose of `P`. -/
def pT (o : Orient) : Orient := ⟨!o.swap, o.negY, o.negX⟩

/-- The number of cells in the local column `x` of a tile with orientation `o`:
a column or a row of `P`. -/
def colLine (o : Orient) (p q : ℤ) (P : Finset Cell) (x : ℤ) : ℤ :=
  if o.swap then rowCount P (if o.negY then q - 1 - x else x)
  else colCount P (if o.negX then p - 1 - x else x)

/-- The number of cells in the local row `y` of a tile with orientation `o`. -/
def rowLine (o : Orient) (p q : ℤ) (P : Finset Cell) (y : ℤ) : ℤ :=
  if o.swap then colCount P (if o.negX then p - 1 - y else y)
  else rowCount P (if o.negY then q - 1 - y else y)

/-- The corner of `box(P) = R p q` named by two switches: `(false, false)` is
`(0, 0)`, `(true, false)` is `(p - 1, 0)`, `(false, true)` is `(0, q - 1)` and
`(true, true)` is `(p - 1, q - 1)`. -/
def cornerP (p q : ℤ) (X Y : Bool) : Cell := (if X then p - 1 else 0, if Y then q - 1 else 0)

/-- The mark: the corner of `box(P)` at the local position `(0, 0)`. -/
theorem back_zero (o : Orient) (p q : ℤ) : o.back p q (0, 0) = cornerP p q o.negX o.negY := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [back, cornerP]

/-- The corner of `box(P)` at the far end of the local horizontal side. -/
theorem back_W (o : Orient) (p q : ℤ) :
    o.back p q (o.W p q - 1, 0) =
      cornerP p q (if o.swap then o.negX else !o.negX) (if o.swap then !o.negY else o.negY) := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [back, cornerP, W]

/-- The corner of `box(P)` at the far end of the local vertical side. -/
theorem back_H (o : Orient) (p q : ℤ) :
    o.back p q (0, o.H p q - 1) =
      cornerP p q (if o.swap then !o.negX else o.negX) (if o.swap then o.negY else !o.negY) := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [back, cornerP, H]

/-- The corner of `box(P)` opposite to the mark. -/
theorem back_WH (o : Orient) (p q : ℤ) :
    o.back p q (o.W p q - 1, o.H p q - 1) = cornerP p q (!o.negX) (!o.negY) := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [back, cornerP, W, H]

theorem back_fwd (o : Orient) (p q : ℤ) (d : Cell) : o.back p q (o.fwd p q d) = d := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [back, fwd]

theorem fwd_back (o : Orient) (p q : ℤ) (c : Cell) : o.fwd p q (o.back p q c) = c := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [back, fwd]

theorem back_injective (o : Orient) (p q : ℤ) : Function.Injective (o.back p q) :=
  Function.LeftInverse.injective (o.fwd_back p q)

/-- A local position lies in the box of the tile exactly when its cell of `box(P)`
lies in `R p q`. -/
theorem back_mem_R (o : Orient) (p q : ℤ) (c : Cell) :
    o.back p q c ∈ R p q ↔ (0 ≤ c.1 ∧ c.1 < o.W p q) ∧ 0 ≤ c.2 ∧ c.2 < o.H p q := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [back, W, H, mem_R] <;> omega

@[simp] theorem reflX_swap (o : Orient) : o.reflX.swap = o.swap := rfl
@[simp] theorem reflY_swap (o : Orient) : o.reflY.swap = o.swap := rfl
@[simp] theorem turn_swap (o : Orient) : o.turn.swap = o.swap := rfl
@[simp] theorem tr_swap (o : Orient) : o.tr.swap = !o.swap := rfl
@[simp] theorem tr_negX (o : Orient) : o.tr.negX = o.negX := rfl
@[simp] theorem tr_negY (o : Orient) : o.tr.negY = o.negY := rfl
@[simp] theorem turn_negX (o : Orient) : o.turn.negX = !o.negX := rfl
@[simp] theorem turn_negY (o : Orient) : o.turn.negY = !o.negY := rfl
@[simp] theorem pX_swap (o : Orient) : o.pX.swap = o.swap := rfl
@[simp] theorem pX_negX (o : Orient) : o.pX.negX = !o.negX := rfl
@[simp] theorem pX_negY (o : Orient) : o.pX.negY = o.negY := rfl
@[simp] theorem pY_swap (o : Orient) : o.pY.swap = o.swap := rfl
@[simp] theorem pY_negX (o : Orient) : o.pY.negX = o.negX := rfl
@[simp] theorem pY_negY (o : Orient) : o.pY.negY = !o.negY := rfl
@[simp] theorem pT_swap (o : Orient) : o.pT.swap = !o.swap := rfl
@[simp] theorem pT_negX (o : Orient) : o.pT.negX = o.negY := rfl
@[simp] theorem pT_negY (o : Orient) : o.pT.negY = o.negX := rfl

@[simp] theorem W_reflX (o : Orient) (p q : ℤ) : o.reflX.W p q = o.W p q := rfl
@[simp] theorem H_reflX (o : Orient) (p q : ℤ) : o.reflX.H p q = o.H p q := rfl
@[simp] theorem W_reflY (o : Orient) (p q : ℤ) : o.reflY.W p q = o.W p q := rfl
@[simp] theorem H_reflY (o : Orient) (p q : ℤ) : o.reflY.H p q = o.H p q := rfl
@[simp] theorem W_turn (o : Orient) (p q : ℤ) : o.turn.W p q = o.W p q := rfl
@[simp] theorem H_turn (o : Orient) (p q : ℤ) : o.turn.H p q = o.H p q := rfl
@[simp] theorem W_pX (o : Orient) (p q : ℤ) : o.pX.W p q = o.W p q := rfl
@[simp] theorem H_pX (o : Orient) (p q : ℤ) : o.pX.H p q = o.H p q := rfl
@[simp] theorem W_pY (o : Orient) (p q : ℤ) : o.pY.W p q = o.W p q := rfl
@[simp] theorem H_pY (o : Orient) (p q : ℤ) : o.pY.H p q = o.H p q := rfl

@[simp] theorem W_tr (o : Orient) (p q : ℤ) : o.tr.W p q = o.H p q := by
  rcases o with ⟨_ | _, _, _⟩ <;> rfl

@[simp] theorem H_tr (o : Orient) (p q : ℤ) : o.tr.H p q = o.W p q := by
  rcases o with ⟨_ | _, _, _⟩ <;> rfl

@[simp] theorem W_pT (o : Orient) (p q : ℤ) : o.pT.W q p = o.W p q := by
  rcases o with ⟨_ | _, _, _⟩ <;> rfl

@[simp] theorem H_pT (o : Orient) (p q : ℤ) : o.pT.H q p = o.H p q := by
  rcases o with ⟨_ | _, _, _⟩ <;> rfl

@[simp] theorem turn_turn (o : Orient) : o.turn.turn = o := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> rfl

@[simp] theorem tr_tr (o : Orient) : o.tr.tr = o := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> rfl

@[simp] theorem reflX_reflX (o : Orient) : o.reflX.reflX = o := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> rfl

@[simp] theorem reflY_reflY (o : Orient) : o.reflY.reflY = o := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> rfl

theorem reflY_reflX (o : Orient) : o.reflX.reflY = o.turn := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> rfl

/-- The mirror image in a vertical line, in local coordinates. -/
theorem back_reflX (o : Orient) (p q : ℤ) (c : Cell) :
    o.reflX.back p q c = o.back p q (o.W p q - 1 - c.1, c.2) := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [reflX, back, W]

/-- The mirror image in a horizontal line, in local coordinates. -/
theorem back_reflY (o : Orient) (p q : ℤ) (c : Cell) :
    o.reflY.back p q c = o.back p q (c.1, o.H p q - 1 - c.2) := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [reflY, back, H]

/-- The half turn of the box of the tile, in local coordinates. -/
theorem back_turn (o : Orient) (p q : ℤ) (c : Cell) :
    o.turn.back p q c = o.back p q (o.W p q - 1 - c.1, o.H p q - 1 - c.2) := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [turn, back, W, H]

/-- The exchange of the two axes, in local coordinates. -/
theorem back_tr (o : Orient) (p q : ℤ) (c : Cell) : o.tr.back p q c = o.back p q (c.2, c.1) := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [tr, back]

theorem back_pX (o : Orient) (p q : ℤ) (c : Cell) :
    o.pX.back p q c = (p - 1 - (o.back p q c).1, (o.back p q c).2) := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [pX, back]

theorem back_pY (o : Orient) (p q : ℤ) (c : Cell) :
    o.pY.back p q c = ((o.back p q c).1, q - 1 - (o.back p q c).2) := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [pY, back]

theorem back_pT (o : Orient) (p q : ℤ) (c : Cell) :
    o.pT.back q p c = ((o.back p q c).2, (o.back p q c).1) := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [pT, back]

theorem colLine_reflX (o : Orient) (p q : ℤ) (P : Finset Cell) (x : ℤ) :
    o.reflX.colLine p q P x = o.colLine p q P (o.W p q - 1 - x) := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [reflX, colLine, W]

theorem rowLine_reflX (o : Orient) (p q : ℤ) (P : Finset Cell) (y : ℤ) :
    o.reflX.rowLine p q P y = o.rowLine p q P y := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [reflX, rowLine]

theorem colLine_reflY (o : Orient) (p q : ℤ) (P : Finset Cell) (x : ℤ) :
    o.reflY.colLine p q P x = o.colLine p q P x := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [reflY, colLine]

theorem rowLine_reflY (o : Orient) (p q : ℤ) (P : Finset Cell) (y : ℤ) :
    o.reflY.rowLine p q P y = o.rowLine p q P (o.H p q - 1 - y) := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [reflY, rowLine, H]

theorem colLine_turn (o : Orient) (p q : ℤ) (P : Finset Cell) (x : ℤ) :
    o.turn.colLine p q P x = o.colLine p q P (o.W p q - 1 - x) := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [turn, colLine, W]

theorem rowLine_turn (o : Orient) (p q : ℤ) (P : Finset Cell) (y : ℤ) :
    o.turn.rowLine p q P y = o.rowLine p q P (o.H p q - 1 - y) := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [turn, rowLine, H]

theorem colLine_tr (o : Orient) (p q : ℤ) (P : Finset Cell) (x : ℤ) :
    o.tr.colLine p q P x = o.rowLine p q P x := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [tr, colLine, rowLine]

theorem rowLine_tr (o : Orient) (p q : ℤ) (P : Finset Cell) (y : ℤ) :
    o.tr.rowLine p q P y = o.colLine p q P y := by
  rcases o with ⟨_ | _, _ | _, _ | _⟩ <;> simp [tr, colLine, rowLine]

end Orient

/-! ## Frames -/

/-- The local position of the cell `c` in the tile of index `i`: measured from
the corner `(0, 0)`, `(a - 1, 0)`, `(a - 1, b - 1)`, `(0, b - 1)` of `R a b` for
`i = 0, 1, 2, 3`, and from the cell `(x5, y5)` for `i = 4`. -/
def loc (a b x5 y5 : ℤ) (i : Fin 5) (c : Cell) : Cell :=
  ![(c.1, c.2), (a - 1 - c.1, c.2), (a - 1 - c.1, b - 1 - c.2), (c.1, b - 1 - c.2),
    (c.1 - x5, c.2 - y5)] i

/-- The cell with local position `c` in the tile of index `i`: the inverse of
`loc`. -/
def unloc (a b x5 y5 : ℤ) (i : Fin 5) (c : Cell) : Cell :=
  ![(c.1, c.2), (a - 1 - c.1, c.2), (a - 1 - c.1, b - 1 - c.2), (c.1, b - 1 - c.2),
    (c.1 + x5, c.2 + y5)] i

/-- The setting of `report-A2.md`, section 1.1, for one polyomino in its box:
`P` is a non-rectangular polyomino with `box(P) = R p q`; `t` is a 5-copy tiling
of `R a b` by `P`; the tile `t i` consists of the cells whose local position
(`loc`) is carried into `P` by the code `o i`; the tiles `t 0, ..., t 3` hold
the corner cells `(0, 0)`, `(a - 1, 0)`, `(a - 1, b - 1)`, `(0, b - 1)`.
`box(T_5) = [x5, x5 + W_5) x [y5, y5 + H_5)`. No order between `p` and `q` is
assumed. -/
structure Frame5 (P : Finset Cell) (p q a b : ℤ) (t : Fin 5 → Finset Cell)
    (o : Fin 5 → Orient) (x5 y5 : ℤ) : Prop where
  /-- `P` is a polyomino. -/
  poly : IsPolyomino P
  /-- `P` is not a rectangle. -/
  notRect : ¬ IsRectangular P
  /-- `P` lies in `R p q`. -/
  sub : P ⊆ R p q
  /-- `P` meets the left column of `R p q`. -/
  left : ∃ y : ℤ, (0, y) ∈ P
  /-- `P` meets the right column of `R p q`. -/
  right : ∃ y : ℤ, (p - 1, y) ∈ P
  /-- `P` meets the bottom row of `R p q`. -/
  bottom : ∃ x : ℤ, (x, 0) ∈ P
  /-- `P` meets the top row of `R p q`. -/
  top : ∃ x : ℤ, (x, q - 1) ∈ P
  /-- The five tiles are a tiling of `R a b` by `P`. -/
  tiling : IsTiling P a b t
  /-- The cells of the tile `t i`, in local coordinates. -/
  mem : ∀ (i : Fin 5) (c : Cell), c ∈ t i ↔ (o i).back p q (loc a b x5 y5 i c) ∈ P
  /-- The mark of a corner tile is an occupied corner of `box(P)`. -/
  corner : ∀ i : Fin 5, i ≠ 4 → (o i).back p q (0, 0) ∈ P

/-- Pattern N (`report-A2.md`, section 1.1): `T_5` meets no side of `R a b`. -/
structure FrameN (P : Finset Cell) (p q a b : ℤ) (t : Fin 5 → Finset Cell)
    (o : Fin 5 → Orient) (x5 y5 : ℤ) : Prop extends Frame5 P p q a b t o x5 y5 where
  /-- `T_5` does not meet the left side. -/
  x5_pos : 1 ≤ x5
  /-- `T_5` does not meet the bottom side. -/
  y5_pos : 1 ≤ y5
  /-- `T_5` does not meet the right side. -/
  x5_le : x5 + (o 4).W p q ≤ a - 1
  /-- `T_5` does not meet the top side. -/
  y5_le : y5 + (o 4).H p q ≤ b - 1

/-- Pattern O (`report-A2.md`, section 1.1): `T_5` meets the bottom side of
`R a b` and no other. -/
structure FrameO (P : Finset Cell) (p q a b : ℤ) (t : Fin 5 → Finset Cell)
    (o : Fin 5 → Orient) (x5 y5 : ℤ) : Prop extends Frame5 P p q a b t o x5 y5 where
  /-- `T_5` meets the bottom side. -/
  y5_eq : y5 = 0
  /-- `T_5` does not meet the left side. -/
  x5_pos : 1 ≤ x5
  /-- `T_5` does not meet the right side. -/
  x5_le : x5 + (o 4).W p q ≤ a - 1
  /-- `T_5` does not meet the top side. -/
  h5_le : (o 4).H p q ≤ b - 1

/-! ## The occupied corners of `box(P)` (`report-A2.md`, section 1.2)

One normal form for each number of occupied corners; the other positions are
reached by `Frame5.flipPX`, `flipPY`, `transposeP`. -/

/-- All four corners of `box(P)` are in `P` (`|S| = 4`, section 4). -/
structure Four (P : Finset Cell) (p q : ℤ) : Prop where
  /-- The lower left corner. -/
  c00 : ((0, 0) : Cell) ∈ P
  /-- The lower right corner. -/
  c10 : ((p - 1, 0) : Cell) ∈ P
  /-- The upper left corner. -/
  c01 : ((0, q - 1) : Cell) ∈ P
  /-- The upper right corner. -/
  c11 : ((p - 1, q - 1) : Cell) ∈ P

/-- Three occupied corners (section 5): `E = (0, 0)`, `A = (p - 1, 0)`,
`B = (0, q - 1)` are in `P` and `D = (p - 1, q - 1)` is not. With `q ≤ p` the
side `EA` is the long one, as in the report. -/
structure Three (P : Finset Cell) (p q : ℤ) : Prop where
  /-- `E`. -/
  hE : ((0, 0) : Cell) ∈ P
  /-- `A`. -/
  hA : ((p - 1, 0) : Cell) ∈ P
  /-- `B`. -/
  hB : ((0, q - 1) : Cell) ∈ P
  /-- `D` is not occupied. -/
  hD : ((p - 1, q - 1) : Cell) ∉ P

/-- Two adjacent occupied corners (section 6): `A = (0, 0)` and `C = (p - 1, 0)`
are in `P`, the other two are not. The side `F` is the bottom row of `box(P)`,
`L = p`, `M = q`; no order between `p` and `q`. -/
structure Adjacent (P : Finset Cell) (p q : ℤ) : Prop where
  /-- `A`. -/
  hA : ((0, 0) : Cell) ∈ P
  /-- `C`. -/
  hC : ((p - 1, 0) : Cell) ∈ P
  /-- The corner above `A` is not occupied. -/
  h01 : ((0, q - 1) : Cell) ∉ P
  /-- The corner above `C` is not occupied. -/
  h11 : ((p - 1, q - 1) : Cell) ∉ P

/-- Two opposite occupied corners (section 7): `A = (0, 0)` and
`C = (p - 1, q - 1)` are in `P`, the other two are not. -/
structure Opposite (P : Finset Cell) (p q : ℤ) : Prop where
  /-- `A`. -/
  hA : ((0, 0) : Cell) ∈ P
  /-- `C`. -/
  hC : ((p - 1, q - 1) : Cell) ∈ P
  /-- The lower right corner is not occupied. -/
  h10 : ((p - 1, 0) : Cell) ∉ P
  /-- The upper left corner is not occupied. -/
  h01 : ((0, q - 1) : Cell) ∉ P

/-- All four corner tiles have the same mark (section 3). -/
def SameMarks (o : Fin 5 → Orient) : Prop :=
  ∀ i : Fin 5, i ≠ 4 → (o i).negX = (o 0).negX ∧ (o i).negY = (o 0).negY

variable {P : Finset Cell} {p q a b : ℤ} {t : Fin 5 → Finset Cell} {o : Fin 5 → Orient}
  {x5 y5 : ℤ}

theorem loc_unloc (a b x5 y5 : ℤ) (i : Fin 5) (c : Cell) :
    loc a b x5 y5 i (unloc a b x5 y5 i c) = c := by
  fin_cases i <;> simp [loc, unloc]

theorem unloc_loc (a b x5 y5 : ℤ) (i : Fin 5) (c : Cell) :
    unloc a b x5 y5 i (loc a b x5 y5 i c) = c := by
  fin_cases i <;> simp [loc, unloc]

namespace Frame5

/-! ## Cells of the tiles -/

/-- The cells of `T_1`. -/
theorem mem0 (F : Frame5 P p q a b t o x5 y5) (c : Cell) :
    c ∈ t 0 ↔ (o 0).back p q c ∈ P := by
  simpa [loc] using F.mem 0 c

/-- The cells of `T_2`. -/
theorem mem1 (F : Frame5 P p q a b t o x5 y5) (c : Cell) :
    c ∈ t 1 ↔ (o 1).back p q (a - 1 - c.1, c.2) ∈ P := by
  simpa [loc] using F.mem 1 c

/-- The cells of `T_3`. -/
theorem mem2 (F : Frame5 P p q a b t o x5 y5) (c : Cell) :
    c ∈ t 2 ↔ (o 2).back p q (a - 1 - c.1, b - 1 - c.2) ∈ P := by
  simpa [loc] using F.mem 2 c

/-- The cells of `T_4`. -/
theorem mem3 (F : Frame5 P p q a b t o x5 y5) (c : Cell) :
    c ∈ t 3 ↔ (o 3).back p q (c.1, b - 1 - c.2) ∈ P := by
  simpa [loc] using F.mem 3 c

/-- The cells of `T_5`. -/
theorem mem4 (F : Frame5 P p q a b t o x5 y5) (c : Cell) :
    c ∈ t 4 ↔ (o 4).back p q (c.1 - x5, c.2 - y5) ∈ P := by
  simpa [loc] using F.mem 4 c

/-- The cells of `P` lie in `R p q`. -/
theorem P_bounds (F : Frame5 P p q a b t o x5 y5) {c : Cell} (hc : c ∈ P) :
    (0 ≤ c.1 ∧ c.1 < p) ∧ 0 ≤ c.2 ∧ c.2 < q :=
  mem_R.1 (F.sub hc)

theorem conn_P (F : Frame5 P p q a b t o x5 y5) : EdgeConnected P := F.poly.2

/-- The tiles are connected. -/
theorem conn (F : Frame5 P p q a b t o x5 y5) (i : Fin 5) : EdgeConnected (t i) :=
  (F.tiling.tile_isPolyomino F.poly i).2

/-- The tiles lie in `R a b`. -/
theorem sub_R (F : Frame5 P p q a b t o x5 y5) (i : Fin 5) : t i ⊆ R a b :=
  F.tiling.subset_R i

/-- Two tiles with a common cell are the same tile. -/
theorem tile_unique (F : Frame5 P p q a b t o x5 y5) {c : Cell} {i j : Fin 5}
    (hi : c ∈ t i) (hj : c ∈ t j) : i = j :=
  F.tiling.tile_unique hi hj

/-- `a ≥ 2`. -/
theorem two_le_a (F : Frame5 P p q a b t o x5 y5) : 2 ≤ a :=
  (F.tiling.two_le F.poly F.notRect (by norm_num)).1

/-- `b ≥ 2`. -/
theorem two_le_b (F : Frame5 P p q a b t o x5 y5) : 2 ≤ b :=
  (F.tiling.two_le F.poly F.notRect (by norm_num)).2

/-- `p ≥ 2`: a connected set of cells in one line is a rectangle
(`report-A2.md`, section 1.1). -/
theorem two_le_p (F : Frame5 P p q a b t o x5 y5) : 2 ≤ p := by
  obtain ⟨y, hy⟩ := F.left
  have h := (F.P_bounds hy).1.2
  have h1 : p ≠ 1 := fun h1 =>
    F.notRect (F.conn_P.isRectangular_of_thin F.sub (Or.inl h1))
  dsimp only at h
  omega

/-- `q ≥ 2` (`report-A2.md`, section 1.1). -/
theorem two_le_q (F : Frame5 P p q a b t o x5 y5) : 2 ≤ q := by
  obtain ⟨x, hx⟩ := F.bottom
  have h := (F.P_bounds hx).2.2
  have h1 : q ≠ 1 := fun h1 =>
    F.notRect (F.conn_P.isRectangular_of_thin F.sub (Or.inr h1))
  dsimp only at h
  omega

/-- `box(P)` has `p` columns. -/
theorem width_eq (F : Frame5 P p q a b t o x5 y5) : width P = p := by
  obtain ⟨y, hy⟩ := F.left
  obtain ⟨y', hy'⟩ := F.right
  exact width_eq_of_cols F.sub hy hy'

/-- `box(P)` has `q` rows. -/
theorem height_eq (F : Frame5 P p q a b t o x5 y5) : height P = q := by
  obtain ⟨x, hx⟩ := F.bottom
  obtain ⟨x', hx'⟩ := F.top
  exact height_eq_of_rows F.sub hx hx'

/-- `T_1` holds the corner cell `(0, 0)`. -/
theorem corner0 (F : Frame5 P p q a b t o x5 y5) : ((0, 0) : Cell) ∈ t 0 :=
  (F.mem0 _).2 (F.corner 0 (by decide))

/-- `T_2` holds the corner cell `(a - 1, 0)`. -/
theorem corner1 (F : Frame5 P p q a b t o x5 y5) : ((a - 1, 0) : Cell) ∈ t 1 := by
  rw [F.mem1]
  simpa using F.corner 1 (by decide)

/-- `T_3` holds the corner cell `(a - 1, b - 1)`. -/
theorem corner2 (F : Frame5 P p q a b t o x5 y5) : ((a - 1, b - 1) : Cell) ∈ t 2 := by
  rw [F.mem2]
  simpa using F.corner 2 (by decide)

/-- `T_4` holds the corner cell `(0, b - 1)`. -/
theorem corner3 (F : Frame5 P p q a b t o x5 y5) : ((0, b - 1) : Cell) ∈ t 3 := by
  rw [F.mem3]
  simpa using F.corner 3 (by decide)

/-- The four corner cells lie in four distinct tiles. -/
theorem cornersDistinct (F : Frame5 P p q a b t o x5 y5) : CornersInDistinctTiles a b t := by
  have hc : ∀ j : Fin 4, PolyominoOddOrder.corner a b j ∈ t j.castSucc := by
    intro j
    fin_cases j
    · exact F.corner0
    · exact F.corner1
    · exact F.corner2
    · exact F.corner3
  intro i j j' hj hj'
  exact Fin.castSucc_injective 4
    ((F.tile_unique (hc j) hj).trans (F.tile_unique hj' (hc j')))

/-- The local position of a cell of a tile lies in the box of the tile. -/
theorem loc_bounds (F : Frame5 P p q a b t o x5 y5) {i : Fin 5} {c : Cell} (hc : c ∈ t i) :
    (0 ≤ (loc a b x5 y5 i c).1 ∧ (loc a b x5 y5 i c).1 < (o i).W p q) ∧
      0 ≤ (loc a b x5 y5 i c).2 ∧ (loc a b x5 y5 i c).2 < (o i).H p q :=
  (Orient.back_mem_R _ _ _ _).1 (F.sub ((F.mem i c).1 hc))

/-- `box(T_1) = [0, W_1) x [0, H_1)` (`report-A2.md`, section 1.1). -/
theorem box0 (F : Frame5 P p q a b t o x5 y5) {c : Cell} (hc : c ∈ t 0) :
    (0 ≤ c.1 ∧ c.1 < (o 0).W p q) ∧ 0 ≤ c.2 ∧ c.2 < (o 0).H p q := by
  simpa [loc] using F.loc_bounds hc

/-- `box(T_2) = [a - W_2, a) x [0, H_2)`. -/
theorem box1 (F : Frame5 P p q a b t o x5 y5) {c : Cell} (hc : c ∈ t 1) :
    (a - (o 1).W p q ≤ c.1 ∧ c.1 < a) ∧ 0 ≤ c.2 ∧ c.2 < (o 1).H p q := by
  have h := F.loc_bounds hc
  simp [loc] at h
  omega

/-- `box(T_3) = [a - W_3, a) x [b - H_3, b)`. -/
theorem box2 (F : Frame5 P p q a b t o x5 y5) {c : Cell} (hc : c ∈ t 2) :
    (a - (o 2).W p q ≤ c.1 ∧ c.1 < a) ∧ b - (o 2).H p q ≤ c.2 ∧ c.2 < b := by
  have h := F.loc_bounds hc
  simp [loc] at h
  omega

/-- `box(T_4) = [0, W_4) x [b - H_4, b)`. -/
theorem box3 (F : Frame5 P p q a b t o x5 y5) {c : Cell} (hc : c ∈ t 3) :
    (0 ≤ c.1 ∧ c.1 < (o 3).W p q) ∧ b - (o 3).H p q ≤ c.2 ∧ c.2 < b := by
  have h := F.loc_bounds hc
  simp [loc] at h
  omega

/-- `box(T_5) = [x5, x5 + W_5) x [y5, y5 + H_5)`. -/
theorem box4 (F : Frame5 P p q a b t o x5 y5) {c : Cell} (hc : c ∈ t 4) :
    (x5 ≤ c.1 ∧ c.1 < x5 + (o 4).W p q) ∧ y5 ≤ c.2 ∧ c.2 < y5 + (o 4).H p q := by
  have h := F.loc_bounds hc
  simp [loc] at h
  omega

/-- Every local column of a box holds a cell of `P`, whatever the code. -/
private theorem exists_fwd_col (F : Frame5 P p q a b t o x5 y5) (c : Orient) {x : ℤ}
    (h0 : 0 ≤ x) (h1 : x < c.W p q) : ∃ d ∈ P, (c.fwd p q d).1 = x := by
  obtain ⟨y, hl⟩ := F.left
  obtain ⟨y', hr⟩ := F.right
  obtain ⟨x', hb⟩ := F.bottom
  obtain ⟨x'', ht⟩ := F.top
  rcases c with ⟨_ | _, nx, ny⟩
  · have h1' : x < p := h1
    have hk : ∀ z : ℤ, 0 ≤ z → z < p → ∃ w : ℤ, (z, w) ∈ P := fun z hz hz' =>
      F.conn_P.exists_in_col hl hr hz (by dsimp only; omega)
    cases nx
    · obtain ⟨w, hw⟩ := hk x h0 h1'
      exact ⟨_, hw, by simp [Orient.fwd]⟩
    · obtain ⟨w, hw⟩ := hk (p - 1 - x) (by omega) (by omega)
      exact ⟨_, hw, by simp [Orient.fwd]⟩
  · have h1' : x < q := h1
    have hk : ∀ z : ℤ, 0 ≤ z → z < q → ∃ w : ℤ, (w, z) ∈ P := fun z hz hz' =>
      F.conn_P.exists_in_row hb ht hz (by dsimp only; omega)
    cases ny
    · obtain ⟨w, hw⟩ := hk x h0 h1'
      exact ⟨_, hw, by simp [Orient.fwd]⟩
    · obtain ⟨w, hw⟩ := hk (q - 1 - x) (by omega) (by omega)
      exact ⟨_, hw, by simp [Orient.fwd]⟩

/-- Every local row of a box holds a cell of `P`, whatever the code. -/
private theorem exists_fwd_row (F : Frame5 P p q a b t o x5 y5) (c : Orient) {y : ℤ}
    (h0 : 0 ≤ y) (h1 : y < c.H p q) : ∃ d ∈ P, (c.fwd p q d).2 = y := by
  obtain ⟨d, hd, hdy⟩ := F.exists_fwd_col c.tr h0 (by rwa [Orient.W_tr])
  refine ⟨d, hd, ?_⟩
  rw [← hdy]
  rcases c with ⟨_ | _, _, _⟩ <;> rfl

/-- The cell of the tile `t i` that comes from the cell `d` of `P`. -/
private theorem unloc_fwd_mem (F : Frame5 P p q a b t o x5 y5) (i : Fin 5) {d : Cell}
    (hd : d ∈ P) : unloc a b x5 y5 i ((o i).fwd p q d) ∈ t i := by
  rw [F.mem, loc_unloc, Orient.back_fwd]
  exact hd

/-- A tile has a cell in every column of its box. -/
private theorem exists_loc_col (F : Frame5 P p q a b t o x5 y5) (i : Fin 5) {x : ℤ}
    (h0 : 0 ≤ x) (h1 : x < (o i).W p q) : ∃ c ∈ t i, (loc a b x5 y5 i c).1 = x := by
  obtain ⟨d, hd, hdx⟩ := F.exists_fwd_col (o i) h0 h1
  exact ⟨_, F.unloc_fwd_mem i hd, by rw [loc_unloc, hdx]⟩

/-- A tile has a cell in every row of its box. -/
private theorem exists_loc_row (F : Frame5 P p q a b t o x5 y5) (i : Fin 5) {y : ℤ}
    (h0 : 0 ≤ y) (h1 : y < (o i).H p q) : ∃ c ∈ t i, (loc a b x5 y5 i c).2 = y := by
  obtain ⟨d, hd, hdy⟩ := F.exists_fwd_row (o i) h0 h1
  exact ⟨_, F.unloc_fwd_mem i hd, by rw [loc_unloc, hdy]⟩

/-- The sides that a corner tile meets hold its corner cell (Proposition 57 (b)). -/
private theorem corner_mem_side (F : Frame5 P p q a b t o x5 y5) {i : Fin 5} {j : Fin 4}
    (hj : PolyominoOddOrder.corner a b j ∈ t i) {c : Cell} (hc : c ∈ t i) {s : Fin 4} (hs : c ∈ side a b s) :
    PolyominoOddOrder.corner a b j ∈ side a b s :=
  corner_tile_sides P F.poly F.notRect a b t F.tiling F.cornersDistinct i j hj s ⟨c, hc, hs⟩

/-- A corner tile is less wide than the rectangle: `W_i ≤ a - 1` (`report-A2.md`,
section 1.1, by (F2)). -/
theorem W_le (F : Frame5 P p q a b t o x5 y5) {i : Fin 5} (hi : i ≠ 4) :
    (o i).W p q ≤ a - 1 := by
  have ha := F.two_le_a
  by_contra hlt
  obtain ⟨c, hc, hx⟩ := F.exists_loc_col i (x := a - 1) (by omega) (by omega)
  have hcR := F.sub_R i hc
  fin_cases i
  · have h := F.corner_mem_side (j := 0) F.corner0 hc (s := 1)
      (mem_rightCol.2 ⟨hcR, by simpa [loc] using hx⟩)
    have h' : (0 : ℤ) = a - 1 := (mem_rightCol.1 h).2
    omega
  · have h := F.corner_mem_side (j := 1) F.corner1 hc (s := 3)
      (mem_leftCol.2 ⟨hcR, by simpa [loc] using hx⟩)
    have h' : a - 1 = 0 := (mem_leftCol.1 h).2
    omega
  · have h := F.corner_mem_side (j := 2) F.corner2 hc (s := 3)
      (mem_leftCol.2 ⟨hcR, by simpa [loc] using hx⟩)
    have h' : a - 1 = 0 := (mem_leftCol.1 h).2
    omega
  · have h := F.corner_mem_side (j := 3) F.corner3 hc (s := 1)
      (mem_rightCol.2 ⟨hcR, by simpa [loc] using hx⟩)
    have h' : (0 : ℤ) = a - 1 := (mem_rightCol.1 h).2
    omega
  · exact hi rfl

/-- A corner tile is less high than the rectangle: `H_i ≤ b - 1`. -/
theorem H_le (F : Frame5 P p q a b t o x5 y5) {i : Fin 5} (hi : i ≠ 4) :
    (o i).H p q ≤ b - 1 := by
  have hb := F.two_le_b
  by_contra hlt
  obtain ⟨c, hc, hy⟩ := F.exists_loc_row i (y := b - 1) (by omega) (by omega)
  have hcR := F.sub_R i hc
  fin_cases i
  · have h := F.corner_mem_side (j := 0) F.corner0 hc (s := 2)
      (mem_topRow.2 ⟨hcR, by simpa [loc] using hy⟩)
    have h' : (0 : ℤ) = b - 1 := (mem_topRow.1 h).2
    omega
  · have h := F.corner_mem_side (j := 1) F.corner1 hc (s := 2)
      (mem_topRow.2 ⟨hcR, by simpa [loc] using hy⟩)
    have h' : (0 : ℤ) = b - 1 := (mem_topRow.1 h).2
    omega
  · have h := F.corner_mem_side (j := 2) F.corner2 hc (s := 0)
      (mem_bottomRow.2 ⟨hcR, by simpa [loc] using hy⟩)
    have h' : b - 1 = 0 := (mem_bottomRow.1 h).2
    omega
  · have h := F.corner_mem_side (j := 3) F.corner3 hc (s := 0)
      (mem_bottomRow.2 ⟨hcR, by simpa [loc] using hy⟩)
    have h' : b - 1 = 0 := (mem_bottomRow.1 h).2
    omega
  · exact hi rfl

/-- The box of `T_5` lies in `R a b`, and it is the box: each of its four sides
holds a cell of `T_5`. -/
theorem box4_in (F : Frame5 P p q a b t o x5 y5) :
    (0 ≤ x5 ∧ x5 + (o 4).W p q ≤ a) ∧ 0 ≤ y5 ∧ y5 + (o 4).H p q ≤ b := by
  have hp := F.two_le_p
  have hq := F.two_le_q
  have hW : 2 ≤ (o 4).W p q := by
    unfold Orient.W
    split <;> omega
  have hH : 2 ≤ (o 4).H p q := by
    unfold Orient.H
    split <;> omega
  obtain ⟨c1, h1, e1⟩ := F.exists_loc_col 4 (x := 0) le_rfl (by omega)
  obtain ⟨c2, h2, e2⟩ := F.exists_loc_col 4 (x := (o 4).W p q - 1) (by omega) (by omega)
  obtain ⟨c3, h3, e3⟩ := F.exists_loc_row 4 (y := 0) le_rfl (by omega)
  obtain ⟨c4, h4, e4⟩ := F.exists_loc_row 4 (y := (o 4).H p q - 1) (by omega) (by omega)
  have r1 := mem_R.1 (F.sub_R 4 h1)
  have r2 := mem_R.1 (F.sub_R 4 h2)
  have r3 := mem_R.1 (F.sub_R 4 h3)
  have r4 := mem_R.1 (F.sub_R 4 h4)
  simp [loc] at e1 e2 e3 e4
  omega

/-- Every cell of `R a b` lies in one of the five tiles, inside its box. The
workhorse of the cell arguments: `rcases F.cover_cases hc with h | h | h | h | h`
and `omega` on the boxes. -/
theorem cover_cases (F : Frame5 P p q a b t o x5 y5) {c : Cell} (hc : c ∈ R a b) :
    (c ∈ t 0 ∧ c.1 < (o 0).W p q ∧ c.2 < (o 0).H p q) ∨
    (c ∈ t 1 ∧ a - (o 1).W p q ≤ c.1 ∧ c.2 < (o 1).H p q) ∨
    (c ∈ t 2 ∧ a - (o 2).W p q ≤ c.1 ∧ b - (o 2).H p q ≤ c.2) ∨
    (c ∈ t 3 ∧ c.1 < (o 3).W p q ∧ b - (o 3).H p q ≤ c.2) ∨
    (c ∈ t 4 ∧ (x5 ≤ c.1 ∧ c.1 < x5 + (o 4).W p q) ∧ y5 ≤ c.2 ∧ c.2 < y5 + (o 4).H p q) := by
  obtain ⟨i, hi⟩ := F.tiling.exists_tile hc
  fin_cases i
  · exact Or.inl ⟨hi, (F.box0 hi).1.2, (F.box0 hi).2.2⟩
  · exact Or.inr (Or.inl ⟨hi, (F.box1 hi).1.1, (F.box1 hi).2.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hi, (F.box2 hi).1.1, (F.box2 hi).2.1⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hi, (F.box3 hi).1.2, (F.box3 hi).2.1⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hi, F.box4 hi⟩)))

/-! ## Lines of `P` (`report-A2.md`, section 1.3) -/

/-- The cells of `P` in column `x`, as a part of a whole column of the box. -/
private theorem filter_col_subset (F : Frame5 P p q a b t o x5 y5) (x : ℤ) :
    (P.filter fun c => c.1 = x) ⊆ ({x} : Finset ℤ) ×ˢ Finset.Ico 0 q := by
  intro c hc
  obtain ⟨hcP, hcx⟩ := Finset.mem_filter.1 hc
  rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico]
  exact ⟨hcx, (F.P_bounds hcP).2⟩

/-- The cells of `P` in row `y`, as a part of a whole row of the box. -/
private theorem filter_row_subset (F : Frame5 P p q a b t o x5 y5) (y : ℤ) :
    (P.filter fun c => c.2 = y) ⊆ Finset.Ico 0 p ×ˢ ({y} : Finset ℤ) := by
  intro c hc
  obtain ⟨hcP, hcy⟩ := Finset.mem_filter.1 hc
  rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico]
  exact ⟨(F.P_bounds hcP).1, hcy⟩

private theorem card_col (x q : ℤ) (hq : 0 ≤ q) :
    (((({x} : Finset ℤ) ×ˢ Finset.Ico 0 q).card : ℕ) : ℤ) = q := by
  rw [Finset.card_product, Finset.card_singleton, one_mul, Int.card_Ico]
  omega

private theorem card_row (y p : ℤ) (hp : 0 ≤ p) :
    (((Finset.Ico 0 p ×ˢ ({y} : Finset ℤ)).card : ℕ) : ℤ) = p := by
  rw [Finset.card_product, Finset.card_singleton, mul_one, Int.card_Ico]
  omega

/-- `P` meets every column of its box. -/
theorem colCount_pos (F : Frame5 P p q a b t o x5 y5) {x : ℤ} (h0 : 0 ≤ x) (h1 : x < p) :
    1 ≤ colCount P x := by
  obtain ⟨y, hl⟩ := F.left
  obtain ⟨y', hr⟩ := F.right
  obtain ⟨w, hw⟩ := F.conn_P.exists_in_col hl hr h0 (by dsimp only; omega)
  have h : 0 < (P.filter fun c => c.1 = x).card :=
    Finset.card_pos.2 ⟨(x, w), Finset.mem_filter.2 ⟨hw, rfl⟩⟩
  unfold colCount
  omega

/-- A column of `P` has at most `q` cells. -/
theorem colCount_le (F : Frame5 P p q a b t o x5 y5) (x : ℤ) : colCount P x ≤ q := by
  have h := Finset.card_le_card (F.filter_col_subset x)
  have hc := card_col x q (by have := F.two_le_q; omega)
  unfold colCount
  omega

/-- `P` has no cell outside the columns of its box. -/
theorem colCount_zero (F : Frame5 P p q a b t o x5 y5) {x : ℤ} (h : x < 0 ∨ p ≤ x) :
    colCount P x = 0 := by
  unfold colCount
  rw [Finset.filter_eq_empty_iff.2, Finset.card_empty, Nat.cast_zero]
  intro c hc hx
  have := F.P_bounds hc
  omega

/-- A column of `P` has `q` cells exactly when it is a whole column of the box. -/
theorem colCount_eq_iff (F : Frame5 P p q a b t o x5 y5) (x : ℤ) :
    colCount P x = q ↔ ∀ y : ℤ, 0 ≤ y → y < q → (x, y) ∈ P := by
  have hc := card_col x q (by have := F.two_le_q; omega)
  constructor
  · intro h y h0 h1
    have he := Finset.eq_of_subset_of_card_le (F.filter_col_subset x) (by
      unfold colCount at h
      omega)
    have hm : ((x, y) : Cell) ∈ P.filter fun c => c.1 = x := by
      rw [he, Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico]
      exact ⟨rfl, h0, h1⟩
    exact (Finset.mem_filter.1 hm).1
  · intro h
    have he : (P.filter fun c => c.1 = x) = ({x} : Finset ℤ) ×ˢ Finset.Ico 0 q := by
      refine Finset.Subset.antisymm (F.filter_col_subset x) ?_
      rintro ⟨x', y⟩ hm
      rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico] at hm
      obtain ⟨rfl, h0, h1⟩ := hm
      exact Finset.mem_filter.2 ⟨h y h0 h1, rfl⟩
    unfold colCount
    rw [he, hc]

/-- `P` meets every row of its box. -/
theorem rowCount_pos (F : Frame5 P p q a b t o x5 y5) {y : ℤ} (h0 : 0 ≤ y) (h1 : y < q) :
    1 ≤ rowCount P y := by
  obtain ⟨x, hb⟩ := F.bottom
  obtain ⟨x', ht⟩ := F.top
  obtain ⟨w, hw⟩ := F.conn_P.exists_in_row hb ht h0 (by dsimp only; omega)
  have h : 0 < (P.filter fun c => c.2 = y).card :=
    Finset.card_pos.2 ⟨(w, y), Finset.mem_filter.2 ⟨hw, rfl⟩⟩
  unfold rowCount
  omega

/-- A row of `P` has at most `p` cells. -/
theorem rowCount_le (F : Frame5 P p q a b t o x5 y5) (y : ℤ) : rowCount P y ≤ p := by
  have h := Finset.card_le_card (F.filter_row_subset y)
  have hc := card_row y p (by have := F.two_le_p; omega)
  unfold rowCount
  omega

/-- `P` has no cell outside the rows of its box. -/
theorem rowCount_zero (F : Frame5 P p q a b t o x5 y5) {y : ℤ} (h : y < 0 ∨ q ≤ y) :
    rowCount P y = 0 := by
  unfold rowCount
  rw [Finset.filter_eq_empty_iff.2, Finset.card_empty, Nat.cast_zero]
  intro c hc hy
  have := F.P_bounds hc
  omega

/-- A row of `P` has `p` cells exactly when it is a whole row of the box. -/
theorem rowCount_eq_iff (F : Frame5 P p q a b t o x5 y5) (y : ℤ) :
    rowCount P y = p ↔ ∀ x : ℤ, 0 ≤ x → x < p → (x, y) ∈ P := by
  have hc := card_row y p (by have := F.two_le_p; omega)
  constructor
  · intro h x h0 h1
    have he := Finset.eq_of_subset_of_card_le (F.filter_row_subset y) (by
      unfold rowCount at h
      omega)
    have hm : ((x, y) : Cell) ∈ P.filter fun c => c.2 = y := by
      rw [he, Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico]
      exact ⟨⟨h0, h1⟩, rfl⟩
    exact (Finset.mem_filter.1 hm).1
  · intro h
    have he : (P.filter fun c => c.2 = y) = Finset.Ico 0 p ×ˢ ({y} : Finset ℤ) := by
      refine Finset.Subset.antisymm (F.filter_row_subset y) ?_
      rintro ⟨x, y'⟩ hm
      rw [Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico] at hm
      obtain ⟨⟨h0, h1⟩, rfl⟩ := hm
      exact Finset.mem_filter.2 ⟨h x h0 h1, rfl⟩
    unfold rowCount
    rw [he, hc]

/-- The columns of `c.W` and the rows of `c.H` are those of the transposed code. -/
private theorem rowLine_eq_colLine_tr (c : Orient) (y : ℤ) :
    c.rowLine p q P y = c.tr.colLine p q P y := (c.colLine_tr p q P y).symm

/-- A tile meets every column of its box, whatever its code. -/
theorem colLine_pos (F : Frame5 P p q a b t o x5 y5) (c : Orient) {x : ℤ} (h0 : 0 ≤ x)
    (h1 : x < c.W p q) : 1 ≤ c.colLine p q P x := by
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;> simp [Orient.colLine, Orient.W] at h1 ⊢
  · exact F.colCount_pos h0 h1
  · exact F.colCount_pos h0 h1
  · exact F.colCount_pos (by omega) (by omega)
  · exact F.colCount_pos (by omega) (by omega)
  · exact F.rowCount_pos h0 h1
  · exact F.rowCount_pos (by omega) (by omega)
  · exact F.rowCount_pos h0 h1
  · exact F.rowCount_pos (by omega) (by omega)

/-- A local column of a tile has at most `H` cells. -/
theorem colLine_le (F : Frame5 P p q a b t o x5 y5) (c : Orient) (x : ℤ) :
    c.colLine p q P x ≤ c.H p q := by
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;> simp [Orient.colLine, Orient.H] <;>
    first
    | exact F.colCount_le _
    | exact F.rowCount_le _

/-- A tile has no cell outside the columns of its box. -/
theorem colLine_zero (F : Frame5 P p q a b t o x5 y5) (c : Orient) {x : ℤ}
    (h : x < 0 ∨ c.W p q ≤ x) : c.colLine p q P x = 0 := by
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;> simp [Orient.colLine, Orient.W] at h ⊢ <;>
    first
    | exact F.colCount_zero (by omega)
    | exact F.rowCount_zero (by omega)

/-- A local column is full exactly when the count is the height of the box. -/
theorem colLine_eq_iff (F : Frame5 P p q a b t o x5 y5) (c : Orient) (x : ℤ) :
    c.colLine p q P x = c.H p q ↔ ∀ y : ℤ, 0 ≤ y → y < c.H p q → c.back p q (x, y) ∈ P := by
  have key : ∀ (n : ℤ) (Q : ℤ → Prop),
      (∀ y, 0 ≤ y → y < n → Q y) ↔ ∀ y, 0 ≤ y → y < n → Q (n - 1 - y) := by
    intro n Q
    constructor
    · intro h y h0 h1
      exact h _ (by omega) (by omega)
    · intro h y h0 h1
      have := h (n - 1 - y) (by omega) (by omega)
      rwa [sub_sub_cancel] at this
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;>
    simp only [Orient.colLine, Orient.H, Orient.back, Bool.false_eq_true, ite_true, ite_false,
      F.colCount_eq_iff, F.rowCount_eq_iff]
  · exact key q _
  · exact key q _
  · exact key p _
  · exact key p _

/-- A tile meets every row of its box, whatever its code. -/
theorem rowLine_pos (F : Frame5 P p q a b t o x5 y5) (c : Orient) {y : ℤ} (h0 : 0 ≤ y)
    (h1 : y < c.H p q) : 1 ≤ c.rowLine p q P y := by
  rw [rowLine_eq_colLine_tr]
  exact F.colLine_pos c.tr h0 (by rwa [Orient.W_tr])

/-- A local row of a tile has at most `W` cells. -/
theorem rowLine_le (F : Frame5 P p q a b t o x5 y5) (c : Orient) (y : ℤ) :
    c.rowLine p q P y ≤ c.W p q := by
  rw [rowLine_eq_colLine_tr, ← Orient.H_tr]
  exact F.colLine_le c.tr y

/-- A tile has no cell outside the rows of its box. -/
theorem rowLine_zero (F : Frame5 P p q a b t o x5 y5) (c : Orient) {y : ℤ}
    (h : y < 0 ∨ c.H p q ≤ y) : c.rowLine p q P y = 0 := by
  rw [rowLine_eq_colLine_tr]
  exact F.colLine_zero c.tr (by rwa [Orient.W_tr])

/-- A local row is full exactly when the count is the width of the box. -/
theorem rowLine_eq_iff (F : Frame5 P p q a b t o x5 y5) (c : Orient) (y : ℤ) :
    c.rowLine p q P y = c.W p q ↔ ∀ x : ℤ, 0 ≤ x → x < c.W p q → c.back p q (x, y) ∈ P := by
  rw [rowLine_eq_colLine_tr, ← Orient.H_tr, F.colLine_eq_iff c.tr y]
  simp only [Orient.back_tr]

/-! ## Line counts of the tiles, from the codes -/

/-- A local column count is the number of cells of `P` whose local position lies
in that column. -/
private theorem colLine_eq_card (c : Orient) (x : ℤ) :
    c.colLine p q P x = ((P.filter fun d => (c.fwd p q d).1 = x).card : ℤ) := by
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;>
    simp only [Orient.colLine, Orient.fwd, Bool.false_eq_true, ite_true, ite_false, colCount,
      rowCount] <;> congr 2 <;> refine Finset.filter_congr fun d _ => ?_ <;> omega

/-- A local row count is the number of cells of `P` whose local position lies in
that row. -/
private theorem rowLine_eq_card (c : Orient) (y : ℤ) :
    c.rowLine p q P y = ((P.filter fun d => (c.fwd p q d).2 = y).card : ℤ) := by
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;>
    simp only [Orient.rowLine, Orient.fwd, Bool.false_eq_true, ite_true, ite_false, colCount,
      rowCount] <;> congr 2 <;> refine Finset.filter_congr fun d _ => ?_ <;> omega

/-- The local column of a cell depends on its column only, and determines it. -/
private theorem loc_fst_iff (i : Fin 5) (c : Cell) (x : ℤ) :
    (loc a b x5 y5 i c).1 = (loc a b x5 y5 i (x, 0)).1 ↔ c.1 = x := by
  fin_cases i <;> simp [loc]

/-- The local row of a cell depends on its row only, and determines it. -/
private theorem loc_snd_iff (i : Fin 5) (c : Cell) (y : ℤ) :
    (loc a b x5 y5 i c).2 = (loc a b x5 y5 i (0, y)).2 ↔ c.2 = y := by
  fin_cases i <;> simp [loc]

/-- Counting the cells of a tile by a property of the local position. -/
private theorem card_tile (F : Frame5 P p q a b t o x5 y5) (i : Fin 5) (A : Cell → Prop)
    [DecidablePred A] :
    ((t i).filter fun c => A (loc a b x5 y5 i c)).card =
      (P.filter fun d => A ((o i).fwd p q d)).card := by
  refine Finset.card_nbij' (fun c => (o i).back p q (loc a b x5 y5 i c))
    (fun d => unloc a b x5 y5 i ((o i).fwd p q d)) ?_ ?_ ?_ ?_
  · intro c hc
    obtain ⟨hc, hA⟩ := Finset.mem_filter.1 hc
    refine Finset.mem_filter.2 ⟨(F.mem i c).1 hc, ?_⟩
    rwa [Orient.fwd_back]
  · intro d hd
    obtain ⟨hd, hA⟩ := Finset.mem_filter.1 hd
    refine Finset.mem_filter.2 ⟨F.unloc_fwd_mem i hd, ?_⟩
    rwa [loc_unloc]
  · intro c _
    simp only [Orient.fwd_back, unloc_loc]
  · intro d _
    simp only [loc_unloc, Orient.back_fwd]

/-- The number of cells of the tile `t i` in column `x` is a line count of `P`,
read off from the code. -/
theorem colCount_tile (F : Frame5 P p q a b t o x5 y5) (i : Fin 5) (x : ℤ) :
    colCount (t i) x = (o i).colLine p q P (loc a b x5 y5 i (x, 0)).1 := by
  rw [colLine_eq_card, ← F.card_tile i fun c => c.1 = (loc a b x5 y5 i (x, 0)).1]
  simp only [loc_fst_iff]
  rfl

/-- The number of cells of the tile `t i` in row `y`. -/
theorem rowCount_tile (F : Frame5 P p q a b t o x5 y5) (i : Fin 5) (y : ℤ) :
    rowCount (t i) y = (o i).rowLine p q P (loc a b x5 y5 i (0, y)).2 := by
  rw [rowLine_eq_card, ← F.card_tile i fun c => c.2 = (loc a b x5 y5 i (0, y)).2]
  simp only [loc_snd_iff]
  rfl

/-- (2) of `report-A2.md`, section 1.3, for columns, the five terms written out:
`T_1` and `T_4` are read from the left, `T_2` and `T_3` from the right, `T_5`
from `x5`. -/
theorem col_sum (F : Frame5 P p q a b t o x5 y5) {x : ℤ} (h0 : 0 ≤ x) (h1 : x < a) :
    (o 0).colLine p q P x + (o 1).colLine p q P (a - 1 - x) + (o 2).colLine p q P (a - 1 - x) +
      (o 3).colLine p q P x + (o 4).colLine p q P (x - x5) = b := by
  have h := sum_colCount_of_cover t F.tiling.disjoint F.tiling.cover
    (by have := F.two_le_b; omega) h0 h1
  rw [Fin.sum_univ_five] at h
  simpa [F.colCount_tile, loc] using h

/-- (2) for rows: `T_1` and `T_2` are read from the bottom, `T_3` and `T_4` from
the top, `T_5` from `y5`. -/
theorem row_sum (F : Frame5 P p q a b t o x5 y5) {y : ℤ} (h0 : 0 ≤ y) (h1 : y < b) :
    (o 0).rowLine p q P y + (o 1).rowLine p q P y + (o 2).rowLine p q P (b - 1 - y) +
      (o 3).rowLine p q P (b - 1 - y) + (o 4).rowLine p q P (y - y5) = a := by
  have h := sum_rowCount_of_cover t F.tiling.disjoint F.tiling.cover
    (by have := F.two_le_a; omega) h0 h1
  rw [Fin.sum_univ_five] at h
  simpa [F.rowCount_tile, loc] using h

/-! ## Symmetries of the rectangle: the codes are permuted

Each statement gives *some* tiling with the new codes; the tiles themselves are
the images of the old ones and are not needed again. -/

/-- The image of a frame under an isometry `g` that carries `R a b` onto a
rectangle, with the tiles renamed by `r`: the new codes have to read the same
cells of `P`. -/
private theorem map_frame (F : Frame5 P p q a b t o x5 y5) (g : GridIso) {a' b' : ℤ}
    (hg : (R a b).image g.apply = R a' b') {r : Fin 5 → Fin 5} (hr : Function.Involutive r)
    (h4 : r 4 = 4) {o' : Fin 5 → Orient} {x5' y5' : ℤ}
    (hmem : ∀ i c, (o' i).back p q (loc a' b' x5' y5' i c) =
      (o (r i)).back p q (loc a b x5 y5 (r i) (g.inv.apply c)))
    (hcor : ∀ i, i ≠ 4 → (o' i).back p q (0, 0) = (o (r i)).back p q (0, 0)) :
    Frame5 P p q a' b' (fun i => (t (r i)).image g.apply) o' x5' y5' where
  poly := F.poly
  notRect := F.notRect
  sub := F.sub
  left := F.left
  right := F.right
  bottom := F.bottom
  top := F.top
  tiling := (F.tiling.map g hg).reindex hr.toPerm
  mem i c := by
    rw [GridIso.mem_image_iff, F.mem, hmem]
  corner i hi := by
    rw [hcor i hi]
    refine F.corner (r i) fun h => hi ?_
    rw [← hr i, h, h4]

/-- The reflection of `R a b` in its vertical midline exchanges `T_1`, `T_2` and
`T_3`, `T_4`; the codes of the corner tiles do not change. -/
theorem flipX (F : Frame5 P p q a b t o x5 y5) :
    ∃ t' : Fin 5 → Finset Cell,
      Frame5 P p q a b t' ![o 1, o 0, o 3, o 2, (o 4).reflX] (a - x5 - (o 4).W p q) y5 := by
  refine ⟨_, F.map_frame (GridIso.flipX a) (GridIso.image_R_flipX a b)
    (r := ![1, 0, 3, 2, 4]) (fun i => by fin_cases i <;> rfl) rfl ?_ ?_⟩
  · intro i c
    have hc : (GridIso.flipX a).inv.apply c = (a - 1 - c.1, c.2) := by
      simp [GridIso.flipX, GridIso.inv, GridIso.apply]
      omega
    rw [hc]
    fin_cases i
    · simp [loc]
    · simp [loc]
    · simp [loc]
    · simp [loc]
    · simp only [loc, Fin.reduceFinMk, Matrix.cons_val, Orient.back_reflX]
      congr 2
      omega
  · intro i hi
    fin_cases i
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd rfl hi

/-- The reflection of `R a b` in its horizontal midline exchanges `T_1`, `T_4`
and `T_2`, `T_3`. -/
theorem flipY (F : Frame5 P p q a b t o x5 y5) :
    ∃ t' : Fin 5 → Finset Cell,
      Frame5 P p q a b t' ![o 3, o 2, o 1, o 0, (o 4).reflY] x5 (b - y5 - (o 4).H p q) := by
  refine ⟨_, F.map_frame (GridIso.flipY b) (GridIso.image_R_flipY a b)
    (r := ![3, 2, 1, 0, 4]) (fun i => by fin_cases i <;> rfl) rfl ?_ ?_⟩
  · intro i c
    have hc : (GridIso.flipY b).inv.apply c = (c.1, b - 1 - c.2) := by
      simp [GridIso.flipY, GridIso.inv, GridIso.apply]
      omega
    rw [hc]
    fin_cases i
    · simp [loc]
    · simp [loc]
    · simp [loc]
    · simp [loc]
    · simp only [loc, Fin.reduceFinMk, Matrix.cons_val, Orient.back_reflY]
      congr 2
      omega
  · intro i hi
    fin_cases i
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd rfl hi

/-- The half turn of `R a b` exchanges `T_1`, `T_3` and `T_2`, `T_4`. -/
theorem halfTurn (F : Frame5 P p q a b t o x5 y5) :
    ∃ t' : Fin 5 → Finset Cell,
      Frame5 P p q a b t' ![o 2, o 3, o 0, o 1, (o 4).turn] (a - x5 - (o 4).W p q)
        (b - y5 - (o 4).H p q) := by
  obtain ⟨t', F'⟩ := F.flipX
  obtain ⟨t'', F''⟩ := F'.flipY
  refine ⟨t'', ?_⟩
  simpa [Orient.reflY_reflX] using F''

/-- The exchange of the two axes turns `R a b` into `R b a`, exchanges `T_2`
and `T_4`, and exchanges wide and tall in every code. -/
theorem transpose (F : Frame5 P p q a b t o x5 y5) :
    ∃ t' : Fin 5 → Finset Cell,
      Frame5 P p q b a t' ![(o 0).tr, (o 3).tr, (o 2).tr, (o 1).tr, (o 4).tr] y5 x5 := by
  refine ⟨_, F.map_frame GridIso.transpose (GridIso.image_R_transpose a b)
    (r := ![0, 3, 2, 1, 4]) (fun i => by fin_cases i <;> rfl) rfl ?_ ?_⟩
  · intro i c
    have hc : GridIso.transpose.inv.apply c = (c.2, c.1) := by
      simp [GridIso.transpose, GridIso.inv, GridIso.apply]
    rw [hc]
    fin_cases i <;> simp [loc, Orient.back_tr]
  · intro i hi
    fin_cases i <;> simp [Orient.back_tr]

/-! ## Symmetries of `P`: the corners of `box(P)` are renamed -/

/-- A tiling by `P` is a tiling by any polyomino congruent to `P`. -/
private theorem isTiling_of_congruent {P' : Finset Cell} (ht : IsTiling P a b t)
    (h : Congruent P P') : IsTiling P' a b t :=
  ⟨fun i => h.symm.trans (ht.congruent i), ht.disjoint, ht.cover⟩

/-- The mirror image of `P` in the vertical midline of its box, with the same
tiles. -/
theorem flipPX (F : Frame5 P p q a b t o x5 y5) :
    Frame5 (P.image (GridIso.flipX p).apply) p q a b t (fun i => (o i).pX) x5 y5 := by
  have hinv : ∀ c : Cell, (GridIso.flipX p).inv.apply c = (p - 1 - c.1, c.2) := by
    intro c
    simp [GridIso.flipX, GridIso.inv, GridIso.apply]
    omega
  refine ⟨GridIso.isPolyomino_image _ F.poly, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [isRectangular_image_iff]
    exact F.notRect
  · rw [← GridIso.image_R_flipX p q]
    exact Finset.image_subset_image F.sub
  · obtain ⟨y, hy⟩ := F.right
    exact ⟨y, (GridIso.mem_image_iff _ _ _).2 (by rw [hinv]; simpa using hy)⟩
  · obtain ⟨y, hy⟩ := F.left
    exact ⟨y, (GridIso.mem_image_iff _ _ _).2 (by rw [hinv]; simpa using hy)⟩
  · obtain ⟨x, hx⟩ := F.bottom
    exact ⟨p - 1 - x, (GridIso.mem_image_iff _ _ _).2 (by rw [hinv]; simpa using hx)⟩
  · obtain ⟨x, hx⟩ := F.top
    exact ⟨p - 1 - x, (GridIso.mem_image_iff _ _ _).2 (by rw [hinv]; simpa using hx)⟩
  · exact isTiling_of_congruent F.tiling ⟨_, rfl⟩
  · intro i c
    rw [GridIso.mem_image_iff, hinv, Orient.back_pX, F.mem]
    simp only [sub_sub_cancel, Prod.mk.eta]
  · intro i hi
    rw [GridIso.mem_image_iff, hinv, Orient.back_pX]
    simpa only [sub_sub_cancel, Prod.mk.eta] using F.corner i hi

/-- The mirror image of `P` in the horizontal midline of its box. -/
theorem flipPY (F : Frame5 P p q a b t o x5 y5) :
    Frame5 (P.image (GridIso.flipY q).apply) p q a b t (fun i => (o i).pY) x5 y5 := by
  have hinv : ∀ c : Cell, (GridIso.flipY q).inv.apply c = (c.1, q - 1 - c.2) := by
    intro c
    simp [GridIso.flipY, GridIso.inv, GridIso.apply]
    omega
  refine ⟨GridIso.isPolyomino_image _ F.poly, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [isRectangular_image_iff]
    exact F.notRect
  · rw [← GridIso.image_R_flipY p q]
    exact Finset.image_subset_image F.sub
  · obtain ⟨y, hy⟩ := F.left
    exact ⟨q - 1 - y, (GridIso.mem_image_iff _ _ _).2 (by rw [hinv]; simpa using hy)⟩
  · obtain ⟨y, hy⟩ := F.right
    exact ⟨q - 1 - y, (GridIso.mem_image_iff _ _ _).2 (by rw [hinv]; simpa using hy)⟩
  · obtain ⟨x, hx⟩ := F.top
    exact ⟨x, (GridIso.mem_image_iff _ _ _).2 (by rw [hinv]; simpa using hx)⟩
  · obtain ⟨x, hx⟩ := F.bottom
    exact ⟨x, (GridIso.mem_image_iff _ _ _).2 (by rw [hinv]; simpa using hx)⟩
  · exact isTiling_of_congruent F.tiling ⟨_, rfl⟩
  · intro i c
    rw [GridIso.mem_image_iff, hinv, Orient.back_pY, F.mem]
    simp only [sub_sub_cancel, Prod.mk.eta]
  · intro i hi
    rw [GridIso.mem_image_iff, hinv, Orient.back_pY]
    simpa only [sub_sub_cancel, Prod.mk.eta] using F.corner i hi

/-- The transpose of `P`; its box is `R q p`. -/
theorem transposeP (F : Frame5 P p q a b t o x5 y5) :
    Frame5 (P.image GridIso.transpose.apply) q p a b t (fun i => (o i).pT) x5 y5 := by
  have hinv : ∀ c : Cell, GridIso.transpose.inv.apply c = (c.2, c.1) := by
    intro c
    simp [GridIso.transpose, GridIso.inv, GridIso.apply]
  refine ⟨GridIso.isPolyomino_image _ F.poly, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [isRectangular_image_iff]
    exact F.notRect
  · rw [← GridIso.image_R_transpose p q]
    exact Finset.image_subset_image F.sub
  · obtain ⟨x, hx⟩ := F.bottom
    exact ⟨x, (GridIso.mem_image_iff _ _ _).2 (by rw [hinv]; exact hx)⟩
  · obtain ⟨x, hx⟩ := F.top
    exact ⟨x, (GridIso.mem_image_iff _ _ _).2 (by rw [hinv]; exact hx)⟩
  · obtain ⟨y, hy⟩ := F.left
    exact ⟨y, (GridIso.mem_image_iff _ _ _).2 (by rw [hinv]; exact hy)⟩
  · obtain ⟨y, hy⟩ := F.right
    exact ⟨y, (GridIso.mem_image_iff _ _ _).2 (by rw [hinv]; exact hy)⟩
  · exact isTiling_of_congruent F.tiling ⟨_, rfl⟩
  · intro i c
    rw [GridIso.mem_image_iff, hinv, Orient.back_pT, F.mem]
  · intro i hi
    rw [GridIso.mem_image_iff, hinv, Orient.back_pT]
    exact F.corner i hi

end Frame5

/-! ## The same symmetries for the two patterns -/

namespace FrameN

theorem flipX (F : FrameN P p q a b t o x5 y5) :
    ∃ t' : Fin 5 → Finset Cell,
      FrameN P p q a b t' ![o 1, o 0, o 3, o 2, (o 4).reflX] (a - x5 - (o 4).W p q) y5 := by
  obtain ⟨t', F'⟩ := F.toFrame5.flipX
  refine ⟨t', F', ?_, ?_, ?_, ?_⟩
  · have := F.x5_le; omega
  · exact F.y5_pos
  · have := F.x5_pos; simp; omega
  · have := F.y5_le; simpa using this

theorem flipY (F : FrameN P p q a b t o x5 y5) :
    ∃ t' : Fin 5 → Finset Cell,
      FrameN P p q a b t' ![o 3, o 2, o 1, o 0, (o 4).reflY] x5 (b - y5 - (o 4).H p q) := by
  obtain ⟨t', F'⟩ := F.toFrame5.flipY
  refine ⟨t', F', ?_, ?_, ?_, ?_⟩
  · exact F.x5_pos
  · have := F.y5_le; omega
  · have := F.x5_le; simpa using this
  · have := F.y5_pos; simp; omega

theorem halfTurn (F : FrameN P p q a b t o x5 y5) :
    ∃ t' : Fin 5 → Finset Cell,
      FrameN P p q a b t' ![o 2, o 3, o 0, o 1, (o 4).turn] (a - x5 - (o 4).W p q)
        (b - y5 - (o 4).H p q) := by
  obtain ⟨t', F'⟩ := F.toFrame5.halfTurn
  refine ⟨t', F', ?_, ?_, ?_, ?_⟩
  · have := F.x5_le; omega
  · have := F.y5_le; omega
  · have := F.x5_pos; simp; omega
  · have := F.y5_pos; simp; omega

theorem transpose (F : FrameN P p q a b t o x5 y5) :
    ∃ t' : Fin 5 → Finset Cell,
      FrameN P p q b a t' ![(o 0).tr, (o 3).tr, (o 2).tr, (o 1).tr, (o 4).tr] y5 x5 := by
  obtain ⟨t', F'⟩ := F.toFrame5.transpose
  refine ⟨t', F', F.y5_pos, F.x5_pos, ?_, ?_⟩
  · have := F.y5_le; simpa using this
  · have := F.x5_le; simpa using this

theorem flipPX (F : FrameN P p q a b t o x5 y5) :
    FrameN (P.image (GridIso.flipX p).apply) p q a b t (fun i => (o i).pX) x5 y5 :=
  ⟨F.toFrame5.flipPX, F.x5_pos, F.y5_pos, F.x5_le, F.y5_le⟩

theorem flipPY (F : FrameN P p q a b t o x5 y5) :
    FrameN (P.image (GridIso.flipY q).apply) p q a b t (fun i => (o i).pY) x5 y5 :=
  ⟨F.toFrame5.flipPY, F.x5_pos, F.y5_pos, F.x5_le, F.y5_le⟩

theorem transposeP (F : FrameN P p q a b t o x5 y5) :
    FrameN (P.image GridIso.transpose.apply) q p a b t (fun i => (o i).pT) x5 y5 :=
  ⟨F.toFrame5.transposeP, F.x5_pos, F.y5_pos, by simpa using F.x5_le, by simpa using F.y5_le⟩

end FrameN

namespace FrameO

/-- In pattern O only the reflection in the vertical midline keeps the pattern. -/
theorem flipX (F : FrameO P p q a b t o x5 y5) :
    ∃ t' : Fin 5 → Finset Cell,
      FrameO P p q a b t' ![o 1, o 0, o 3, o 2, (o 4).reflX] (a - x5 - (o 4).W p q) y5 := by
  obtain ⟨t', F'⟩ := F.toFrame5.flipX
  refine ⟨t', F', F.y5_eq, ?_, ?_, ?_⟩
  · have := F.x5_le; omega
  · have := F.x5_pos; simp; omega
  · have := F.h5_le; simpa using this

theorem flipPX (F : FrameO P p q a b t o x5 y5) :
    FrameO (P.image (GridIso.flipX p).apply) p q a b t (fun i => (o i).pX) x5 y5 :=
  ⟨F.toFrame5.flipPX, F.y5_eq, F.x5_pos, F.x5_le, F.h5_le⟩

theorem flipPY (F : FrameO P p q a b t o x5 y5) :
    FrameO (P.image (GridIso.flipY q).apply) p q a b t (fun i => (o i).pY) x5 y5 :=
  ⟨F.toFrame5.flipPY, F.y5_eq, F.x5_pos, F.x5_le, F.h5_le⟩

theorem transposeP (F : FrameO P p q a b t o x5 y5) :
    FrameO (P.image GridIso.transpose.apply) q p a b t (fun i => (o i).pT) x5 y5 :=
  ⟨F.toFrame5.transposeP, F.y5_eq, F.x5_pos, by simpa using F.x5_le, by simpa using F.h5_le⟩

end FrameO

end PolyominoOddOrder
