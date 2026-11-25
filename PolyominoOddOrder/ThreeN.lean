module

public import PolyominoOddOrder.ThreeCorners

/-!
# Case (I), three occupied corners, pattern N (`ThreeN.lean`)

Blueprint unit C2 (third increment), with `ThreeCorners.lean`. `report-A2.md`,
section 5.2: `|S| = 3` does not occur in pattern N.

* `p = q`: the kinds V, H, E of a corner tile (`kindV`, `kindH`, `isE`); where
  a kind H or V tile sits decides which side of `box(T_5)` is the full one
  (`n52_sq_H_bottom` and its three mirror images); the side equations leave four
  arrangements (`n52_sq_class`), all the same after a symmetry of the rectangle;
  the last bullet is `n52_sq_final`.
* `p > q`: the orientations alternate (`n52_types`); the marks solve two
  equations (`n52_alt_marks`), whose solutions have period two (half turn, (T4))
  or are `(B, E, E, A)` up to a quarter turn (`n52_BEEA`).

Entry statement (binding): `three_N`. A proof unit may reshape the nodes marked
PROVISIONAL.

Source: `theoretician/report-A2.md` (goals lab, commit `076d663`), section 5.2.
-/

@[expose] public section

namespace PolyominoOddOrder

open Orient (cornerP)

variable {P : Finset Cell} {p q a b : ℤ} {t : Fin 5 → Finset Cell} {o : Fin 5 → Orient}
  {x5 y5 : ℤ}

/-! ## `p = q`: kinds -/

/-- Kind V (`report-A2.md`, 5.2, `p = q`): the mark is `A` or `B` and the full
side at the mark is vertical in the tile. These are the codes tall `A` and
wide `B`. -/
def kindV (c : Orient) : Prop := c.negX = c.swap ∧ c.negY = !c.swap

/-- Kind H: the mark is `A` or `B` and the full side at the mark is horizontal
in the tile. These are the codes wide `A` and tall `B`. -/
def kindH (c : Orient) : Prop := c.negX = !c.swap ∧ c.negY = c.swap

/-- Kind E: the mark is `E`. -/
def isE (c : Orient) : Prop := c.negX = false ∧ c.negY = false

@[simp] theorem kindV_tr (c : Orient) : kindV c.tr ↔ kindH c := by
  simp [kindV, kindH]

@[simp] theorem kindH_tr (c : Orient) : kindH c.tr ↔ kindV c := by
  simp [kindV, kindH]

@[simp] theorem isE_tr (c : Orient) : isE c.tr ↔ isE c := by
  simp [isE]

/-- `report-A2.md`, 5.2, `p = q`, first bullet: a tile of kind H has a full
local column `k - 1`, the side of `P` at its end `E` ("the side of T_1 in column
k-1 is full"); it is the side `EB` or `EA` of `P`. -/
private theorem sq_H_col (F : Frame5 P p p a b t o x5 y5) (S : ThreeFull P p p) {c : Orient}
    (h : kindH c) {y : ℤ} (h0 : 0 ≤ y) (h1 : y < p) : c.back p p (p - 1, y) ∈ P := by
  rcases c with ⟨s, nx, ny⟩
  obtain ⟨hx, hy⟩ := h
  cases s <;> cases nx <;> cases ny <;> simp at hx hy
  · simpa [Orient.back] using (F.colCount_eq_iff 0).1 S.fullEB y h0 h1
  · simpa [Orient.back] using (F.rowCount_eq_iff 0).1 S.fullEA y h0 h1

/-- `report-A2.md`, 5.2, `p = q`, first bullet: if the full horizontal side of
`T_5` is the lowest row of `box(T_5)` (`revV = false`), `T_5` holds the whole row
`y5` of its box. -/
private theorem sq_low_row (F : Frame5 P p p a b t o x5 y5) (S : ThreeFull P p p)
    (hv : (o 4).revV = false) {X : ℤ} (h0 : x5 ≤ X) (h1 : X < x5 + p) :
    ((X, y5) : Cell) ∈ t 4 := by
  have hA := (F.rowCount_eq_iff 0).1 S.fullEA
  have hB := (F.colCount_eq_iff 0).1 S.fullEB
  rw [F.mem4]
  dsimp only
  rw [sub_self]
  generalize o 4 = c at hv ⊢
  rcases c with ⟨s, nx, ny⟩
  cases s <;> cases nx <;> cases ny <;> simp [Orient.revV] at hv <;> simp [Orient.back]
  · exact hA _ (by omega) (by omega)
  · exact hA _ (by omega) (by omega)
  · exact hB _ (by omega) (by omega)
  · exact hB _ (by omega) (by omega)

/-- `report-A2.md`, 5.2, `p = q`, first bullet: if `T_1` or `T_2` is of kind H,
the full horizontal side of `T_5` is the highest row of `box(T_5)`. For `T_1`:
its end `E` is `(k - 1, 0)` and its column `k - 1` is full; the columns of
`box(T_5)` contain `k - 1` (from `1 ≤ x5`, `x5 + k ≤ a - 1`, `a ≤ 2k`), so the
full horizontal side of `T_5` is in a row `≥ k`; were it the lowest row of
`box(T_5)`, then `y5 + k ≥ 2k ≥ b`. For `T_2` the same with the column
`a - k`. -/
theorem n52_sq_H_bottom (F : FrameN P p q a b t o x5 y5) (S : ThreeFull P p q) (hpq : p = q)
    (h : kindH (o 0) ∨ kindH (o 1)) : (o 4).revV = true := by
  subst hpq
  by_contra hv
  have hv' : (o 4).revV = false := by simpa using hv
  have hu0 := F.toFrame5.rowLine_le (o 0) 0
  have hu1 := F.toFrame5.rowLine_le (o 1) 0
  have hv0 := F.toFrame5.colLine_le (o 0) 0
  have hv3 := F.toFrame5.colLine_le (o 3) 0
  have hx := F.x5_pos
  have hy := F.y5_pos
  have hxl := F.x5_le
  have hyl := F.y5_le
  have hb := F.side_bottom
  have hl := F.side_left
  simp only [Orient.W, Orient.H, ite_self] at hu0 hu1 hv0 hv3 hxl hyl
  rcases h with h | h
  · -- `T_1` holds `(k - 1, y5)`, a cell of the lowest row of `box(T_5)`
    have h4 := sq_low_row F.toFrame5 S hv' (X := p - 1) (by omega) (by omega)
    have h0 : ((p - 1, y5) : Cell) ∈ t 0 :=
      (F.toFrame5.mem0 _).2 (sq_H_col F.toFrame5 S h (by omega) (by omega))
    exact Finset.disjoint_left.1 (F.tiling.disjoint 0 4 (by decide)) h0 h4
  · -- `T_2` holds `(a - k, y5)`
    have h4 := sq_low_row F.toFrame5 S hv' (X := a - p) (by omega) (by omega)
    have h1 : ((a - p, y5) : Cell) ∈ t 1 := by
      rw [F.toFrame5.mem1]
      dsimp only
      rw [show a - 1 - (a - p) = p - 1 by ring]
      exact sq_H_col F.toFrame5 S h (by omega) (by omega)
    exact Finset.disjoint_left.1 (F.tiling.disjoint 1 4 (by decide)) h1 h4

/-- `report-A2.md`, 5.2, `p = q`, second bullet ("turn R upside down"). -/
theorem n52_sq_H_top (F : FrameN P p q a b t o x5 y5) (S : ThreeFull P p q) (hpq : p = q)
    (h : kindH (o 2) ∨ kindH (o 3)) : (o 4).revV = false := by
  obtain ⟨t', F'⟩ := F.flipY
  have h' := n52_sq_H_bottom F' S hpq (by simpa [or_comm] using h)
  simpa using h'

/-- `report-A2.md`, 5.2, `p = q`, third bullet: kind V on the left; the full
vertical side of `T_5` is the rightmost column of `box(T_5)`. -/
theorem n52_sq_V_left (F : FrameN P p q a b t o x5 y5) (S : ThreeFull P p q) (hpq : p = q)
    (h : kindV (o 0) ∨ kindV (o 3)) : (o 4).revH = true := by
  obtain ⟨t', F'⟩ := F.transpose
  have h' := n52_sq_H_bottom F' S hpq (by simpa using h)
  simpa using h'

/-- `report-A2.md`, 5.2, `p = q`, third bullet: kind V on the right. -/
theorem n52_sq_V_right (F : FrameN P p q a b t o x5 y5) (S : ThreeFull P p q) (hpq : p = q)
    (h : kindV (o 1) ∨ kindV (o 2)) : (o 4).revH = false := by
  obtain ⟨t', F'⟩ := F.transpose
  have h' := n52_sq_H_top F' S hpq (by simpa [or_comm] using h)
  simpa using h'

/-- `report-A2.md`, 5.2, `p = q`, the kinds by their runs: kind V has `u_i < k`
(and `v_i = k`), kind H has `v_i < k` (and `u_i = k`), kind E has
`u_i = v_i = k`; every code whose mark is not `D` has one of the three kinds. -/
private theorem sq_kind (S : ThreeFull P p p) {c : Orient}
    (hm : ¬ (c.negX = true ∧ c.negY = true)) :
    (kindV c ↔ c.rowLine p p P 0 < p) ∧ (kindH c ↔ c.colLine p p P 0 < p) ∧
      (isE c ↔ ¬ c.rowLine p p P 0 < p ∧ ¬ c.colLine p p P 0 < p) ∧
      c.rowLine p p P 0 ≤ p ∧ c.colLine p p P 0 ≤ p ∧
      ¬ (c.rowLine p p P 0 < p ∧ c.colLine p p P 0 < p) := by
  have hα := S.alpha_lt
  have hβ := S.beta_lt
  have hA := S.fullEA
  have hB := S.fullEB
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;>
    simp [kindV, kindH, isE, Orient.hrun_eq, Orient.vrun_eq, hA, hB] at hm ⊢ <;> omega

/-- `report-A2.md`, 5.2, `p = q`, fourth bullet, the last step: with `A_i` for
"`T_i` is of kind V" and `B_i` for kind H, the pairs of each kind as they are
left by (1) and the three bullets before; "A pair of one kind and a pair of the
other kind would share a tile"; not all marks are `E`. -/
private theorem sq_class_prop {A0 A1 A2 A3 B0 B1 B2 B3 : Prop}
    (X0 : ¬ (A0 ∧ B0)) (X1 : ¬ (A1 ∧ B1)) (X2 : ¬ (A2 ∧ B2)) (X3 : ¬ (A3 ∧ B3))
    (xE : ¬ ((¬ A0 ∧ ¬ B0) ∧ (¬ A1 ∧ ¬ B1) ∧ (¬ A2 ∧ ¬ B2) ∧ (¬ A3 ∧ ¬ B3)))
    (hV : (A0 ↔ A3) ∧ (A1 ↔ A2) ∧ ¬ (A0 ∧ A1))
    (hH : (B0 ↔ B1) ∧ (B2 ↔ B3) ∧ ¬ (B0 ∧ B2)) :
    (A0 ∧ A3 ∧ (¬ A1 ∧ ¬ B1) ∧ (¬ A2 ∧ ¬ B2)) ∨
    (A1 ∧ A2 ∧ (¬ A0 ∧ ¬ B0) ∧ (¬ A3 ∧ ¬ B3)) ∨
    (B0 ∧ B1 ∧ (¬ A2 ∧ ¬ B2) ∧ (¬ A3 ∧ ¬ B3)) ∨
    (B2 ∧ B3 ∧ (¬ A0 ∧ ¬ B0) ∧ (¬ A1 ∧ ¬ B1)) := by
  by_cases a0 : A0 <;> by_cases a1 : A1 <;> by_cases b0 : B0 <;> by_cases b2 : B2 <;> simp_all

/-- `report-A2.md`, 5.2, `p = q`, fourth bullet, the count: with `u_i`, `v_i` the
runs, kind V read as `u_i < k` and kind H as `v_i < k`. By (1) and the exclusion
of kind V left and right, "the tiles of kind V are none, or exactly T_1 and T_4
..., or exactly T_2 and T_3"; the same for kind H with the pairs at the bottom
and on top. -/
private theorem sq_class_arith {p a b u0 u1 u2 u3 v0 v1 v2 v3 : ℤ}
    (hb : u0 + u1 = a) (ht : u2 + u3 = a) (hl : v0 + v3 = b) (hr : v1 + v2 = b)
    (U0 : u0 ≤ p) (U1 : u1 ≤ p) (U2 : u2 ≤ p) (U3 : u3 ≤ p)
    (W0 : v0 ≤ p) (W1 : v1 ≤ p) (W2 : v2 ≤ p) (W3 : v3 ≤ p)
    (X0 : ¬ (u0 < p ∧ v0 < p)) (X1 : ¬ (u1 < p ∧ v1 < p)) (X2 : ¬ (u2 < p ∧ v2 < p))
    (X3 : ¬ (u3 < p ∧ v3 < p))
    (xV : ¬ ((u0 < p ∨ u3 < p) ∧ (u1 < p ∨ u2 < p)))
    (xH : ¬ ((v0 < p ∨ v1 < p) ∧ (v2 < p ∨ v3 < p)))
    (xE : ¬ ((¬ u0 < p ∧ ¬ v0 < p) ∧ (¬ u1 < p ∧ ¬ v1 < p) ∧ (¬ u2 < p ∧ ¬ v2 < p) ∧
      (¬ u3 < p ∧ ¬ v3 < p))) :
    (u0 < p ∧ u3 < p ∧ (¬ u1 < p ∧ ¬ v1 < p) ∧ (¬ u2 < p ∧ ¬ v2 < p)) ∨
    (u1 < p ∧ u2 < p ∧ (¬ u0 < p ∧ ¬ v0 < p) ∧ (¬ u3 < p ∧ ¬ v3 < p)) ∨
    (v0 < p ∧ v1 < p ∧ (¬ u2 < p ∧ ¬ v2 < p) ∧ (¬ u3 < p ∧ ¬ v3 < p)) ∨
    (v2 < p ∧ v3 < p ∧ (¬ u0 < p ∧ ¬ v0 < p) ∧ (¬ u1 < p ∧ ¬ v1 < p)) :=
  sq_class_prop X0 X1 X2 X3 xE (by omega) (by omega)

/-- `report-A2.md`, 5.2, `p = q`, fourth bullet: by (1), `2k - a` is the sum of
`k - u_i` over `T_1, T_2` and over `T_3, T_4`, and the same for `b` and the
`v_i`. With the three bullets before: the tiles of kind V are none, or exactly
`T_1, T_4`, or exactly `T_2, T_3`; those of kind H none, or exactly `T_1, T_2`,
or exactly `T_3, T_4`; only one kind occurs besides E; not all marks are `E`
(`Three.not_sameMarks_N`). -/
theorem n52_sq_class (F : FrameN P p q a b t o x5 y5) (S : ThreeFull P p q) (hpq : p = q) :
    (kindV (o 0) ∧ kindV (o 3) ∧ isE (o 1) ∧ isE (o 2)) ∨
    (kindV (o 1) ∧ kindV (o 2) ∧ isE (o 0) ∧ isE (o 3)) ∨
    (kindH (o 0) ∧ kindH (o 1) ∧ isE (o 2) ∧ isE (o 3)) ∨
    (kindH (o 2) ∧ kindH (o 3) ∧ isE (o 0) ∧ isE (o 1)) := by
  subst hpq
  -- not all marks are `E` (3)
  have xE : ¬ (isE (o 0) ∧ isE (o 1) ∧ isE (o 2) ∧ isE (o 3)) := by
    rintro ⟨e0, e1, e2, e3⟩
    refine S.not_sameMarks_N F fun i hi => ?_
    fin_cases i
    · exact ⟨rfl, rfl⟩
    · exact ⟨e1.1.trans e0.1.symm, e1.2.trans e0.2.symm⟩
    · exact ⟨e2.1.trans e0.1.symm, e2.2.trans e0.2.symm⟩
    · exact ⟨e3.1.trans e0.1.symm, e3.2.trans e0.2.symm⟩
    · exact absurd rfl hi
  -- kind H not both at the bottom and on top, kind V not both left and right
  have xH : ¬ ((kindH (o 0) ∨ kindH (o 1)) ∧ (kindH (o 2) ∨ kindH (o 3))) := by
    rintro ⟨h, h'⟩
    have e := n52_sq_H_bottom F S rfl h
    rw [n52_sq_H_top F S rfl h'] at e
    exact Bool.false_ne_true e
  have xV : ¬ ((kindV (o 0) ∨ kindV (o 3)) ∧ (kindV (o 1) ∨ kindV (o 2))) := by
    rintro ⟨h, h'⟩
    have e := n52_sq_V_left F S rfl h
    rw [n52_sq_V_right F S rfl h'] at e
    exact Bool.false_ne_true e
  -- the kinds by the runs, and (1)
  obtain ⟨V0, H0, E0, U0, W0, X0⟩ := sq_kind S (S.mark F.toFrame5 (i := 0) (by decide))
  obtain ⟨V1, H1, E1, U1, W1, X1⟩ := sq_kind S (S.mark F.toFrame5 (i := 1) (by decide))
  obtain ⟨V2, H2, E2, U2, W2, X2⟩ := sq_kind S (S.mark F.toFrame5 (i := 2) (by decide))
  obtain ⟨V3, H3, E3, U3, W3, X3⟩ := sq_kind S (S.mark F.toFrame5 (i := 3) (by decide))
  have hb := F.side_bottom
  have ht := F.side_top
  have hl := F.side_left
  have hr := F.side_right
  simp only [V0, V1, V2, V3, H0, H1, H2, H3, E0, E1, E2, E3] at xE xH xV ⊢
  exact sq_class_arith hb ht hl hr U0 U1 U2 U3 W0 W1 W2 W3 X0 X1 X2 X3 xV xH xE

/-- `report-A2.md`, 5.2, `p = q`, last bullet: if the full vertical side of `T_5`
is the rightmost column of `box(T_5)` (`revH = true`), `T_5` holds the whole
column `x* = x5 + k - 1` of its box. -/
private theorem sq_right_col (F : Frame5 P p p a b t o x5 y5) (S : ThreeFull P p p)
    (hh : (o 4).revH = true) {Y : ℤ} (h0 : y5 ≤ Y) (h1 : Y < y5 + p) :
    ((x5 + p - 1, Y) : Cell) ∈ t 4 := by
  have hA := (F.rowCount_eq_iff 0).1 S.fullEA
  have hB := (F.colCount_eq_iff 0).1 S.fullEB
  rw [F.mem4]
  dsimp only
  rw [show x5 + p - 1 - x5 = p - 1 by ring]
  generalize o 4 = c at hh ⊢
  rcases c with ⟨s, nx, ny⟩
  cases s <;> cases nx <;> cases ny <;> simp [Orient.revH] at hh <;> simp [Orient.back]
  · exact hB _ (by omega) (by omega)
  · exact hB _ (by omega) (by omega)
  · exact hA _ (by omega) (by omega)
  · exact hA _ (by omega) (by omega)

/-- `report-A2.md`, 5.2, `p = q`, last bullet: a tile of kind V and a tile of
kind E with the same direction of `box(P)` horizontal. The run of the mark of the
first (`wB`: the side `BD`; `tA`: the side `AD`) is read by the second along its
local row `k - 1`, from its corner `B` or `A` ("the cells of T_2 in row k-1 would
include the run of m_1"). -/
private theorem sq_VE_back {c d : Orient} (hc : kindV c) (hd : isE d) (hs : c.swap = d.swap)
    (x : ℤ) : c.back p p (x, 0) = d.back p p (x, p - 1) := by
  rcases c with ⟨s, nx, ny⟩
  rcases d with ⟨s', nx', ny'⟩
  obtain ⟨h1, h2⟩ := hc
  obtain ⟨h3, h4⟩ := hd
  simp only at h1 h2 h3 h4 hs
  subst h3 h4 hs
  cases s <;> cases nx <;> cases ny <;> simp at h1 h2 <;> simp [Orient.back]

/-- `report-A2.md`, 5.2, `p = q`, last bullet: `T_1`, `T_4` of kind V and `T_2`,
`T_3` of kind E. Then `a = k + sigma`, `b = 2k` with `sigma = u_1 = u_4`; the
full vertical side of `T_5` is in a column `x*` with `k ≤ x* ≤ a - 2` and holds
`(x*, k - 1)` and `(x*, k)`; the corner of `T_2` at `(a - 1, k - 1)` and the
corner of `T_3` at `(a - 1, k)` are the element of `{A, B}` that is not `m_1`,
and `m_1 = m_4`; so the reflection of `R a b` in its horizontal midline permutes
the corner tiles (`o 0 = o 3`, `o 1 = o 2`), against (T4) (`Frame5.T4_flipY`,
`Three.no_reflection`). -/
theorem n52_sq_final (F : FrameN P p q a b t o x5 y5) (S : ThreeFull P p q) (hpq : p = q)
    (h0 : kindV (o 0)) (h3 : kindV (o 3)) (h1 : isE (o 1)) (h2 : isE (o 2)) : False := by
  subst hpq
  obtain ⟨V0, -, -, U0, W0, X0⟩ := sq_kind S (S.mark F.toFrame5 (i := 0) (by decide))
  obtain ⟨-, -, E1, U1, W1, -⟩ := sq_kind S (S.mark F.toFrame5 (i := 1) (by decide))
  obtain ⟨-, -, E2, U2, W2, -⟩ := sq_kind S (S.mark F.toFrame5 (i := 2) (by decide))
  obtain ⟨V3, -, -, U3, W3, X3⟩ := sq_kind S (S.mark F.toFrame5 (i := 3) (by decide))
  have u0 := V0.1 h0
  have u3 := V3.1 h3
  have e1 := E1.1 h1
  have e2 := E2.1 h2
  have hb := F.side_bottom
  have ht := F.side_top
  have hl := F.side_left
  -- `b = 2k`, `a = k + sigma`, `sigma = u_1 = u_4`
  have hb2 : b = 2 * p := by omega
  have ha : a = p + (o 0).rowLine p p P 0 := by omega
  have hu : (o 3).rowLine p p P 0 = (o 0).rowLine p p P 0 := by omega
  -- the full vertical side of `T_5` is the column `x* = x5 + k - 1`, which holds
  -- `(x*, k - 1)` and `(x*, k)`
  have hH := n52_sq_V_left F S rfl (Or.inl h0)
  have hx := F.x5_pos
  have hy := F.y5_pos
  have hxl := F.x5_le
  have hyl := F.y5_le
  simp only [Orient.W, Orient.H, ite_self] at hxl hyl
  have c4a := sq_right_col F.toFrame5 S hH (Y := p - 1) (by omega) (by omega)
  have c4b := sq_right_col F.toFrame5 S hH (Y := p) (by omega) (by omega)
  -- the corner of `T_2` at `(a - 1, k - 1)` is not `m_1`, nor `m_4`
  have s10 : ¬ (o 1).swap = (o 0).swap := by
    intro hs
    have hc : ((x5 + p - 1, p - 1) : Cell) ∈ t 1 := by
      rw [F.toFrame5.mem1]
      dsimp only
      rw [← sq_VE_back h0 h1 hs.symm]
      exact (F.toFrame5.hside (i := 0) (by decide) _).2 ⟨by omega, by omega⟩
    exact Finset.disjoint_left.1 (F.tiling.disjoint 1 4 (by decide)) hc c4a
  have s13 : ¬ (o 1).swap = (o 3).swap := by
    intro hs
    have hc : ((x5 + p - 1, p - 1) : Cell) ∈ t 1 := by
      rw [F.toFrame5.mem1]
      dsimp only
      rw [← sq_VE_back h3 h1 hs.symm]
      exact (F.toFrame5.hside (i := 3) (by decide) _).2 ⟨by omega, by omega⟩
    exact Finset.disjoint_left.1 (F.tiling.disjoint 1 4 (by decide)) hc c4a
  -- the same for the corner of `T_3` at `(a - 1, k)`
  have s20 : ¬ (o 2).swap = (o 0).swap := by
    intro hs
    have hc : ((x5 + p - 1, p) : Cell) ∈ t 2 := by
      rw [F.toFrame5.mem2]
      dsimp only
      rw [show b - 1 - p = p - 1 by omega, ← sq_VE_back h0 h2 hs.symm]
      exact (F.toFrame5.hside (i := 0) (by decide) _).2 ⟨by omega, by omega⟩
    exact Finset.disjoint_left.1 (F.tiling.disjoint 2 4 (by decide)) hc c4b
  have s23 : ¬ (o 2).swap = (o 3).swap := by
    intro hs
    have hc : ((x5 + p - 1, p) : Cell) ∈ t 2 := by
      rw [F.toFrame5.mem2]
      dsimp only
      rw [show b - 1 - p = p - 1 by omega, ← sq_VE_back h3 h2 hs.symm]
      exact (F.toFrame5.hside (i := 3) (by decide) _).2 ⟨by omega, by omega⟩
    exact Finset.disjoint_left.1 (F.tiling.disjoint 2 4 (by decide)) hc c4b
  -- so `m_1 = m_4`, `T_2` and `T_3` have the same code, and the reflection of `R`
  -- in its horizontal midline permutes the corner tiles: against (T4)
  have hs03 : (o 0).swap = (o 3).swap :=
    bool_eq_of_ne (fun h => s10 h.symm) (fun h => s13 h.symm)
  have hs12 : (o 1).swap = (o 2).swap :=
    bool_eq_of_ne s10 s20
  have e03 : o 0 = o 3 :=
    Orient.ext hs03 (by rw [h0.1, h3.1, hs03]) (by rw [h0.2, h3.2, hs03])
  have e12 : o 1 = o 2 := Orient.ext hs12 (by rw [h1.1, h2.1]) (by rw [h1.2, h2.2])
  obtain ⟨-, hsym⟩ := F.toFrame5.T4_flipY e03 e12
  refine S.no_reflection ?_
  cases h : (o 4).swap
  · exact Or.inr fun c => by simpa [h] using hsym c
  · exact Or.inl fun c => by simpa [h] using hsym c

/-- `report-A2.md`, 5.2, `p = q`: "Exchange the axes and reflect, so that T_1 and
T_4 are of kind V, T_2 and T_3 of kind E." -/
theorem n52_sq (F : FrameN P p q a b t o x5 y5) (S : ThreeFull P p q) (hpq : p = q) :
    False := by
  rcases n52_sq_class F S hpq with ⟨a0, a3, a1, a2⟩ | ⟨a1, a2, a0, a3⟩ | ⟨a0, a1, a2, a3⟩ |
    ⟨a2, a3, a0, a1⟩
  · exact n52_sq_final F S hpq a0 a3 a1 a2
  · obtain ⟨t', F'⟩ := F.flipX
    exact n52_sq_final F' S hpq (by simpa using a1) (by simpa using a2) (by simpa using a0)
      (by simpa using a3)
  · obtain ⟨t', F'⟩ := F.transpose
    exact n52_sq_final F' S hpq (by simpa using a0) (by simpa using a1) (by simpa using a3)
      (by simpa using a2)
  · obtain ⟨t', F'⟩ := F.flipY
    obtain ⟨t'', F''⟩ := F'.transpose
    exact n52_sq_final F'' S hpq (by simpa using a3) (by simpa using a2) (by simpa using a0)
      (by simpa using a1)

/-! ## `p > q` -/

/-- A corner tile whose two runs are whole sides of its box has the mark `E`
(`report-A2.md`, section 5: the runs of `A` along `AD` and of `B` along `BD`
are `alpha < q` and `beta < p`). -/
private theorem bt_markE (S : ThreeFull P p q) (c : Orient) (hr : c.rowLine p q P 0 = c.W p q)
    (hc : c.colLine p q P 0 = c.H p q) : c.negX = false ∧ c.negY = false := by
  have hα := S.alpha_lt
  have hβ := S.beta_lt
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;>
    simp [Orient.rowLine, Orient.colLine, Orient.W, Orient.H] at hr hc ⊢ <;> omega

/-- `report-A2.md`, 5.2, `p > q`, the first three bullets: the orientations
alternate. Lemma 5.1 applies to all four sides. All equal: all runs are whole
sides, so all marks are `E`, against (3). Exactly one different: `b = 2H`,
`a = 2W` and `2W ≤ H + W`, `2H ≤ W + H`. Two equal at one side and the other two
equal, of the other orientation: two opposite sides of `R a b` have the lengths
`2p` and `2q`. PROVISIONAL: one node here, three in the report. -/
theorem n52_types (F : FrameN P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p) :
    ((o 0).swap = false ∧ (o 1).swap = true ∧ (o 2).swap = false ∧ (o 3).swap = true) ∨
      ((o 0).swap = true ∧ (o 1).swap = false ∧ (o 2).swap = true ∧ (o 3).swap = false) := by
  have F5 := F.toFrame5
  have L0 := lemma51_bottom F5 S hq F.y5_pos
  have L1 := lemma51_top F5 S hq F.y5_le
  have L2 := lemma51_left F5 S hq F.x5_pos
  have L3 := lemma51_right F5 S hq F.x5_le
  -- all equal: all runs are whole sides, so all marks are `E`, against (3)
  have hall : ¬ ((o 0).swap = (o 1).swap ∧ (o 1).swap = (o 2).swap ∧
      (o 2).swap = (o 3).swap) := by
    rintro ⟨e01, e12, e23⟩
    obtain ⟨r0, r1⟩ := L0 e01
    obtain ⟨r2, r3⟩ := L1 e23
    obtain ⟨c0, c3⟩ := L2 (e01.trans (e12.trans e23))
    obtain ⟨c1, c2⟩ := L3 e12
    have m0 := bt_markE S (o 0) r0 c0
    have m1 := bt_markE S (o 1) r1 c1
    have m2 := bt_markE S (o 2) r2 c2
    have m3 := bt_markE S (o 3) r3 c3
    refine S.not_sameMarks_N F fun i hi => ?_
    fin_cases i <;> simp [m0.1, m0.2, m1.1, m1.2, m2.1, m2.2, m3.1, m3.2] at hi ⊢
  have hb := F.side_bottom
  have ht := F.side_top
  have hl := F.side_left
  have hr := F.side_right
  have u0 := (F5.hrun_bounds 0).2
  have u1 := (F5.hrun_bounds 1).2
  have u2 := (F5.hrun_bounds 2).2
  have u3 := (F5.hrun_bounds 3).2
  have v0 := (F5.vrun_bounds 0).2
  have v1 := (F5.vrun_bounds 1).2
  have v2 := (F5.vrun_bounds 2).2
  have v3 := (F5.vrun_bounds 3).2
  -- exactly one different, or two pairs: the side equations (1) force `p = q`
  cases h0 : (o 0).swap <;> cases h1 : (o 1).swap <;> cases h2 : (o 2).swap <;>
    cases h3 : (o 3).swap <;>
    simp [h0, h1, h2, h3, Orient.W, Orient.H] at L0 L1 L2 L3 hall u0 u1 u2 u3 v0 v1 v2 v3 ⊢ <;>
    omega

/-- The finite analysis of the marks of `report-A2.md`, 5.2, `p > q`, for four
codes and the four side counts of `P`: `T_1`, `T_3` wide, `T_2`, `T_4` tall, no
mark is `D`, and the side equations (1) hold. Then the marks have period two, or
`d_A = d_B` and they are `(B, E, E, A)`, `(A, B, E, E)`, `(E, A, B, E)` or
`(E, E, A, B)`. All 81 choices of marks: `simp` computes the runs, `omega` uses
`alpha < q`, `beta < p`. -/
theorem n52_alt_marks_aux {P : Finset Cell} {p q a b : ℤ} (c0 c1 c2 c3 : Orient)
    (hEA : rowCount P 0 = p) (hEB : colCount P 0 = q) (hα : colCount P (p - 1) < q)
    (hβ : rowCount P (q - 1) < p)
    (h0 : c0.swap = false) (h1 : c1.swap = true) (h2 : c2.swap = false) (h3 : c3.swap = true)
    (m0 : ¬ (c0.negX = true ∧ c0.negY = true)) (m1 : ¬ (c1.negX = true ∧ c1.negY = true))
    (m2 : ¬ (c2.negX = true ∧ c2.negY = true)) (m3 : ¬ (c3.negX = true ∧ c3.negY = true))
    (hb : c0.rowLine p q P 0 + c1.rowLine p q P 0 = a)
    (ht : c2.rowLine p q P 0 + c3.rowLine p q P 0 = a)
    (hl : c0.colLine p q P 0 + c3.colLine p q P 0 = b)
    (hr : c1.colLine p q P 0 + c2.colLine p q P 0 = b) :
    (c0 = c2 ∧ c1 = c3) ∨
      (p - rowCount P (q - 1) = q - colCount P (p - 1) ∧
        ((c0 = Orient.wB ∧ c1 = Orient.tE ∧ c2 = Orient.wE ∧ c3 = Orient.tA) ∨
          (c0 = Orient.wA ∧ c1 = Orient.tB ∧ c2 = Orient.wE ∧ c3 = Orient.tE) ∨
          (c0 = Orient.wE ∧ c1 = Orient.tA ∧ c2 = Orient.wB ∧ c3 = Orient.tE) ∨
          (c0 = Orient.wE ∧ c1 = Orient.tE ∧ c2 = Orient.wA ∧ c3 = Orient.tB))) := by
  rcases c0 with ⟨s0, x0, y0⟩
  rcases c1 with ⟨s1, x1, y1⟩
  rcases c2 with ⟨s2, x2, y2⟩
  rcases c3 with ⟨s3, x3, y3⟩
  simp only at h0 h1 h2 h3
  subst h0 h1 h2 h3
  cases x0 <;> cases y0 <;> cases x1 <;> cases y1 <;> cases x2 <;> cases y2 <;> cases x3 <;>
    cases y3 <;>
    simp [Orient.rowLine, Orient.colLine, Orient.wE, Orient.wA, Orient.wB, Orient.tE,
      Orient.tA, Orient.tB, hEA, hEB] at m0 m1 m2 m3 hb ht hl hr ⊢ <;>
    omega

/-- **`report-A2.md`, 5.2, `p > q`, "The solutions other than the period-two
ones".** With `T_1`, `T_3` wide and `T_2`, `T_4` tall, the codes have period two
(`o 0 = o 2`, `o 1 = o 3`), or `d_A = d_B` and the marks are one of the four
solutions. -/
theorem n52_alt_marks (F : FrameN P p q a b t o x5 y5) (S : ThreeFull P p q)
    (h0 : (o 0).swap = false) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) :
    (o 0 = o 2 ∧ o 1 = o 3) ∨
      (p - rowCount P (q - 1) = q - colCount P (p - 1) ∧
        ((o 0 = Orient.wB ∧ o 1 = Orient.tE ∧ o 2 = Orient.wE ∧ o 3 = Orient.tA) ∨
          (o 0 = Orient.wA ∧ o 1 = Orient.tB ∧ o 2 = Orient.wE ∧ o 3 = Orient.tE) ∨
          (o 0 = Orient.wE ∧ o 1 = Orient.tA ∧ o 2 = Orient.wB ∧ o 3 = Orient.tE) ∨
          (o 0 = Orient.wE ∧ o 1 = Orient.tE ∧ o 2 = Orient.wA ∧ o 3 = Orient.tB))) :=
  n52_alt_marks_aux (o 0) (o 1) (o 2) (o 3) S.fullEA S.fullEB S.alpha_lt S.beta_lt h0 h1 h2 h3
    (S.mark F.toFrame5 (by decide)) (S.mark F.toFrame5 (by decide))
    (S.mark F.toFrame5 (by decide)) (S.mark F.toFrame5 (by decide))
    F.side_bottom F.side_top F.side_left F.side_right

/-- `T_5` has a full vertical side, as a local column of its box: `EB` if it is
wide, `EA` if it is tall. -/
private theorem bt_back_vfull (F : Frame5 P p q a b t o x5 y5) (S : ThreeFull P p q)
    (c : Orient) {y : ℤ} (h0 : 0 ≤ y) (h1 : y < c.H p q) :
    c.back p q (if c.revH then c.W p q - 1 else 0, y) ∈ P := by
  have hEA := (F.rowCount_eq_iff 0).1 S.fullEA
  have hEB := (F.colCount_eq_iff 0).1 S.fullEB
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;>
    simp [Orient.back, Orient.revH, Orient.W, Orient.H] at h1 ⊢ <;>
    first
    | (apply hEB <;> omega)
    | (apply hEA <;> omega)

/-- A box has at least one column and one row. -/
private theorem bt_W_pos (F : Frame5 P p q a b t o x5 y5) (c : Orient) :
    1 ≤ c.W p q ∧ 1 ≤ c.H p q := by
  have := F.two_le_p
  have := F.two_le_q
  unfold Orient.W Orient.H
  constructor <;> split <;> omega

/-- `report-A2.md`, 5.2, `p > q`: "T_5 has a full vertical side, in a column
x". -/
private theorem bt_vfull (F : Frame5 P p q a b t o x5 y5) (S : ThreeFull P p q) :
    ∃ x : ℤ, x5 ≤ x ∧ x < x5 + (o 4).W p q ∧
      ∀ y : ℤ, y5 ≤ y → y < y5 + (o 4).H p q → ((x, y) : Cell) ∈ t 4 := by
  have hW := (bt_W_pos F (o 4)).1
  refine ⟨x5 + (if (o 4).revH then (o 4).W p q - 1 else 0), ?_, ?_, fun y h0 h1 => ?_⟩
  · split <;> omega
  · split <;> omega
  · rw [F.mem4, add_sub_cancel_left]
    exact bt_back_vfull F S (o 4) (by omega) (by omega)

/-- The dimensions for the marks `(B, E, E, A)`: `a = beta + q = p + alpha`,
`b = p + q` (by (1)). -/
private theorem bt_BEEA_dims (F : FrameN P p q a b t o x5 y5) (S : ThreeFull P p q)
    (e0 : o 0 = Orient.wB) (e1 : o 1 = Orient.tE) (e2 : o 2 = Orient.wE)
    (e3 : o 3 = Orient.tA) :
    a = rowCount P (q - 1) + q ∧ a = p + colCount P (p - 1) ∧ b = p + q := by
  have hb := F.side_bottom
  have ht := F.side_top
  have hl := F.side_left
  rw [e0, e1] at hb
  rw [e2, e3] at ht
  rw [e0, e3] at hl
  simp [Orient.hrun_eq, Orient.vrun_eq, Orient.wB, Orient.tE, Orient.wE, Orient.tA, S.fullEA,
    S.fullEB] at hb ht hl
  omega

/-- `report-A2.md`, 5.2, marks `(B, E, E, A)`: `T_5` is wide, and `box(T_5)` lies
in the rows `≥ q` or in the rows `< p`. `T_5` has a full vertical side in a
column `x`; if the rows of `box(T_5)` contained `q - 1` and `p`, then `x ≥ p` by
`T_1` (its row `q - 1` is full) and `x < q` by `T_3` (which holds
`[q, a) x {p}`); a tall `T_5` would need `p` rows among `p - 1`.
PROVISIONAL (a leaf of `n52_BEEA`). -/
theorem n52_BEEA_wide (F : FrameN P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (e0 : o 0 = Orient.wB) (e1 : o 1 = Orient.tE) (e2 : o 2 = Orient.wE) (e3 : o 3 = Orient.tA)
    (hd : p - rowCount P (q - 1) = q - colCount P (p - 1)) :
    (o 4).swap = false ∧ (q ≤ y5 ∨ y5 + q ≤ p) := by
  have F5 := F.toFrame5
  obtain ⟨ha, -, hb⟩ := bt_BEEA_dims F S e0 e1 e2 e3
  have hEA := (F5.rowCount_eq_iff 0).1 S.fullEA
  -- the run of `B` along `BD`: the first `beta` cells of the row `q - 1` of `P`
  have hB : ∀ z : ℤ, 0 ≤ z → z < rowCount P (q - 1) → ((z, q - 1) : Cell) ∈ P := by
    intro z h0 h1
    have h := (F5.hside (i := 0) (by decide) z).2
      ⟨h0, by simpa [e0, Orient.wB, Orient.rowLine] using h1⟩
    simpa [e0, Orient.wB, Orient.back] using h
  obtain ⟨x, hx1, hx2, hx⟩ := bt_vfull F5 S
  have hx5 := F.x5_pos
  have hx5' := F.x5_le
  have hy5 := F.y5_pos
  have hy5' := F.y5_le
  -- the rows of `box(T_5)` do not contain both `q - 1` and `p`
  have hrows : q ≤ y5 ∨ y5 + (o 4).H p q ≤ p := by
    by_contra hcon
    rw [not_or, not_le, not_le] at hcon
    obtain ⟨c1, c2⟩ := hcon
    rcases lt_or_ge x p with hxp | hxp
    · -- `x < p`: the cell `(x, q - 1)` of the full row `q - 1` of `T_1`
      have h4 := hx (q - 1) (by omega) (by omega)
      have h0 : ((x, q - 1) : Cell) ∈ t 0 := by
        refine (F5.mem_of 0 (d := (x, 0)) ?_).2 (hEA x (by omega) hxp)
        simp [loc, e0, Orient.wB, Orient.back]
      exact Finset.disjoint_left.1 (F.tiling.disjoint 0 4 (by decide)) h0 h4
    · -- `x ≥ p`: the cell `(x, p)` of the run of `B` of `T_3`
      have h4 := hx p (by omega) (by omega)
      have h2 : ((x, p) : Cell) ∈ t 2 := by
        refine (F5.mem_of 2 (d := (a - 1 - x, q - 1)) ?_).2 (hB _ (by omega) (by omega))
        simp [loc, e2, Orient.wE, Orient.back]
        omega
      exact Finset.disjoint_left.1 (F.tiling.disjoint 2 4 (by decide)) h2 h4
  cases h4 : (o 4).swap
  · refine ⟨rfl, ?_⟩
    simpa [Orient.H, h4] using hrows
  · exfalso
    simp [Orient.H, h4] at hrows hy5'
    omega

/-- `report-A2.md`, 5.2, marks `(B, E, E, A)`: `kappa_c = q` for `c < beta`. If
`T_5` is in the rows `≥ q`, the rows `[0, q)` lie in `T_1` and `T_2` alone, so
`[0, beta) x [0, q)` is in `T_1`; if `T_5` is in the rows `< p`, the rows
`[p, b)` lie in `T_3` and `T_4` alone, so `[q, a) x [p, b)` is in `T_3`.
PROVISIONAL (a leaf of `n52_BEEA`). -/
theorem n52_BEEA_cols (F : FrameN P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (e0 : o 0 = Orient.wB) (e1 : o 1 = Orient.tE) (e2 : o 2 = Orient.wE) (e3 : o 3 = Orient.tA)
    (hd : p - rowCount P (q - 1) = q - colCount P (p - 1)) :
    ∀ c : ℤ, 0 ≤ c → c < rowCount P (q - 1) → colCount P c = q := by
  have F5 := F.toFrame5
  obtain ⟨ha, -, hb⟩ := bt_BEEA_dims F S e0 e1 e2 e3
  obtain ⟨h4, hrows⟩ := n52_BEEA_wide F S hq e0 e1 e2 e3 hd
  have H4 : (o 4).H p q = q := by simp [Orient.H, h4]
  have W0 : (o 0).W p q = p := by rw [e0]; rfl
  have H0 : (o 0).H p q = q := by rw [e0]; rfl
  have W1 : (o 1).W p q = q := by rw [e1]; rfl
  have H1 : (o 1).H p q = p := by rw [e1]; rfl
  have H2 : (o 2).H p q = q := by rw [e2]; rfl
  have W3 : (o 3).W p q = q := by rw [e3]; rfl
  have H3 : (o 3).H p q = p := by rw [e3]; rfl
  have hy5 := F.y5_pos
  intro c hc0 hc1
  rw [F5.colCount_eq_iff]
  intro y hy0 hy1
  rcases hrows with hr | hr
  · -- `T_5` in the rows `≥ q`: the rows `[0, q)` lie in `T_1` and `T_2`, and the
    -- cell `(c, q - 1 - y)` is not in `box(T_2)`
    have hR : ((c, q - 1 - y) : Cell) ∈ R a b := by
      rw [mem_R]
      constructor <;> constructor <;> dsimp only <;> omega
    rcases F5.cover_cases hR with h | h | h | h | h
    · refine (F5.mem_of 0 (d := (c, y)) ?_).1 h.1
      simp [loc, e0, Orient.wB, Orient.back]
    · obtain ⟨-, h1, -⟩ := h
      dsimp only at h1
      omega
    · obtain ⟨-, -, h2⟩ := h
      dsimp only at h2
      omega
    · obtain ⟨-, -, h3⟩ := h
      dsimp only at h3
      omega
    · obtain ⟨-, -, h5, -⟩ := h
      dsimp only at h5
      omega
  · -- `T_5` in the rows `< p`: the rows `[p, b)` lie in `T_3` and `T_4`, and the
    -- cell `(a - 1 - c, b - 1 - y)` is not in `box(T_4)`
    have hR : ((a - 1 - c, b - 1 - y) : Cell) ∈ R a b := by
      rw [mem_R]
      constructor <;> constructor <;> dsimp only <;> omega
    rcases F5.cover_cases hR with h | h | h | h | h
    · obtain ⟨-, -, h1⟩ := h
      dsimp only at h1
      omega
    · obtain ⟨-, -, h1⟩ := h
      dsimp only at h1
      omega
    · refine (F5.mem_of 2 (d := (c, y)) ?_).1 h.1
      simp [loc, e2, Orient.wE, Orient.back]
    · obtain ⟨-, h1, -⟩ := h
      dsimp only at h1
      omega
    · obtain ⟨-, -, -, h5⟩ := h
      dsimp only at h5
      omega

/-- `T_5` has a full horizontal side, as a local row of its box. -/
private theorem bt_back_hfull (F : Frame5 P p q a b t o x5 y5) (S : ThreeFull P p q)
    (c : Orient) {x : ℤ} (h0 : 0 ≤ x) (h1 : x < c.W p q) :
    c.back p q (x, if c.revV then c.H p q - 1 else 0) ∈ P := by
  have hEA := (F.rowCount_eq_iff 0).1 S.fullEA
  have hEB := (F.colCount_eq_iff 0).1 S.fullEB
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;>
    simp [Orient.back, Orient.revV, Orient.W, Orient.H] at h1 ⊢ <;>
    first
    | (apply hEB <;> omega)
    | (apply hEA <;> omega)

/-- `T_5` has a full horizontal side, in a row `y`. -/
private theorem bt_hfull (F : Frame5 P p q a b t o x5 y5) (S : ThreeFull P p q) :
    ∃ y : ℤ, y5 ≤ y ∧ y < y5 + (o 4).H p q ∧
      ∀ x : ℤ, x5 ≤ x → x < x5 + (o 4).W p q → ((x, y) : Cell) ∈ t 4 := by
  have hH := (bt_W_pos F (o 4)).2
  refine ⟨y5 + (if (o 4).revV then (o 4).H p q - 1 else 0), ?_, ?_, fun x h0 h1 => ?_⟩
  · split <;> omega
  · split <;> omega
  · rw [F.mem4, add_sub_cancel_left]
    exact bt_back_hfull F S (o 4) (by omega) (by omega)

/-- `report-A2.md`, 5.2, marks `(B, E, E, A)`: contradiction. With `d = d_A =
d_B`: `a = p + q - d`, `b = p + q`, `beta = p - d`, `alpha = q - d`. By
`n52_BEEA_cols`, `T_1` contains `[0, beta) x [0, q)`, `T_4` contains
`[0, q) x [q, q + beta)`, `T_3` contains `[q, a) x [p, b)`. The full long side
of `T_5` (wide by `n52_BEEA_wide`) is in a row `y` and the columns
`[x5, x5 + p)` with `x5 < beta`, `x5 < q`, `x5 + p - 1 ≥ p`: for `y < q` the cell
`(x5, y)` is in `T_1`, for `q ≤ y < q + beta` in `T_4`, for `y ≥ p` the cell
`(x5 + p - 1, y)` is in `T_3`; and `q + beta > p`. -/
theorem n52_BEEA (F : FrameN P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (e0 : o 0 = Orient.wB) (e1 : o 1 = Orient.tE) (e2 : o 2 = Orient.wE) (e3 : o 3 = Orient.tA)
    (hd : p - rowCount P (q - 1) = q - colCount P (p - 1)) : False := by
  have F5 := F.toFrame5
  obtain ⟨ha, ha', hb⟩ := bt_BEEA_dims F S e0 e1 e2 e3
  obtain ⟨h4, -⟩ := n52_BEEA_wide F S hq e0 e1 e2 e3 hd
  have hk := n52_BEEA_cols F S hq e0 e1 e2 e3 hd
  have hα := S.alpha_pos
  have hα' := S.alpha_lt
  have hx5 := F.x5_pos
  have hx5' := F.x5_le
  have hy5 := F.y5_pos
  have hy5' := F.y5_le
  have W4 : (o 4).W p q = p := by simp [Orient.W, h4]
  have H4 : (o 4).H p q = q := by simp [Orient.H, h4]
  -- the columns `c < beta` of `P` are full
  have hcol : ∀ c z : ℤ, 0 ≤ c → c < rowCount P (q - 1) → 0 ≤ z → z < q →
      ((c, z) : Cell) ∈ P :=
    fun c z h0 h1 h2 h3 => (F5.colCount_eq_iff c).1 (hk c h0 h1) z h2 h3
  -- the full long side of `T_5`: the row `y`, the columns `[x5, x5 + p)`
  obtain ⟨y, hy1, hy2, hy⟩ := bt_hfull F5 S
  rcases lt_or_ge y q with hyq | hyq
  · -- `y < q`: `(x5, y)` is in `T_1`, which contains `[0, beta) x [0, q)`
    have h0 : ((x5, y) : Cell) ∈ t 0 := by
      refine (F5.mem_of 0 (d := (x5, q - 1 - y)) ?_).2
        (hcol _ _ (by omega) (by omega) (by omega) (by omega))
      simp [loc, e0, Orient.wB, Orient.back]
    exact Finset.disjoint_left.1 (F.tiling.disjoint 0 4 (by decide)) h0
      (hy x5 le_rfl (by omega))
  rcases lt_or_ge y (q + rowCount P (q - 1)) with hyb | hyb
  · -- `q ≤ y < q + beta`: `(x5, y)` is in `T_4`, which contains `[0, q) x [q, q + beta)`
    have h3 : ((x5, y) : Cell) ∈ t 3 := by
      refine (F5.mem_of 3 (d := (y - q, x5)) ?_).2
        (hcol _ _ (by omega) (by omega) (by omega) (by omega))
      simp [loc, e3, Orient.tA, Orient.back]
      omega
    exact Finset.disjoint_left.1 (F.tiling.disjoint 3 4 (by decide)) h3
      (hy x5 le_rfl (by omega))
  · -- `y ≥ q + beta > p`: `(x5 + p - 1, y)` is in `T_3`, which contains `[q, a) x [p, b)`
    have h2 : ((x5 + p - 1, y) : Cell) ∈ t 2 := by
      refine (F5.mem_of 2 (d := (a - 1 - (x5 + p - 1), b - 1 - y)) ?_).2
        (hcol _ _ (by omega) (by omega) (by omega) (by omega))
      simp [loc, e2, Orient.wE, Orient.back]
    exact Finset.disjoint_left.1 (F.tiling.disjoint 2 4 (by decide)) h2
      (hy _ (by omega) (by omega))

/-- `report-A2.md`, 5.2, `p > q`, the alternating case with `T_1`, `T_3` wide:
period two is against (T4) (half turn), and "a quarter turn of R ... moves the
four solutions around in a circle". -/
theorem n52_alt (F : FrameN P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (h0 : (o 0).swap = false) (h1 : (o 1).swap = true) (h2 : (o 2).swap = false)
    (h3 : (o 3).swap = true) : False := by
  rcases n52_alt_marks F S h0 h1 h2 h3 with ⟨e02, e13⟩ | ⟨hd, hsol⟩
  · obtain ⟨-, -, hT⟩ := F.toFrame5.T4_halfTurn e02 e13
    exact S.no_halfTurn hT
  · rcases hsol with ⟨e0, e1, e2, e3⟩ | ⟨e0, e1, e2, e3⟩ | ⟨e0, e1, e2, e3⟩ | ⟨e0, e1, e2, e3⟩
    · exact n52_BEEA F S hq e0 e1 e2 e3 hd
    · obtain ⟨t', F'⟩ := F.transpose
      obtain ⟨t'', F''⟩ := F'.flipY
      exact n52_BEEA F'' S hq (by show (o 1).tr = _; rw [e1]; rfl)
        (by show (o 2).tr = _; rw [e2]; rfl) (by show (o 3).tr = _; rw [e3]; rfl)
        (by show (o 0).tr = _; rw [e0]; rfl) hd
    · obtain ⟨t', F'⟩ := F.halfTurn
      exact n52_BEEA F' S hq e2 e3 e0 e1 hd
    · obtain ⟨t', F'⟩ := F.transpose
      obtain ⟨t'', F''⟩ := F'.flipX
      exact n52_BEEA F'' S hq (by show (o 3).tr = _; rw [e3]; rfl)
        (by show (o 0).tr = _; rw [e0]; rfl) (by show (o 1).tr = _; rw [e1]; rfl)
        (by show (o 2).tr = _; rw [e2]; rfl) hd

/-- **`report-A2.md`, 5.2.** Pattern N with three occupied corners does not
occur. -/
theorem three_N (F : FrameN P p q a b t o x5 y5) (S : Three P p q) (hpq : q ≤ p) : False := by
  have S' := S.full_N F
  rcases eq_or_lt_of_le hpq with h | hq
  · exact n52_sq F S' h.symm
  · rcases n52_types F S' hq with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩
    · exact n52_alt F S' hq h0 h1 h2 h3
    · obtain ⟨t', F'⟩ := F.flipX
      exact n52_alt F' S' hq (by simpa using h1) (by simpa using h0) (by simpa using h3)
        (by simpa using h2)

end PolyominoOddOrder
