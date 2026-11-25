module

public import PolyominoOddOrder.Frame5Tools

/-!
# Case (I): lemmas shared by the case files (`Frame5Lemmas.lean`)

Blueprint: no unit (third increment); every statement here is proved from the
statements of `Frame5.lean`, `Frame5Sides.lean`, `Frame5Tools.lean`. The file
belongs to the architect of the increment; a case unit that needs one more
shared lemma states it in its own file.

* the corners of `box(P)` under the three symmetries of `P`
  (`cornerP_mem_flipPX`, `cornerP_mem_flipPY`, `cornerP_mem_transposeP`) and the
  normal forms `Four`, `Three`, `Adjacent`, `Opposite` under them;
* marks: `Frame5.mark_mem`, the far ends of the two sides at a mark
  (`Frame5.far_h`, `Frame5.far_v`), `SameMarks.eq_of_swap`;
* `Frame5.normalize`: after renaming the corners of `box(P)` the set `S` of the
  occupied corners is in one of the normal forms of `report-A2.md`, sections 3
  to 7.

Source: `theoretician/report-A2.md` (goals lab, commit `076d663`), sections 1.2
and 3 ("Consequences").
-/

@[expose] public section

namespace PolyominoOddOrder

open Orient (cornerP)

variable {P : Finset Cell} {p q a b : ℤ} {t : Fin 5 → Finset Cell} {o : Fin 5 → Orient}
  {x5 y5 : ℤ}

/-! ## Corners of `box(P)` and the symmetries of `P` -/

/-- The reflection of `box(P)` in its vertical midline exchanges the corners in
each row. -/
theorem cornerP_mem_flipPX {X Y : Bool} :
    cornerP p q X Y ∈ P.image (GridIso.flipX p).apply ↔ cornerP p q (!X) Y ∈ P := by
  rw [CaseI.mem_image_flipX]
  cases X <;> cases Y <;> simp [cornerP]

/-- The reflection of `box(P)` in its horizontal midline exchanges the corners in
each column. -/
theorem cornerP_mem_flipPY {X Y : Bool} :
    cornerP p q X Y ∈ P.image (GridIso.flipY q).apply ↔ cornerP p q X (!Y) ∈ P := by
  rw [CaseI.mem_image_flipY]
  cases X <;> cases Y <;> simp [cornerP]

/-- The exchange of the axes exchanges the two switches of a corner. -/
theorem cornerP_mem_transposeP {X Y : Bool} :
    cornerP q p X Y ∈ P.image GridIso.transpose.apply ↔ cornerP p q Y X ∈ P := by
  rw [CaseI.mem_image_transpose]
  cases X <;> cases Y <;> simp [cornerP]

theorem cornerP_ff : cornerP p q false false = (0, 0) := by simp [cornerP]
theorem cornerP_tf : cornerP p q true false = (p - 1, 0) := by simp [cornerP]
theorem cornerP_ft : cornerP p q false true = (0, q - 1) := by simp [cornerP]
theorem cornerP_tt : cornerP p q true true = (p - 1, q - 1) := by simp [cornerP]

/-- With all four corners occupied, every corner is in `P`. -/
theorem Four.corner_mem (S : Four P p q) (X Y : Bool) : cornerP p q X Y ∈ P := by
  cases X <;> cases Y
  · simpa [Orient.cornerP] using S.c00
  · simpa [Orient.cornerP] using S.c01
  · simpa [Orient.cornerP] using S.c10
  · simpa [Orient.cornerP] using S.c11

/-- `Four` from the four corners. -/
theorem Four.of_corners (h : ∀ X Y : Bool, cornerP p q X Y ∈ P) : Four P p q :=
  ⟨by simpa [cornerP] using h false false, by simpa [cornerP] using h true false,
    by simpa [cornerP] using h false true, by simpa [cornerP] using h true true⟩

/-- `|S| = 4` does not depend on the names of the corners: reflection of
`box(P)` in its vertical midline. -/
theorem Four.of_flipPX (S : Four (P.image (GridIso.flipX p).apply) p q) : Four P p q :=
  Four.of_corners fun X Y => by
    have h := S.corner_mem (!X) Y
    rwa [cornerP_mem_flipPX, Bool.not_not] at h

/-- `|S| = 4` does not depend on the names of the corners: reflection of
`box(P)` in its horizontal midline. -/
theorem Four.of_flipPY (S : Four (P.image (GridIso.flipY q).apply) p q) : Four P p q :=
  Four.of_corners fun X Y => by
    have h := S.corner_mem X (!Y)
    rwa [cornerP_mem_flipPY, Bool.not_not] at h

/-- `|S| = 4` does not depend on the names of the corners: exchange of the
axes. -/
theorem Four.of_transposeP (S : Four (P.image GridIso.transpose.apply) q p) : Four P p q :=
  Four.of_corners fun X Y => by
    have h := S.corner_mem Y X
    rwa [cornerP_mem_transposeP] at h

/-- `|S| = 4` for the mirror image in the vertical midline. -/
theorem Four.flipPX (S : Four P p q) : Four (P.image (GridIso.flipX p).apply) p q :=
  Four.of_corners fun _ _ => cornerP_mem_flipPX.2 (S.corner_mem _ _)

/-- `|S| = 4` for the mirror image in the horizontal midline. -/
theorem Four.flipPY (S : Four P p q) : Four (P.image (GridIso.flipY q).apply) p q :=
  Four.of_corners fun _ _ => cornerP_mem_flipPY.2 (S.corner_mem _ _)

/-- `|S| = 4` for the transposed polyomino. -/
theorem Four.transposeP (S : Four P p q) : Four (P.image GridIso.transpose.apply) q p :=
  Four.of_corners fun _ _ => cornerP_mem_transposeP.2 (S.corner_mem _ _)

/-- Three occupied corners, after the exchange of the axes: `A` and `B` change
names. -/
theorem Three.transposeP (S : Three P p q) : Three (P.image GridIso.transpose.apply) q p := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← cornerP_ff (p := q) (q := p), cornerP_mem_transposeP, cornerP_ff]; exact S.hE
  · rw [← cornerP_tf (p := q) (q := p), cornerP_mem_transposeP, cornerP_ft]; exact S.hB
  · rw [← cornerP_ft (p := q) (q := p), cornerP_mem_transposeP, cornerP_tf]; exact S.hA
  · rw [← cornerP_tt (p := q) (q := p), cornerP_mem_transposeP, cornerP_tt]; exact S.hD

/-- Two opposite occupied corners, after the exchange of the axes. -/
theorem Opposite.transposeP (S : Opposite P p q) :
    Opposite (P.image GridIso.transpose.apply) q p := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← cornerP_ff (p := q) (q := p), cornerP_mem_transposeP, cornerP_ff]; exact S.hA
  · rw [← cornerP_tt (p := q) (q := p), cornerP_mem_transposeP, cornerP_tt]; exact S.hC
  · rw [← cornerP_tf (p := q) (q := p), cornerP_mem_transposeP, cornerP_ft]; exact S.h01
  · rw [← cornerP_ft (p := q) (q := p), cornerP_mem_transposeP, cornerP_tf]; exact S.h10

/-- The reflection of `box(P)` in its vertical midline, on corners. -/
theorem cornerP_reflect_x (p q : ℤ) (X Y : Bool) :
    (p - 1 - (cornerP p q X Y).1, (cornerP p q X Y).2) = cornerP p q (!X) Y := by
  cases X <;> cases Y <;> simp [cornerP]

/-- The reflection of `box(P)` in its horizontal midline, on corners. -/
theorem cornerP_reflect_y (p q : ℤ) (X Y : Bool) :
    ((cornerP p q X Y).1, q - 1 - (cornerP p q X Y).2) = cornerP p q X (!Y) := by
  cases X <;> cases Y <;> simp [cornerP]

/-- (T4), last sentences: if `P` is invariant under both reflections of its box
and one corner is occupied, all four are. -/
theorem Four.of_reflections {X Y : Bool} (h : cornerP p q X Y ∈ P)
    (hX : ∀ c : Cell, c ∈ P ↔ (p - 1 - c.1, c.2) ∈ P)
    (hY : ∀ c : Cell, c ∈ P ↔ (c.1, q - 1 - c.2) ∈ P) : Four P p q := by
  have hx : ∀ X Y, cornerP p q X Y ∈ P → cornerP p q (!X) Y ∈ P := fun X Y h => by
    rw [← cornerP_reflect_x]; exact (hX _).1 h
  have hy : ∀ X Y, cornerP p q X Y ∈ P → cornerP p q X (!Y) ∈ P := fun X Y h => by
    rw [← cornerP_reflect_y]; exact (hY _).1 h
  refine Four.of_corners fun X' Y' => ?_
  cases X <;> cases Y <;> cases X' <;> cases Y' <;>
    first
    | exact h
    | exact hx _ _ h
    | exact hy _ _ h
    | exact hx _ _ (hy _ _ h)

/-- (T4), last sentence: if `p = q`, `P` is invariant under the quarter turn of
its box and one corner is occupied, all four are. -/
theorem Four.of_quarter {X Y : Bool} (hpq : p = q) (h : cornerP p q X Y ∈ P)
    (hQ : ∀ c : Cell, c ∈ P ↔ (q - 1 - c.2, c.1) ∈ P) : Four P p q := by
  subst hpq
  have hq : ∀ X Y, cornerP p p X Y ∈ P → cornerP p p (!Y) X ∈ P := fun X Y h => by
    have h' := (hQ _).1 h
    have e : (p - 1 - (cornerP p p X Y).2, (cornerP p p X Y).1) = cornerP p p (!Y) X := by
      cases X <;> cases Y <;> simp [cornerP]
    rwa [e] at h'
  refine Four.of_corners fun X' Y' => ?_
  cases X <;> cases Y <;> cases X' <;> cases Y' <;>
    first
    | exact h
    | exact hq _ _ h
    | exact hq _ _ (hq _ _ h)
    | exact hq _ _ (hq _ _ (hq _ _ h))

/-! ## Marks -/

/-- Two codes with the same mark: the run along the local horizontal side is the
same run of `P` if the same direction of `box(P)` is horizontal, and the other
run of the mark if not. -/
theorem Orient.rowLine_zero_of_marks {c d : Orient} (hx : c.negX = d.negX)
    (hy : c.negY = d.negY) (p q : ℤ) (P : Finset Cell) :
    c.rowLine p q P 0 = if c.swap = d.swap then d.rowLine p q P 0 else d.colLine p q P 0 := by
  rcases c with ⟨cs, cx, cy⟩
  rcases d with ⟨ds, dx, dy⟩
  simp only at hx hy
  subst hx hy
  cases cs <;> cases ds <;> simp [Orient.rowLine, Orient.colLine]

/-- Two codes with the same mark: the run along the local vertical side. -/
theorem Orient.colLine_zero_of_marks {c d : Orient} (hx : c.negX = d.negX)
    (hy : c.negY = d.negY) (p q : ℤ) (P : Finset Cell) :
    c.colLine p q P 0 = if c.swap = d.swap then d.colLine p q P 0 else d.rowLine p q P 0 := by
  rcases c with ⟨cs, cx, cy⟩
  rcases d with ⟨ds, dx, dy⟩
  simp only at hx hy
  subst hx hy
  cases cs <;> cases ds <;> simp [Orient.rowLine, Orient.colLine]

/-- `W + H = p + q` for every code. -/
theorem Orient.W_add_H (c : Orient) (p q : ℤ) : c.W p q + c.H p q = p + q := by
  rcases c with ⟨_ | _, _, _⟩ <;> simp [Orient.W, Orient.H]
  omega

/-- For `p ≠ q` two boxes have the same width exactly when the same direction of
`box(P)` is horizontal in both. -/
theorem Orient.W_eq_iff (hpq : q ≠ p) (c d : Orient) : c.W p q = d.W p q ↔ c.swap = d.swap := by
  rcases c with ⟨_ | _, _, _⟩ <;> rcases d with ⟨_ | _, _, _⟩ <;> simp [Orient.W] <;> omega

/-- The run along the local horizontal side as a side count of `P`: the row or
the column of `box(P)` at the mark. -/
theorem Orient.hrun_eq (c : Orient) (p q : ℤ) (P : Finset Cell) :
    c.rowLine p q P 0 = if c.swap then colCount P (if c.negX then p - 1 else 0)
      else rowCount P (if c.negY then q - 1 else 0) := by
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;> simp [Orient.rowLine]

/-- The run along the local vertical side as a side count of `P`. -/
theorem Orient.vrun_eq (c : Orient) (p q : ℤ) (P : Finset Cell) :
    c.colLine p q P 0 = if c.swap then rowCount P (if c.negY then q - 1 else 0)
      else colCount P (if c.negX then p - 1 else 0) := by
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;> simp [Orient.colLine]

/-! ### Line counts of a tile with a known code

After `rw` with the code of a tile, `simp only [Orient.colLine_wide, ...]` turns
a line count of the tile into a line count of `P` without touching the
argument. -/

theorem Orient.colLine_wide (ny : Bool) (p q : ℤ) (P : Finset Cell) (x : ℤ) :
    (⟨false, false, ny⟩ : Orient).colLine p q P x = colCount P x := rfl

theorem Orient.colLine_wide_neg (ny : Bool) (p q : ℤ) (P : Finset Cell) (x : ℤ) :
    (⟨false, true, ny⟩ : Orient).colLine p q P x = colCount P (p - 1 - x) := rfl

theorem Orient.colLine_tall (nx : Bool) (p q : ℤ) (P : Finset Cell) (x : ℤ) :
    (⟨true, nx, false⟩ : Orient).colLine p q P x = rowCount P x := rfl

theorem Orient.colLine_tall_neg (nx : Bool) (p q : ℤ) (P : Finset Cell) (x : ℤ) :
    (⟨true, nx, true⟩ : Orient).colLine p q P x = rowCount P (q - 1 - x) := rfl

theorem Orient.rowLine_wide (nx : Bool) (p q : ℤ) (P : Finset Cell) (y : ℤ) :
    (⟨false, nx, false⟩ : Orient).rowLine p q P y = rowCount P y := rfl

theorem Orient.rowLine_wide_neg (nx : Bool) (p q : ℤ) (P : Finset Cell) (y : ℤ) :
    (⟨false, nx, true⟩ : Orient).rowLine p q P y = rowCount P (q - 1 - y) := rfl

theorem Orient.rowLine_tall (ny : Bool) (p q : ℤ) (P : Finset Cell) (y : ℤ) :
    (⟨true, false, ny⟩ : Orient).rowLine p q P y = colCount P y := rfl

theorem Orient.rowLine_tall_neg (ny : Bool) (p q : ℤ) (P : Finset Cell) (y : ℤ) :
    (⟨true, true, ny⟩ : Orient).rowLine p q P y = colCount P (p - 1 - y) := rfl

/-- Reversing the local vertical direction, read off the code. -/
@[simp] theorem Orient.revV_reflY (c : Orient) : c.reflY.revV = !c.revV := by
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;> rfl

@[simp] theorem Orient.revH_reflY (c : Orient) : c.reflY.revH = c.revH := by
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;> rfl

@[simp] theorem Orient.revH_reflX (c : Orient) : c.reflX.revH = !c.revH := by
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;> rfl

@[simp] theorem Orient.revV_reflX (c : Orient) : c.reflX.revV = c.revV := by
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;> rfl

@[simp] theorem Orient.revV_tr (c : Orient) : c.tr.revV = c.revH := by
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;> rfl

@[simp] theorem Orient.revH_tr (c : Orient) : c.tr.revH = c.revV := by
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;> rfl

/-- Two switches that both differ from a third are equal. -/
theorem bool_eq_of_ne {x y z : Bool} (h : ¬ x = z) (h' : ¬ y = z) : x = y := by
  cases x <;> cases y <;> cases z <;> simp_all

/-- A statement about the marks of the four corner tiles holds for the codes
after a symmetry of the rectangle, which permutes them. -/
theorem marks_perm {X Y : Bool}
    (hm : ∀ i : Fin 5, i ≠ 4 → (o i).negX = X ∧ (o i).negY = Y) (i0 i1 i2 i3 : Fin 5)
    (h0 : i0 ≠ 4) (h1 : i1 ≠ 4) (h2 : i2 ≠ 4) (h3 : i3 ≠ 4) (c : Orient) :
    ∀ i : Fin 5, i ≠ 4 → (![o i0, o i1, o i2, o i3, c] i).negX = X ∧
      (![o i0, o i1, o i2, o i3, c] i).negY = Y := by
  intro i hi
  fin_cases i
  · simpa using hm i0 h0
  · simpa using hm i1 h1
  · simpa using hm i2 h2
  · simpa using hm i3 h3
  · exact absurd rfl hi

/-- The same after the exchange of the axes. -/
theorem marks_perm_tr {X Y : Bool}
    (hm : ∀ i : Fin 5, i ≠ 4 → (o i).negX = X ∧ (o i).negY = Y) (c : Orient) :
    ∀ i : Fin 5, i ≠ 4 → (![(o 0).tr, (o 3).tr, (o 2).tr, (o 1).tr, c] i).negX = X ∧
      (![(o 0).tr, (o 3).tr, (o 2).tr, (o 1).tr, c] i).negY = Y := by
  intro i hi
  fin_cases i
  · simpa using hm 0 (by decide)
  · simpa using hm 3 (by decide)
  · simpa using hm 2 (by decide)
  · simpa using hm 1 (by decide)
  · exact absurd rfl hi

namespace Frame5

/-- Membership in a tile through an explicit cell of `box(P)`: the form used in
the cell arguments. The side goal `h` is closed by
`simp [loc, <code>, Orient.back, ...] <;> omega`. -/
theorem mem_of (F : Frame5 P p q a b t o x5 y5) (i : Fin 5) {c d : Cell}
    (h : (o i).back p q (loc a b x5 y5 i c) = d) : c ∈ t i ↔ d ∈ P := by
  rw [F.mem, h]

/-- The mark of a corner tile is an occupied corner of `box(P)`: `m_i ∈ S`
(`report-A2.md`, section 1.2). -/
theorem mark_mem (F : Frame5 P p q a b t o x5 y5) {i : Fin 5} (hi : i ≠ 4) :
    cornerP p q (o i).negX (o i).negY ∈ P := by
  rw [← Orient.back_zero]
  exact F.corner i hi

/-- (Full), read backwards, horizontal: if the horizontal run of a corner tile
is its whole side, the corner of `box(P)` at the far end is occupied. -/
theorem far_h (F : Frame5 P p q a b t o x5 y5) {i : Fin 5} (hi : i ≠ 4)
    (h : (o i).rowLine p q P 0 = (o i).W p q) :
    cornerP p q (if (o i).swap then (o i).negX else !(o i).negX)
      (if (o i).swap then !(o i).negY else (o i).negY) ∈ P := by
  rw [← Orient.back_W]
  exact (F.hrun_eq_iff hi).1 h

/-- (Full), read backwards, vertical. -/
theorem far_v (F : Frame5 P p q a b t o x5 y5) {i : Fin 5} (hi : i ≠ 4)
    (h : (o i).colLine p q P 0 = (o i).H p q) :
    cornerP p q (if (o i).swap then !(o i).negX else (o i).negX)
      (if (o i).swap then (o i).negY else !(o i).negY) ∈ P := by
  rw [← Orient.back_H]
  exact (F.vrun_eq_iff hi).1 h

/-- (Full), horizontal: the run is the whole side when the far corner is
occupied. -/
theorem hrun_of_far (F : Frame5 P p q a b t o x5 y5) {i : Fin 5} (hi : i ≠ 4)
    (h : cornerP p q (if (o i).swap then (o i).negX else !(o i).negX)
      (if (o i).swap then !(o i).negY else (o i).negY) ∈ P) :
    (o i).rowLine p q P 0 = (o i).W p q := by
  rw [← Orient.back_W] at h
  exact (F.hrun_eq_iff hi).2 h

/-- (Full), vertical: the run is the whole side when the far corner is
occupied. -/
theorem vrun_of_far (F : Frame5 P p q a b t o x5 y5) {i : Fin 5} (hi : i ≠ 4)
    (h : cornerP p q (if (o i).swap then !(o i).negX else (o i).negX)
      (if (o i).swap then (o i).negY else !(o i).negY) ∈ P) :
    (o i).colLine p q P 0 = (o i).H p q := by
  rw [← Orient.back_H] at h
  exact (F.vrun_eq_iff hi).2 h

end Frame5

/-- Two corner tiles with the same mark and the same direction of `box(P)` along
a side have the same code. -/
theorem SameMarks.eq_of_swap (hm : SameMarks o) {i j : Fin 5} (hi : i ≠ 4) (hj : j ≠ 4)
    (h : (o i).swap = (o j).swap) : o i = o j := by
  obtain ⟨hix, hiy⟩ := hm i hi
  obtain ⟨hjx, hjy⟩ := hm j hj
  exact Orient.ext h (hix.trans hjx.symm) (hiy.trans hjy.symm)

end PolyominoOddOrder
