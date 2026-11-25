module

public import PolyominoOddOrder.AllEqual

/-!
# Case (I), three occupied corners: the common part (`ThreeCorners.lean`)

Blueprint unit C2 (third increment), with `ThreeN.lean`. `report-A2.md`,
section 5 up to Lemma 5.1. Normal form (`Three`): `E = (0, 0)`,
`A = (p - 1, 0)`, `B = (0, q - 1)` are in `P`, `D = (p - 1, q - 1)` is not, and
`q ≤ p` in the entry statements, so `EA` (the bottom row of `box(P)`) is the long
side.

| report | Lean |
|---|---|
| mark `E` / `A` / `B` of `T_i` | `((o i).negX, (o i).negY)` is `(false, false)` / `(true, false)` / `(false, true)` |
| wide `E`, `A`, `B`; tall `E`, `A`, `B` | the codes `Orient.wE`, `wA`, `wB`, `tE`, `tA`, `tB` |
| `EA`, `EB` are full | `ThreeFull.fullEA`, `ThreeFull.fullEB` |
| `alpha`, `beta` | `colCount P (p - 1)`, `rowCount P (q - 1)` |
| `kappa_c`, `rho_j` | `colCount P c`, `rowCount P j` |
| the table of runs | `Orient.hrun_eq`, `Orient.vrun_eq` with `fullEA`, `fullEB` |

Entry statements for the other files of section 5: `Three.full_N`,
`Three.full_O`, `lemma51_bottom`, `lemma51_top`, `lemma51_left`, `lemma51_right`.

Source: `theoretician/report-A2.md` (goals lab, commit `076d663`), section 5.
-/

@[expose] public section

namespace PolyominoOddOrder

open Orient (cornerP)

variable {P : Finset Cell} {p q a b : ℤ} {t : Fin 5 → Finset Cell} {o : Fin 5 → Orient}
  {x5 y5 : ℤ}

/-! ## The six codes of a corner tile -/

/-- Wide, mark `E`. -/
def Orient.wE : Orient := ⟨false, false, false⟩
/-- Wide, mark `A`. -/
def Orient.wA : Orient := ⟨false, true, false⟩
/-- Wide, mark `B`. -/
def Orient.wB : Orient := ⟨false, false, true⟩
/-- Tall, mark `E`. -/
def Orient.tE : Orient := ⟨true, false, false⟩
/-- Tall, mark `A`. -/
def Orient.tA : Orient := ⟨true, true, false⟩
/-- Tall, mark `B`. -/
def Orient.tB : Orient := ⟨true, false, true⟩

/-! ## Marks; `EA` and `EB` are full -/

/-- The mark of a corner tile is not `D`. -/
theorem Three.mark (S : Three P p q) (F : Frame5 P p q a b t o x5 y5) {i : Fin 5}
    (hi : i ≠ 4) : ¬ ((o i).negX = true ∧ (o i).negY = true) := by
  rintro ⟨hx, hy⟩
  have h := F.mark_mem hi
  rw [hx, hy, cornerP_tt] at h
  exact S.hD h

/-- With three occupied corners `P` has no half turn as a symmetry ((T4): `|S|`
would be even). -/
theorem Three.no_halfTurn (S : Three P p q)
    (h : ∀ c : Cell, c ∈ P ↔ (p - 1 - c.1, q - 1 - c.2) ∈ P) : False :=
  S.hD (by simpa using (h (0, 0)).1 S.hE)

/-- With three occupied corners `P` has no reflection in an axis-parallel line as
a symmetry ((T4): `|S|` would be even). -/
theorem Three.no_reflection (S : Three P p q)
    (h : (∀ c : Cell, c ∈ P ↔ (p - 1 - c.1, c.2) ∈ P) ∨
      (∀ c : Cell, c ∈ P ↔ (c.1, q - 1 - c.2) ∈ P)) : False := by
  rcases h with h | h
  · exact S.hD (by simpa using (h (0, q - 1)).1 S.hB)
  · exact S.hD (by simpa using (h (p - 1, 0)).1 S.hA)

/-- (3) of `report-A2.md`, section 3, for `|S| = 3` in pattern N: two different
corners are used. -/
theorem Three.not_sameMarks_N (S : Three P p q) (F : FrameN P p q a b t o x5 y5) :
    ¬ SameMarks o := fun hm => S.hD (allEqual_N F hm).c11

/-- (3) of `report-A2.md`, section 3, for `|S| = 3` in pattern O. -/
theorem Three.not_sameMarks_O (S : Three P p q) (F : FrameO P p q a b t o x5 y5) :
    ¬ SameMarks o := fun hm => S.no_reflection (allEqual_O F hm)

/-- Three occupied corners together with what `report-A2.md`, section 5, first
paragraph, derives at once: `EA` and `EB` are full, and the sides `AD`, `BD`
hold `alpha` and `beta` cells with `1 ≤ alpha < q`, `1 ≤ beta < p`. -/
structure ThreeFull (P : Finset Cell) (p q : ℤ) : Prop extends Three P p q where
  /-- The side `EA` is full: `rho_0 = p`. -/
  fullEA : rowCount P 0 = p
  /-- The side `EB` is full: `kappa_0 = q`. -/
  fullEB : colCount P 0 = q
  /-- `alpha ≥ 1`. -/
  alpha_pos : 1 ≤ colCount P (p - 1)
  /-- `alpha < q`, as `D` is not in `P`. -/
  alpha_lt : colCount P (p - 1) < q
  /-- `beta ≥ 1`. -/
  beta_pos : 1 ≤ rowCount P (q - 1)
  /-- `beta < p`, as `D` is not in `P`. -/
  beta_lt : rowCount P (q - 1) < p

/-- Two different marks, neither of them `D`: one of them is on the side `EA`
(`negY = false`) and one of them on the side `EB` (`negX = false`). -/
private theorem three_marks_aux {x0 y0 x1 y1 : Bool} (h0 : ¬ (x0 = true ∧ y0 = true))
    (h1 : ¬ (x1 = true ∧ y1 = true)) (hne : ¬ (x1 = x0 ∧ y1 = y0)) :
    (y0 = false ∨ y1 = false) ∧ (x0 = false ∨ x1 = false) := by
  revert x0 y0 x1 y1
  decide

/-- `report-A2.md`, section 5, first paragraph, for the side `EA`: if the mark of
a corner tile is `E` or `A`, its run along `EA` is the whole side by (Full), as
the other end is occupied. -/
private theorem Three.fullEA_of (S : Three P p q) (F : Frame5 P p q a b t o x5 y5)
    {i : Fin 5} (hi : i ≠ 4) (hy : (o i).negY = false) : rowCount P 0 = p := by
  have hfar : cornerP p q (!(o i).negX) false ∈ P := by
    cases (o i).negX
    · simpa [cornerP] using S.hA
    · simpa [cornerP] using S.hE
  cases hs : (o i).swap
  · have h := F.hrun_of_far hi (by simpa [hs, hy] using hfar)
    simpa [Orient.hrun_eq, hs, hy, Orient.W] using h
  · have h := F.vrun_of_far hi (by simpa [hs, hy] using hfar)
    simpa [Orient.vrun_eq, hs, hy, Orient.H] using h

/-- The same for the side `EB`: if the mark of a corner tile is `E` or `B`. -/
private theorem Three.fullEB_of (S : Three P p q) (F : Frame5 P p q a b t o x5 y5)
    {i : Fin 5} (hi : i ≠ 4) (hx : (o i).negX = false) : colCount P 0 = q := by
  have hfar : cornerP p q false (!(o i).negY) ∈ P := by
    cases (o i).negY
    · simpa [cornerP] using S.hB
    · simpa [cornerP] using S.hE
  cases hs : (o i).swap
  · have h := F.vrun_of_far hi (by simpa [hs, hx] using hfar)
    simpa [Orient.vrun_eq, hs, hx, Orient.H] using h
  · have h := F.hrun_of_far hi (by simpa [hs, hx] using hfar)
    simpa [Orient.hrun_eq, hs, hx, Orient.W] using h

/-- `report-A2.md`, section 5, first paragraph: "By (3) two different corners are
used: E is, or A and B are. So EA and EB are full. ... alpha < q, beta < p, as D
is not in P." Two different marks among `E`, `A`, `B`: if one is `E`, (Full)
gives both sides (`Frame5.hrun_of_far`, `vrun_of_far` with `Orient.hrun_eq`,
`vrun_eq`); if they are `A` and `B`, the run of `A` along `EA` and the run of
`B` along `EB`. The bounds are `Frame5.colCount_pos`, `colCount_le`,
`colCount_eq_iff` at the column `p - 1` and the same for the row `q - 1`. -/
theorem Three.full (S : Three P p q) (F : Frame5 P p q a b t o x5 y5)
    (hns : ¬ SameMarks o) : ThreeFull P p q := by
  have hp := F.two_le_p
  have hq := F.two_le_q
  have hex : ∃ i : Fin 5, i ≠ 4 ∧
      ¬ ((o i).negX = (o 0).negX ∧ (o i).negY = (o 0).negY) := by
    by_contra hc
    refine hns fun i hi => ?_
    by_contra h
    exact hc ⟨i, hi, h⟩
  obtain ⟨i, hi, hne⟩ := hex
  obtain ⟨hy, hx⟩ := three_marks_aux (S.mark F (i := 0) (by decide)) (S.mark F hi) hne
  have hEA : rowCount P 0 = p := by
    rcases hy with hy | hy
    · exact S.fullEA_of F (by decide) hy
    · exact S.fullEA_of F hi hy
  have hEB : colCount P 0 = q := by
    rcases hx with hx | hx
    · exact S.fullEB_of F (by decide) hx
    · exact S.fullEB_of F hi hx
  have hal := F.colCount_le (p - 1)
  have hbe := F.rowCount_le (q - 1)
  refine ⟨S, hEA, hEB, F.colCount_pos (by omega) (by omega), ?_,
    F.rowCount_pos (by omega) (by omega), ?_⟩
  · refine lt_of_le_of_ne hal fun h => S.hD ?_
    exact (F.colCount_eq_iff (p - 1)).1 h (q - 1) (by omega) (by omega)
  · refine lt_of_le_of_ne hbe fun h => S.hD ?_
    exact (F.rowCount_eq_iff (q - 1)).1 h (p - 1) (by omega) (by omega)

/-- `ThreeFull` in pattern N. -/
theorem Three.full_N (S : Three P p q) (F : FrameN P p q a b t o x5 y5) : ThreeFull P p q :=
  S.full F.toFrame5 (S.not_sameMarks_N F)

/-- `ThreeFull` in pattern O. -/
theorem Three.full_O (S : Three P p q) (F : FrameO P p q a b t o x5 y5) : ThreeFull P p q :=
  S.full F.toFrame5 (S.not_sameMarks_O F)

/-! ## Lemma 5.1 -/

/-- `report-A2.md`, Lemma 5.1, proof, for `T_1` at a free bottom side. The run of
`T_1` along the side is short only for the marks `B` (wide: `beta < p`) and `A`
(tall: `alpha < q`). Then the mark of `T_2` is the same one ((T1),
`Frame5.T1_bottom`: the run would be the whole side), the other one of `A`, `B`
((T2)(b), `Frame5.T2_bottom`, against `a = W + run < 2 W`), or `E` ((T5),
`Frame5.T5_bottom`). -/
private theorem lemma51_first (F : Frame5 P p q a b t o x5 y5) (S : ThreeFull P p q)
    (hfree : 1 ≤ y5) (h : (o 0).swap = (o 1).swap) :
    (o 0).rowLine p q P 0 = (o 0).W p q := by
  have hm0 := S.mark F (i := 0) (by decide)
  have hm1 := S.mark F (i := 1) (by decide)
  have hs := F.side_bottom hfree
  have hEA := S.fullEA
  have hEB := S.fullEB
  have hal := S.alpha_lt
  have hbe := S.beta_lt
  rcases e0 : o 0 with ⟨s, x0, y0⟩
  rcases e1 : o 1 with ⟨s1, x1, y1⟩
  rw [e0, e1] at h hs
  rw [e0] at hm0
  rw [e1] at hm1
  simp only at h hm0 hm1
  obtain rfl : s1 = s := h.symm
  cases s1 <;> cases x0 <;> cases y0 <;> simp at hm0
  · -- wide, mark `E`
    simp [Orient.rowLine, Orient.W, hEA]
  · -- wide, mark `B`
    exfalso
    cases x1 <;> cases y1 <;> simp at hm1
    · -- `T_2` wide with mark `E`: (T5)
      exact F.T5_bottom hfree (by simp [e0, e1, Orient.reflY])
    · -- `T_2` wide with mark `B`: (T1)
      have h1 := (F.T1_bottom hfree (e0.trans e1.symm)).1
      rw [e0] at h1
      simp [Orient.rowLine, Orient.W] at h1
      omega
    · -- `T_2` wide with mark `A`: (T2)(b)
      have h2 := F.T2_bottom (by simp [e0, e1, Orient.H])
        (by rw [e0]; simpa [Orient.back, Orient.W, Orient.H] using S.hA)
        (by rw [e1]; simpa [Orient.back, Orient.W, Orient.H] using S.hB)
      rw [e0, e1] at h2
      simp [Orient.W] at h2
      simp [Orient.rowLine] at hs
      omega
  · -- wide, mark `A`
    simp [Orient.rowLine, Orient.W, hEA]
  · -- tall, mark `E`
    simp [Orient.rowLine, Orient.W, hEB]
  · -- tall, mark `B`
    simp [Orient.rowLine, Orient.W, hEB]
  · -- tall, mark `A`
    exfalso
    cases x1 <;> cases y1 <;> simp at hm1
    · -- `T_2` tall with mark `E`: (T5)
      exact F.T5_bottom hfree (by simp [e0, e1, Orient.reflY])
    · -- `T_2` tall with mark `B`: (T2)(b)
      have h2 := F.T2_bottom (by simp [e0, e1, Orient.H])
        (by rw [e0]; simpa [Orient.back, Orient.W, Orient.H] using S.hB)
        (by rw [e1]; simpa [Orient.back, Orient.W, Orient.H] using S.hA)
      rw [e0, e1] at h2
      simp [Orient.W] at h2
      simp [Orient.rowLine] at hs
      omega
    · -- `T_2` tall with mark `A`: (T1)
      have h1 := (F.T1_bottom hfree (e0.trans e1.symm)).1
      rw [e0] at h1
      simp [Orient.rowLine, Orient.W] at h1
      omega

/-- **`report-A2.md`, Lemma 5.1 (same orientation), `p > q`, bottom side.** If
the two corner tiles at a free side are both wide or both tall, both their runs
along the side are whole sides of their boxes. Proof of the report: the run is
short only for one mark (`B` if `EA` lies along the side, `A` if `EB` does); if
both tiles have it, (T1) (`Frame5.T1_bottom`); if the other tile has the other
one of `A`, `B`, (T2)(b) (`Frame5.T2_bottom`: both opposite corners are
occupied, and the runs add up to less than `W_1 + W_2`); if the other tile has
`E`, (T5) (`Frame5.T5_bottom`: the second code is the first with the local
vertical direction reversed). -/
theorem lemma51_bottom (F : Frame5 P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (hfree : 1 ≤ y5) (h : (o 0).swap = (o 1).swap) :
    (o 0).rowLine p q P 0 = (o 0).W p q ∧ (o 1).rowLine p q P 0 = (o 1).W p q := by
  -- the proof does not use `q < p`: for `p = q` the same three tools apply
  have _ := hq
  refine ⟨lemma51_first F S hfree h, ?_⟩
  obtain ⟨t', F'⟩ := F.flipX
  simpa using lemma51_first F' S hfree (by simpa using h.symm)

/-- Lemma 5.1 at a free top side. -/
theorem lemma51_top (F : Frame5 P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (hfree : y5 + (o 4).H p q ≤ b - 1) (h : (o 2).swap = (o 3).swap) :
    (o 2).rowLine p q P 0 = (o 2).W p q ∧ (o 3).rowLine p q P 0 = (o 3).W p q := by
  obtain ⟨t', F'⟩ := F.flipY
  have h' := lemma51_bottom F' S hq (by omega) (by simpa using h.symm)
  simpa [and_comm] using h'

/-- Lemma 5.1 at a free left side. -/
theorem lemma51_left (F : Frame5 P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (hfree : 1 ≤ x5) (h : (o 0).swap = (o 3).swap) :
    (o 0).colLine p q P 0 = (o 0).H p q ∧ (o 3).colLine p q P 0 = (o 3).H p q := by
  obtain ⟨t', F'⟩ := F.transpose
  have h' := lemma51_bottom F' S hq hfree (by simpa using h)
  simpa [Orient.rowLine_tr] using h'

/-- Lemma 5.1 at a free right side. -/
theorem lemma51_right (F : Frame5 P p q a b t o x5 y5) (S : ThreeFull P p q) (hq : q < p)
    (hfree : x5 + (o 4).W p q ≤ a - 1) (h : (o 1).swap = (o 2).swap) :
    (o 1).colLine p q P 0 = (o 1).H p q ∧ (o 2).colLine p q P 0 = (o 2).H p q := by
  obtain ⟨t', F'⟩ := F.transpose
  have h' := lemma51_top F' S hq (by simpa using hfree) (by simpa using h.symm)
  simpa [Orient.rowLine_tr, and_comm] using h'

end PolyominoOddOrder
