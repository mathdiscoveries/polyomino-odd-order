module

public import PolyominoOddOrder.Frame5Lemmas
public import PolyominoOddOrder.PolyDivisibility

/-!
# Case (I), two opposite occupied corners: common part and pattern N (`OppositeN.lean`)

Blueprint unit C7 (third increment). `report-A2.md`, section 7 up to the end of
7.2. Normal form (`Opposite`): `A = (0, 0)` and `C = (p - 1, q - 1)` are in `P`,
the other two corners of `box(P)` are not. The entry statements assume
`q ≤ p`, so the long direction of `box(P)` is the first coordinate; 7.1 gives
`q < p`.

| report | Lean |
|---|---|
| mark `A` / `C` of `T_i` | `(o i).negX = false` / `true`, with `(o i).negY = (o i).negX` (`Opposite.mark`) |
| `h_j`, `v_j` | `oppH P q j`, `oppV P p j` (`j = false` for `A`, `true` for `C`) |
| `h_j < p`, `v_j < q` | `OppFull` |
| `X_j(c)`, `Y_j(c)` | `colCount P c`, `rowCount P c` for `j = A`; `colCount P (p - 1 - c)`, `rowCount P (q - 1 - c)` for `j = C` |
| `T_1`, `T_3` wide, `T_2`, `T_4` tall | `Alt o` |
| (14) in pattern N: `h_A = h_C`, `v_A = v_C`, `a = b = h + v` | `Setup72` |
| `j_L`, `j_B` (`T_5` wide) | `(o 4).negX`, `(o 4).negY` (`false` for `A`) |
| `o_L`, `o_R`, `o_B`, `o_T` | `x5`, `a - p - x5`, `y5`, `a - q - y5` |
| `X_j(z)`, `Y_j(z)`, `[s]`, `M(z)`, `w` | `profX`, `profY`, `geom`, `M72`, `prof72` |
| (15) | `n72_det_odd`, `n72_det_three` |

The divisibility step is stated against `PolyDivisibility.lean`: with
`s = l^k s'` the four equations are `M w = C (l^k) * (C s' * [s])`, so `l^k`
divides `X_A(0) = v` and `Y_A(0) = h` (`n72_pow_dvd`), while `s = 2v`, `3v` or
`3h` (`no_pow_tower`).

Entry statements (binding): `OppFull`, `Opposite.full`, `Opposite.mark`,
`Opposite.hrun`, `Opposite.vrun`, `Alt`, `opp_alt` (used by `OppositeO.lean`)
and `opp_N`.

Source: `theoretician/report-A2.md` (goals lab, commit `076d663`), section 7.
-/

@[expose] public section

open Polynomial

namespace PolyominoOddOrder

open Orient (cornerP)

variable {P : Finset Cell} {p q a b : ℤ} {t : Fin 5 → Finset Cell} {o : Fin 5 → Orient}
  {x5 y5 : ℤ}

/-! ## Marks and runs -/

/-- `h_j` of `report-A2.md`, section 7: the run of the occupied corner `j` along
the long side of `box(P)`; `j = false` is `A`, `j = true` is `C`. -/
def oppH (P : Finset Cell) (q : ℤ) (j : Bool) : ℤ := rowCount P (if j then q - 1 else 0)

/-- `v_j`: the run of the occupied corner `j` along the short side. -/
def oppV (P : Finset Cell) (p : ℤ) (j : Bool) : ℤ := colCount P (if j then p - 1 else 0)

/-- The mark of a corner tile is `A` or `C`. -/
theorem Opposite.mark (S : Opposite P p q) (F : Frame5 P p q a b t o x5 y5) {i : Fin 5}
    (hi : i ≠ 4) : (o i).negY = (o i).negX := by
  have h := F.mark_mem hi
  cases hx : (o i).negX <;> cases hy : (o i).negY <;> rw [hx, hy] at h
  · rw [cornerP_ft] at h
    exact absurd h S.h01
  · rw [cornerP_tf] at h
    exact absurd h S.h10

/-- The half turn of `P` in its box exchanges the names `A` and `C` ("Let
m_1 = A", 7.3). -/
theorem Opposite.turnP (S : Opposite P p q) :
    Opposite ((P.image (GridIso.flipX p).apply).image (GridIso.flipY q).apply) p q := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← cornerP_ff (p := p) (q := q), cornerP_mem_flipPY, cornerP_mem_flipPX]
    simpa [cornerP] using S.hC
  · rw [← cornerP_tt (p := p) (q := q), cornerP_mem_flipPY, cornerP_mem_flipPX]
    simpa [cornerP] using S.hA
  · rw [← cornerP_tf (p := p) (q := q), cornerP_mem_flipPY, cornerP_mem_flipPX]
    simpa [cornerP] using S.h01
  · rw [← cornerP_ft (p := p) (q := q), cornerP_mem_flipPY, cornerP_mem_flipPX]
    simpa [cornerP] using S.h10

/-- Two opposite occupied corners together with `report-A2.md`, section 7, first
paragraph: "h_j < p, v_j < q, as the other corners are not occupied". -/
structure OppFull (P : Finset Cell) (p q : ℤ) : Prop extends Opposite P p q where
  /-- `h_j ≥ 1`. -/
  h_pos : ∀ j : Bool, 1 ≤ oppH P q j
  /-- `h_j < p`. -/
  h_lt : ∀ j : Bool, oppH P q j < p
  /-- `v_j ≥ 1`. -/
  v_pos : ∀ j : Bool, 1 ≤ oppV P p j
  /-- `v_j < q`. -/
  v_lt : ∀ j : Bool, oppV P p j < q

/-- `report-A2.md`, section 7, first paragraph. -/
theorem Opposite.full (S : Opposite P p q) (F : Frame5 P p q a b t o x5 y5) : OppFull P p q := by
  have hp := F.two_le_p
  have hq := F.two_le_q
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · intro j
    cases j
    · simpa [oppH] using F.rowCount_pos (y := 0) le_rfl (by omega)
    · simpa [oppH] using F.rowCount_pos (y := q - 1) (by omega) (by omega)
  · intro j
    rcases lt_or_eq_of_le (F.rowCount_le (if j then q - 1 else 0)) with h | h
    · exact h
    · exfalso
      have hall := (F.rowCount_eq_iff _).1 h
      cases j
      · exact S.h10 (by simpa using hall (p - 1) (by omega) (by omega))
      · exact S.h01 (by simpa using hall 0 le_rfl (by omega))
  · intro j
    cases j
    · simpa [oppV] using F.colCount_pos (x := 0) le_rfl (by omega)
    · simpa [oppV] using F.colCount_pos (x := p - 1) (by omega) (by omega)
  · intro j
    rcases lt_or_eq_of_le (F.colCount_le (if j then p - 1 else 0)) with h | h
    · exact h
    · exfalso
      have hall := (F.colCount_eq_iff _).1 h
      cases j
      · exact S.h01 (by simpa using hall (q - 1) (by omega) (by omega))
      · exact S.h10 (by simpa using hall 0 le_rfl (by omega))

/-- The run of a corner tile along the horizontal side at its corner: `h` of its
mark if it is wide, `v` if it is tall. -/
theorem Opposite.hrun (S : Opposite P p q) (F : Frame5 P p q a b t o x5 y5) {i : Fin 5}
    (hi : i ≠ 4) :
    (o i).rowLine p q P 0 = if (o i).swap then oppV P p (o i).negX else oppH P q (o i).negX := by
  rw [Orient.hrun_eq, S.mark F hi]
  rfl

/-- The run of a corner tile along the vertical side at its corner. -/
theorem Opposite.vrun (S : Opposite P p q) (F : Frame5 P p q a b t o x5 y5) {i : Fin 5}
    (hi : i ≠ 4) :
    (o i).colLine p q P 0 = if (o i).swap then oppH P q (o i).negX else oppV P p (o i).negX := by
  rw [Orient.vrun_eq, S.mark F hi]
  rfl

/-- "The corner of box(T_i) opposite to the mark m_i is m_i' and it is
occupied." -/
theorem Opposite.far_mem (S : Opposite P p q) (F : Frame5 P p q a b t o x5 y5) {i : Fin 5}
    (hi : i ≠ 4) : (o i).back p q ((o i).W p q - 1, (o i).H p q - 1) ∈ P := by
  rw [Orient.back_WH, S.mark F hi]
  cases (o i).negX
  · simpa [cornerP] using S.hC
  · simpa [cornerP] using S.hA

/-- `u_i < W_i` for a corner tile. -/
theorem OppFull.hrun_lt (S : OppFull P p q) (F : Frame5 P p q a b t o x5 y5) {i : Fin 5}
    (hi : i ≠ 4) : (o i).rowLine p q P 0 < (o i).W p q := by
  rw [S.toOpposite.hrun F hi]
  cases h : (o i).swap
  · simpa [Orient.W, h] using S.h_lt _
  · simpa [Orient.W, h] using S.v_lt _

/-- `v_i < H_i` for a corner tile. -/
theorem OppFull.vrun_lt (S : OppFull P p q) (F : Frame5 P p q a b t o x5 y5) {i : Fin 5}
    (hi : i ≠ 4) : (o i).colLine p q P 0 < (o i).H p q := by
  rw [S.toOpposite.vrun F hi]
  cases h : (o i).swap
  · simpa [Orient.H, h] using S.v_lt _
  · simpa [Orient.H, h] using S.h_lt _

/-! ## 7.1 The boxes alternate -/

/-- **`report-A2.md`, 7.1, bottom side.** At a free side the two boxes have
different extents perpendicular to the side: with `H_1 = H_2`, `u_1 < W_1` and
`u_2 < W_2` give `a < W_1 + W_2`, against (T2)(b) (`Frame5.T2_bottom`). -/
theorem lemma71_bottom (F : Frame5 P p q a b t o x5 y5) (S : OppFull P p q) (hfree : 1 ≤ y5) :
    (o 0).H p q ≠ (o 1).H p q := by
  intro hH
  have h2 := F.T2_bottom hH (S.toOpposite.far_mem F (by decide))
    (S.toOpposite.far_mem F (by decide))
  have h1 := F.side_bottom hfree
  have u0 := S.hrun_lt F (i := 0) (by decide)
  have u1 := S.hrun_lt F (i := 1) (by decide)
  omega

/-- 7.1 at a free top side. -/
theorem lemma71_top (F : Frame5 P p q a b t o x5 y5) (S : OppFull P p q)
    (hfree : y5 + (o 4).H p q ≤ b - 1) : (o 2).H p q ≠ (o 3).H p q := by
  obtain ⟨t', F'⟩ := F.flipY
  have h := lemma71_bottom F' S (by omega)
  intro e
  apply h
  simpa using e.symm

/-- 7.1 at a free left side. -/
theorem lemma71_left (F : Frame5 P p q a b t o x5 y5) (S : OppFull P p q) (hfree : 1 ≤ x5) :
    (o 0).W p q ≠ (o 3).W p q := by
  obtain ⟨t', F'⟩ := F.transpose
  have h := lemma71_bottom F' S hfree
  simpa using h

/-- 7.1 at a free right side. -/
theorem lemma71_right (F : Frame5 P p q a b t o x5 y5) (S : OppFull P p q)
    (hfree : x5 + (o 4).W p q ≤ a - 1) : (o 1).W p q ≠ (o 2).W p q := by
  obtain ⟨t', F'⟩ := F.transpose
  have h := lemma71_top F' S (by simpa using hfree)
  intro e
  apply h
  simpa using e.symm

/-- **`report-A2.md`, 7.1.** "So p > q, and (with the left, top, right side) T_1,
T_3 have one orientation, T_2, T_4 the other." Only the three sides that are
free in both patterns are used. -/
theorem opp_alt (F : Frame5 P p q a b t o x5 y5) (S : OppFull P p q)
    (htop : y5 + (o 4).H p q ≤ b - 1) (hleft : 1 ≤ x5) (hright : x5 + (o 4).W p q ≤ a - 1) :
    p ≠ q ∧ (o 0).swap = (o 2).swap ∧ (o 1).swap = (o 3).swap ∧ (o 0).swap ≠ (o 1).swap := by
  have h1 := lemma71_top F S htop
  have h2 := lemma71_left F S hleft
  have h3 := lemma71_right F S hright
  have hpq : p ≠ q := fun e => h1 (by simp [Orient.H, e])
  have e23 : (o 2).swap ≠ (o 3).swap := fun e => h1 (by simp [Orient.H, e])
  have e03 : (o 0).swap ≠ (o 3).swap := fun e => h2 (by simp [Orient.W, e])
  have e12 : (o 1).swap ≠ (o 2).swap := fun e => h3 (by simp [Orient.W, e])
  refine ⟨hpq, ?_⟩
  revert e23 e03 e12
  cases (o 0).swap <;> cases (o 1).swap <;> cases (o 2).swap <;> cases (o 3).swap <;> simp

/-- The normal form of 7.1: "Reflect R so that T_1, T_3 are wide, T_2, T_4
tall." -/
structure Alt (o : Fin 5 → Orient) : Prop where
  /-- `T_1` is wide. -/
  w0 : (o 0).swap = false
  /-- `T_2` is tall. -/
  t1 : (o 1).swap = true
  /-- `T_3` is wide. -/
  w2 : (o 2).swap = false
  /-- `T_4` is tall. -/
  t3 : (o 3).swap = true

/-- The normal form, if `T_1` is wide. -/
theorem Alt.of (h0 : (o 0).swap = false) (h02 : (o 0).swap = (o 2).swap)
    (h13 : (o 1).swap = (o 3).swap) (h01 : (o 0).swap ≠ (o 1).swap) : Alt o := by
  rw [h0] at h01
  have h1 : (o 1).swap = true := by simpa using h01.symm
  exact ⟨h0, h1, by rw [← h02]; exact h0, by rw [← h13]; exact h1⟩

/-- The normal form after the reflection of `R a b` in its vertical midline, if
`T_1` is tall. -/
theorem Alt.flip (h0 : (o 0).swap = true) (h02 : (o 0).swap = (o 2).swap)
    (h13 : (o 1).swap = (o 3).swap) (h01 : (o 0).swap ≠ (o 1).swap) (c : Orient) :
    Alt ![o 1, o 0, o 3, o 2, c] := by
  rw [h0] at h01
  have h1 : (o 1).swap = false := by simpa using h01.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (o 1).swap = false
    exact h1
  · show (o 0).swap = true
    exact h0
  · show (o 3).swap = false
    rw [← h13]
    exact h1
  · show (o 2).swap = true
    rw [← h02]
    exact h0

/-! ## 7.2 Pattern N -/

/-- (14) in pattern N, solved (`report-A2.md`, 7.2, first paragraph):
`h_A = h_C =: h`, `v_A = v_C =: v`, `a = b = h + v =: s`. -/
structure Setup72 (P : Finset Cell) (p q a b : ℤ) : Prop where
  /-- `h_C = h_A`. -/
  hh : oppH P q true = oppH P q false
  /-- `v_C = v_A`. -/
  vv : oppV P p true = oppV P p false
  /-- `a = h + v`. -/
  ha : a = oppH P q false + oppV P p false
  /-- `b = a`. -/
  hb : b = a

/-- Two corner tiles with the same orientation of the box and the same mark have
the same code (the mark fixes `negY` by `Opposite.mark`). -/
private theorem sa_code_eq (S : Opposite P p q) (F : Frame5 P p q a b t o x5 y5) {i j : Fin 5}
    (hi : i ≠ 4) (hj : j ≠ 4) (hs : (o i).swap = (o j).swap) (hx : (o i).negX = (o j).negX) :
    o i = o j :=
  Orient.ext hs hx (by rw [S.mark F hi, S.mark F hj, hx])

/-- The row counts of a set with the half turn of `box(P)` as a symmetry. -/
private theorem sa_rowCount_turn (hP : ∀ c : Cell, c ∈ P ↔ (p - 1 - c.1, q - 1 - c.2) ∈ P)
    (y : ℤ) : rowCount P (q - 1 - y) = rowCount P y := by
  unfold rowCount
  congr 1
  refine Finset.card_nbij' (fun c => (p - 1 - c.1, q - 1 - c.2))
    (fun c => (p - 1 - c.1, q - 1 - c.2)) ?_ ?_ ?_ ?_
  · rintro ⟨x, z⟩ hc
    simp only [Finset.mem_coe, Finset.mem_filter] at hc ⊢
    obtain ⟨hc, rfl⟩ := hc
    exact ⟨(hP _).1 hc, by ring⟩
  · rintro ⟨x, z⟩ hc
    simp only [Finset.mem_coe, Finset.mem_filter] at hc ⊢
    obtain ⟨hc, rfl⟩ := hc
    exact ⟨(hP _).1 hc, rfl⟩
  · rintro ⟨x, z⟩ -
    simp
  · rintro ⟨x, z⟩ -
    simp

/-- The column counts of a set with the half turn of `box(P)` as a symmetry. -/
private theorem sa_colCount_turn (hP : ∀ c : Cell, c ∈ P ↔ (p - 1 - c.1, q - 1 - c.2) ∈ P)
    (x : ℤ) : colCount P (p - 1 - x) = colCount P x := by
  unfold colCount
  congr 1
  refine Finset.card_nbij' (fun c => (p - 1 - c.1, q - 1 - c.2))
    (fun c => (p - 1 - c.1, q - 1 - c.2)) ?_ ?_ ?_ ?_
  · rintro ⟨z, y⟩ hc
    simp only [Finset.mem_coe, Finset.mem_filter] at hc ⊢
    obtain ⟨hc, rfl⟩ := hc
    exact ⟨(hP _).1 hc, by ring⟩
  · rintro ⟨z, y⟩ hc
    simp only [Finset.mem_coe, Finset.mem_filter] at hc ⊢
    obtain ⟨hc, rfl⟩ := hc
    exact ⟨(hP _).1 hc, rfl⟩
  · rintro ⟨z, y⟩ -
    simp
  · rintro ⟨z, y⟩ -
    simp

/-- "Hd = Vd = 0" when the half turn of `R a b` permutes the corner tiles:
`m_1 = m_3`, `m_2 = m_4` give a half turn of `P` (`Frame5.T4_halfTurn`), which
exchanges `A` and `C`. -/
private theorem sa_runs_of_turn (F : Frame5 P p q a b t o x5 y5) (S : Opposite P p q) (A : Alt o)
    (h02 : (o 0).negX = (o 2).negX) (h13 : (o 1).negX = (o 3).negX) :
    (∀ c : Cell, c ∈ P ↔ (p - 1 - c.1, q - 1 - c.2) ∈ P) ∧
      oppH P q true = oppH P q false ∧ oppV P p true = oppV P p false := by
  have e02 := sa_code_eq S F (i := 0) (j := 2) (by decide) (by decide)
    (by rw [A.w0, A.w2]) h02
  have e13 := sa_code_eq S F (i := 1) (j := 3) (by decide) (by decide)
    (by rw [A.t1, A.t3]) h13
  obtain ⟨-, -, hP⟩ := F.T4_halfTurn e02 e13
  refine ⟨hP, ?_, ?_⟩
  · simpa [oppH] using sa_rowCount_turn hP 0
  · simpa [oppV] using sa_colCount_turn hP 0

/-- **`report-A2.md`, 7.2, first paragraph.** (1) is (14) with right side 0. If
`(Hd, Vd) ≠ (0, 0)`, the determinant `-(Hd^2 + Vd^2)` gives `d = e = 0`:
`m_1 = m_3`, `m_2 = m_4`, so `o 0 = o 2`, `o 1 = o 3`, the half turn of `R a b`
permutes the corner tiles, `P` has a half turn by (T4) (`Frame5.T4_halfTurn`),
which exchanges `A` and `C`: `Hd = Vd = 0`. -/
theorem n72_setup (F : FrameN P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) : Setup72 P p q a b := by
  -- (14) is solved without `q < p`; the binding statement keeps the hypothesis
  have _ := hq
  have hB := F.side_bottom
  have hT := F.side_top
  have hL := F.side_left
  have hR := F.side_right
  rw [S.toOpposite.hrun F.toFrame5 (i := 0) (by decide),
    S.toOpposite.hrun F.toFrame5 (i := 1) (by decide)] at hB
  rw [S.toOpposite.hrun F.toFrame5 (i := 2) (by decide),
    S.toOpposite.hrun F.toFrame5 (i := 3) (by decide)] at hT
  rw [S.toOpposite.vrun F.toFrame5 (i := 0) (by decide),
    S.toOpposite.vrun F.toFrame5 (i := 3) (by decide)] at hL
  rw [S.toOpposite.vrun F.toFrame5 (i := 1) (by decide),
    S.toOpposite.vrun F.toFrame5 (i := 2) (by decide)] at hR
  simp only [A.w0, A.t1, A.w2, A.t3, Bool.false_eq_true, ↓reduceIte] at hB hT hL hR
  -- `d = e = 0`: the half turn; otherwise the determinant `-(Hd^2 + Vd^2)`
  have hturn : (o 0).negX = (o 2).negX → (o 1).negX = (o 3).negX →
      oppH P q true = oppH P q false ∧ oppV P p true = oppV P p false :=
    fun h02 h13 => (sa_runs_of_turn F.toFrame5 S.toOpposite A h02 h13).2
  generalize (o 0).negX = m1 at hB hL hturn
  generalize (o 1).negX = m2 at hB hR hturn
  generalize (o 2).negX = m3 at hT hR hturn
  generalize (o 3).negX = m4 at hT hL hturn
  have key : oppH P q true = oppH P q false ∧ oppV P p true = oppV P p false := by
    cases m1 <;> cases m2 <;> cases m3 <;> cases m4 <;>
      first
      | exact hturn rfl rfl
      | exact ⟨by omega, by omega⟩
  obtain ⟨hh, vv⟩ := key
  refine ⟨hh, vv, ?_, ?_⟩ <;> cases m1 <;> cases m2 <;> cases m3 <;> cases m4 <;> omega

/-- The half turn of `box(P)` in codes: turning a code moves each cell of
`box(P)` to the opposite cell. -/
private theorem sa_back_turn (c : Orient) (p q : ℤ) (d : Cell) :
    c.turn.back p q d = (p - 1 - (c.back p q d).1, q - 1 - (c.back p q d).2) := by
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;> simp [Orient.turn, Orient.back]

/-- A code of a corner tile with two equal switches, changed to mark `A`. -/
private theorem sa_turn_mark {c : Orient} (hy : c.negY = c.negX) :
    (if c.negX then c.turn else c) = ⟨c.swap, false, false⟩ := by
  revert hy
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;> simp [Orient.turn]

/-- **`report-A2.md`, 7.2, "m_1 = m_3 and m_2 = m_4 is impossible".** `P` has a
half turn (`Frame5.T4_halfTurn`), so a corner tile is determined by its corner
of `R a b` and its orientation: the codes can be changed to mark `A` everywhere.
Then the quarter turn of `R a b` (`a = b`) permutes the corner tiles and `p = q`
by (T4) (`Frame5.T4_quarter`). -/
theorem n72_period (F : FrameN P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (h02 : (o 0).negX = (o 2).negX) (h13 : (o 1).negX = (o 3).negX) : False := by
  have K := n72_setup F S hq A
  obtain ⟨hP, -, -⟩ := sa_runs_of_turn F.toFrame5 S.toOpposite A h02 h13
  -- the codes changed to mark `A` everywhere describe the same tiles
  have hmem : ∀ (i : Fin 5) (c : Cell),
      (if (o i).negX then (o i).turn else o i).back p q c ∈ P ↔ (o i).back p q c ∈ P := by
    intro i c
    cases (o i).negX
    · exact Iff.rfl
    · simp only [↓reduceIte, sa_back_turn]
      exact (hP _).symm
  have F' : Frame5 P p q a b t (fun i => if (o i).negX then (o i).turn else o i) x5 y5 :=
    ⟨F.poly, F.notRect, F.sub, F.left, F.right, F.bottom, F.top, F.tiling,
      fun i c => (F.mem i c).trans (hmem i _).symm, fun i hi => (hmem i _).2 (F.corner i hi)⟩
  have c0 : (if (o 0).negX then (o 0).turn else o 0) = ⟨false, false, false⟩ := by
    rw [sa_turn_mark (S.toOpposite.mark F.toFrame5 (i := 0) (by decide)), A.w0]
  have c1 : (if (o 1).negX then (o 1).turn else o 1) = ⟨true, false, false⟩ := by
    rw [sa_turn_mark (S.toOpposite.mark F.toFrame5 (i := 1) (by decide)), A.t1]
  have c2 : (if (o 2).negX then (o 2).turn else o 2) = ⟨false, false, false⟩ := by
    rw [sa_turn_mark (S.toOpposite.mark F.toFrame5 (i := 2) (by decide)), A.w2]
  have c3 : (if (o 3).negX then (o 3).turn else o 3) = ⟨true, false, false⟩ := by
    rw [sa_turn_mark (S.toOpposite.mark F.toFrame5 (i := 3) (by decide)), A.t3]
  have hpq := (F'.T4_quarter K.hb.symm (by simp only [c0, c1]; rfl) (by simp only [c0, c2])
    (by simp only [c1, c3])).1
  omega

/-- `X_j(c)` of `report-A2.md`, section 7: the number of cells of `P` at
distance `c` from the corner `j` in the long direction (`j = false` is `A`). -/
private def sr_X (P : Finset Cell) (p : ℤ) (j : Bool) (c : ℤ) : ℤ :=
  colCount P (if j then p - 1 - c else c)

/-- `Y_j(c)`: the number of cells of `P` at distance `c` from the corner `j`
in the short direction. -/
private def sr_Y (P : Finset Cell) (q : ℤ) (j : Bool) (c : ℤ) : ℤ :=
  rowCount P (if j then q - 1 - c else c)

/-- `X_j(c) = 0` outside `0 ≤ c < p`. -/
private theorem sr_X_zero (F : Frame5 P p q a b t o x5 y5) (j : Bool) {x : ℤ}
    (h : x < 0 ∨ p ≤ x) : sr_X P p j x = 0 := by
  cases j
  · exact F.colCount_zero h
  · exact F.colCount_zero (by omega)

/-- `Y_j(c) = 0` outside `0 ≤ c < q`. -/
private theorem sr_Y_zero (F : Frame5 P p q a b t o x5 y5) (j : Bool) {y : ℤ}
    (h : y < 0 ∨ q ≤ y) : sr_Y P q j y = 0 := by
  cases j
  · exact F.rowCount_zero h
  · exact F.rowCount_zero (by omega)

/-- "X_{j'}(c) = X_j(p-1-c)". -/
private theorem sr_X_rev (j : Bool) (x : ℤ) : sr_X P p j (p - 1 - x) = sr_X P p (!j) x := by
  cases j <;> simp [sr_X]

/-- "Y_{j'}(c) = Y_j(q-1-c)". -/
private theorem sr_Y_rev (j : Bool) (y : ℤ) : sr_Y P q j (q - 1 - y) = sr_Y P q (!j) y := by
  cases j <;> simp [sr_Y]

/-- `X_j(0) = v_j = v` in pattern N (`Setup72`). -/
private theorem sr_X_start (K : Setup72 P p q a b) (j : Bool) : sr_X P p j 0 = oppV P p false := by
  cases j
  · simp [sr_X, oppV]
  · rw [← K.vv]
    simp [sr_X, oppV]

/-- `Y_j(0) = h_j = h` in pattern N. -/
private theorem sr_Y_start (K : Setup72 P p q a b) (j : Bool) : sr_Y P q j 0 = oppH P q false := by
  cases j
  · simp [sr_Y, oppH]
  · rw [← K.hh]
    simp [sr_Y, oppH]

/-- A column of a wide tile is a column of `P`, read from its mark. -/
private theorem sr_colLine_wide {c : Orient} (h : c.swap = false) (x : ℤ) :
    c.colLine p q P x = sr_X P p c.negX x := by
  simp [Orient.colLine, h, sr_X]

/-- A column of a tall tile is a row of `P`. -/
private theorem sr_colLine_tall {c : Orient} (h : c.swap = true) (x : ℤ) :
    c.colLine p q P x = sr_Y P q c.negY x := by
  simp [Orient.colLine, h, sr_Y]

/-- A row of a wide tile is a row of `P`. -/
private theorem sr_rowLine_wide {c : Orient} (h : c.swap = false) (y : ℤ) :
    c.rowLine p q P y = sr_Y P q c.negY y := by
  simp [Orient.rowLine, h, sr_Y]

/-- A row of a tall tile is a column of `P`. -/
private theorem sr_rowLine_tall {c : Orient} (h : c.swap = true) (y : ℤ) :
    c.rowLine p q P y = sr_X P p c.negX y := by
  simp [Orient.rowLine, h, sr_X]

/-- The four side equations of `report-A2.md`, 7.2, "Ratios", for `c < N = s - p`
(the line at distance `c` from a side meets only the two corner tiles at that
side and `T_5`): left `X_{m_1} + Y_{m_4} + t_L = s`, right
`X_{m_3} + Y_{m_2} + t_R = s`, bottom `X_{m_2} + Y_{m_1} + t_B = s`, top
`X_{m_4} + Y_{m_3} + t_T = s`, with `t_L(c) = X_{j_L}(c - o_L)`,
`t_R(c) = X_{j_L'}(c - o_R)`, `t_B(c) = Y_{j_B}(c - o_B)`,
`t_T(c) = Y_{j_B'}(c - o_T)`. -/
private theorem sr_sides (F : FrameN P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (K : Setup72 P p q a b) (h4 : (o 4).swap = false) {c : ℤ} (h0 : 0 ≤ c)
    (h1 : c < a - p) :
    sr_X P p (o 0).negX c + sr_Y P q (o 3).negX c + sr_X P p (o 4).negX (c - x5) = a ∧
    sr_X P p (o 2).negX c + sr_Y P q (o 1).negX c +
      sr_X P p (!(o 4).negX) (c - (a - p - x5)) = a ∧
    sr_X P p (o 1).negX c + sr_Y P q (o 0).negX c + sr_Y P q (o 4).negY (c - y5) = a ∧
    sr_X P p (o 3).negX c + sr_Y P q (o 2).negX c +
      sr_Y P q (!(o 4).negY) (c - (a - q - y5)) = a := by
  have F5 := F.toFrame5
  have hb := K.hb
  have hp := F5.two_le_p
  have m0 := S.toOpposite.mark F5 (i := 0) (by decide)
  have m1 := S.toOpposite.mark F5 (i := 1) (by decide)
  have m2 := S.toOpposite.mark F5 (i := 2) (by decide)
  have m3 := S.toOpposite.mark F5 (i := 3) (by decide)
  have cl := F5.col_sum (x := c) h0 (by omega)
  have cr := F5.col_sum (x := a - 1 - c) (by omega) (by omega)
  have rb := F5.row_sum (y := c) h0 (by omega)
  have rt := F5.row_sum (y := b - 1 - c) (by omega) (by omega)
  rw [sr_colLine_wide A.w0, sr_colLine_tall A.t1, sr_colLine_wide A.w2, sr_colLine_tall A.t3,
    sr_colLine_wide h4] at cl cr
  rw [sr_rowLine_wide A.w0, sr_rowLine_tall A.t1, sr_rowLine_wide A.w2, sr_rowLine_tall A.t3,
    sr_rowLine_wide h4] at rb rt
  rw [show a - 1 - (a - 1 - c) = c by ring] at cr
  rw [show b - 1 - (b - 1 - c) = c by ring] at rt
  rw [sr_Y_zero F5 _ (y := a - 1 - c) (by omega), sr_X_zero F5 _ (x := a - 1 - c) (by omega)]
    at cl
  rw [sr_X_zero F5 _ (x := a - 1 - c) (by omega), sr_Y_zero F5 _ (y := a - 1 - c) (by omega),
    show a - 1 - c - x5 = p - 1 - (c - (a - p - x5)) by ring, sr_X_rev] at cr
  rw [sr_Y_zero F5 _ (y := b - 1 - c) (by omega), sr_X_zero F5 _ (x := b - 1 - c) (by omega)]
    at rb
  rw [sr_Y_zero F5 _ (y := b - 1 - c) (by omega), sr_X_zero F5 _ (x := b - 1 - c) (by omega),
    show b - 1 - c - y5 = q - 1 - (c - (a - q - y5)) by rw [hb]; ring, sr_Y_rev] at rt
  rw [m3] at cl
  rw [m1] at cr
  rw [m0] at rb
  rw [m2] at rt
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- The argument of the first bullet: a vertical side `V` and a horizontal side
`H` with the same corner terms give `t_V(c) = t_H(c)` for `c < N`. "At
c = o_V the left side is v > 0, so o_H <= o_V; at c = o_H the right side is
h > 0, so o_V <= o_H. So o_V = o_H and h = v." -/
private theorem sr_three_core (F : Frame5 P p q a b t o x5 y5) (S : OppFull P p q)
    (K : Setup72 P p q a b) {mx my jV jH : Bool} {oV oH N : ℤ} (hoV : 0 ≤ oV) (hoVN : oV < N)
    (hoH : 0 ≤ oH)
    (hV : ∀ c, 0 ≤ c → c < N → sr_X P p mx c + sr_Y P q my c + sr_X P p jV (c - oV) = a)
    (hH : ∀ c, 0 ≤ c → c < N → sr_X P p mx c + sr_Y P q my c + sr_Y P q jH (c - oH) = a) :
    oppH P q false = oppV P p false := by
  have hv := S.v_pos false
  have hh := S.h_pos false
  have eV := sr_X_start K jV
  have eH := sr_Y_start K jH
  have e1 := hV oV hoV hoVN
  have e1' := hH oV hoV hoVN
  rw [sub_self, eV] at e1
  have hle : oH ≤ oV := by
    by_contra hlt
    rw [sr_Y_zero F jH (y := oV - oH) (by omega)] at e1'
    omega
  have e2 := hV oH hoH (by omega)
  have e2' := hH oH hoH (by omega)
  rw [sub_self, eH] at e2'
  have hle' : oV ≤ oH := by
    by_contra hlt
    rw [sr_X_zero F jV (x := oH - oV) (by omega)] at e2
    omega
  obtain rfl : oH = oV := le_antisymm hle hle'
  rw [sub_self, eH] at e1'
  omega

/-- **`report-A2.md`, 7.2, "Ratios", first bullet:** three marks equal, the
fourth different (exactly one of `m_1 = m_3`, `m_2 = m_4`), `T_5` wide. The two
sides of `R a b` that do not end at the corner of the fourth have the same
corner terms, so `t_V(c) = t_H(c)` for `c < N`; `o_V = o_H` and `h = v`. -/
theorem n72_ratio_three (F : FrameN P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (K : Setup72 P p q a b) (h4 : (o 4).swap = false)
    (h : ((o 0).negX = (o 2).negX ∧ (o 1).negX ≠ (o 3).negX) ∨
      ((o 0).negX ≠ (o 2).negX ∧ (o 1).negX = (o 3).negX)) :
    oppH P q false = oppV P p false := by
  have F5 := F.toFrame5
  have hW := F.x5_le
  have hH := F.y5_le
  have hx := F.x5_pos
  have hy := F.y5_pos
  simp only [Orient.W, Orient.H, h4, Bool.false_eq_true, ite_false] at hW hH
  have hb := K.hb
  have hL0 : 0 ≤ x5 := by omega
  have hLN : x5 < a - p := by omega
  have hR0 : 0 ≤ a - p - x5 := by omega
  have hRN : a - p - x5 < a - p := by omega
  have hB0 : 0 ≤ y5 := by omega
  have hT0 : 0 ≤ a - q - y5 := by omega
  have sL := fun c (h0 : 0 ≤ c) (h1 : c < a - p) => (sr_sides F S hq A K h4 h0 h1).1
  have sR := fun c (h0 : 0 ≤ c) (h1 : c < a - p) => (sr_sides F S hq A K h4 h0 h1).2.1
  have sB := fun c (h0 : 0 ≤ c) (h1 : c < a - p) => (sr_sides F S hq A K h4 h0 h1).2.2.1
  have sT := fun c (h0 : 0 ≤ c) (h1 : c < a - p) => (sr_sides F S hq A K h4 h0 h1).2.2.2
  generalize (o 0).negX = m1 at sL sR sB sT h
  generalize (o 1).negX = m2 at sL sR sB sT h
  generalize (o 2).negX = m3 at sL sR sB sT h
  generalize (o 3).negX = m4 at sL sR sB sT h
  cases m1 <;> cases m2 <;> cases m3 <;> cases m4 <;> simp at h <;>
    first
    | exact sr_three_core F5 S K hL0 hLN hB0 sL sB
    | exact sr_three_core F5 S K hL0 hLN hT0 sL sT
    | exact sr_three_core F5 S K hR0 hRN hB0 sR sB
    | exact sr_three_core F5 S K hR0 hRN hT0 sR sT

/-- The two terms of a pair of sides at the smaller margin `m = min(r, r')`:
both vanish below `m`, and at `m` their sum is `v` or `2v`. -/
private theorem sr_pair (f : Bool → ℤ → ℤ) (v : ℤ) (hz : ∀ j x, x < 0 → f j x = 0)
    (hv : ∀ j, f j 0 = v) (j j' : Bool) (r r' : ℤ) :
    ∃ m, m ≤ r ∧ m ≤ r' ∧ (m = r ∨ m = r') ∧
      (∀ c, c < m → f j (c - r) + f j' (c - r') = 0) ∧
      (f j (m - r) + f j' (m - r') = v ∨ f j (m - r) + f j' (m - r') = 2 * v) := by
  rcases lt_trichotomy r r' with hr | rfl | hr
  · refine ⟨r, le_rfl, hr.le, Or.inl rfl, fun c hc => ?_, Or.inl ?_⟩
    · rw [hz j (c - r) (by omega), hz j' (c - r') (by omega), add_zero]
    · rw [sub_self, hv, hz j' (r - r') (by omega), add_zero]
  · refine ⟨r, le_rfl, le_rfl, Or.inl rfl, fun c hc => ?_, Or.inr ?_⟩
    · rw [hz j (c - r) (by omega), hz j' (c - r) (by omega), add_zero]
    · rw [sub_self, hv, hv]
      ring
  · refine ⟨r', hr.le, le_rfl, Or.inr rfl, fun c hc => ?_, Or.inl ?_⟩
    · rw [hz j (c - r) (by omega), hz j' (c - r') (by omega), add_zero]
    · rw [sub_self, hv, hz j (r' - r) (by omega), zero_add]

/-- The argument of the second bullet. "the corner terms of left + right and of
bottom + top have the same sum, X_A + X_C + Y_A + Y_C: so t_L + t_R = t_B + t_T
for c < N. Let o be the smaller of o_L, o_R, and o' of o_B, o_T. At c = o < N the
left side is v or 2v, so o' <= o; at c = o' the right side is h or 2h, so
o <= o'. So o = o' and v or 2v equals h or 2h." -/
private theorem sr_two_core (F : Frame5 P p q a b t o x5 y5) (S : OppFull P p q)
    (K : Setup72 P p q a b) {m1 m2 m3 m4 jL jR jB jT : Bool} {oL oR oB oT N : ℤ}
    (hL0 : 0 ≤ oL) (hLN : oL < N) (hR0 : 0 ≤ oR) (hB0 : 0 ≤ oB) (hT0 : 0 ≤ oT)
    (h13 : m1 ≠ m3) (h24 : m2 ≠ m4)
    (sL : ∀ c, 0 ≤ c → c < N → sr_X P p m1 c + sr_Y P q m4 c + sr_X P p jL (c - oL) = a)
    (sR : ∀ c, 0 ≤ c → c < N → sr_X P p m3 c + sr_Y P q m2 c + sr_X P p jR (c - oR) = a)
    (sB : ∀ c, 0 ≤ c → c < N → sr_X P p m2 c + sr_Y P q m1 c + sr_Y P q jB (c - oB) = a)
    (sT : ∀ c, 0 ≤ c → c < N → sr_X P p m4 c + sr_Y P q m3 c + sr_Y P q jT (c - oT) = a) :
    oppH P q false = oppV P p false ∨ oppH P q false = 2 * oppV P p false ∨
      oppV P p false = 2 * oppH P q false := by
  have heq : ∀ c, 0 ≤ c → c < N → sr_X P p jL (c - oL) + sr_X P p jR (c - oR) =
      sr_Y P q jB (c - oB) + sr_Y P q jT (c - oT) := by
    intro c h0 h1
    have l := sL c h0 h1
    have r := sR c h0 h1
    have b' := sB c h0 h1
    have t' := sT c h0 h1
    cases m1 <;> cases m3 <;> cases m2 <;> cases m4 <;>
      first
      | exact absurd rfl h13
      | exact absurd rfl h24
      | omega
  have hv := S.v_pos false
  have hh := S.h_pos false
  obtain ⟨m, hmL, hmR, hm, A0, A1⟩ := sr_pair (sr_X P p) (oppV P p false)
    (fun j x hx => sr_X_zero F j (Or.inl hx)) (sr_X_start K) jL jR oL oR
  obtain ⟨m', hmB, hmT, hm', B0, B1⟩ := sr_pair (sr_Y P q) (oppH P q false)
    (fun j y hy => sr_Y_zero F j (Or.inl hy)) (sr_Y_start K) jB jT oB oT
  have hm0 : 0 ≤ m := by omega
  have hmN : m < N := by omega
  have hm0' : 0 ≤ m' := by omega
  have le1 : m' ≤ m := by
    by_contra hlt
    have e := heq m hm0 hmN
    have z := B0 m (by omega)
    omega
  have le2 : m ≤ m' := by
    by_contra hlt
    have e := heq m' hm0' (by omega)
    have z := A0 m' (by omega)
    omega
  obtain rfl : m = m' := le_antisymm le2 le1
  have e := heq m hm0 hmN
  omega

/-- **`report-A2.md`, 7.2, "Ratios", second bullet:** two and two, equal at
neighbouring corners (`m_1 ≠ m_3` and `m_2 ≠ m_4`), `T_5` wide. The corner terms
of left + right and of bottom + top have the same sum, so
`t_L + t_R = t_B + t_T` for `c < N`; `h = v`, `h = 2v` or `v = 2h`. -/
theorem n72_ratio_two (F : FrameN P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (K : Setup72 P p q a b) (h4 : (o 4).swap = false)
    (h02 : (o 0).negX ≠ (o 2).negX) (h13 : (o 1).negX ≠ (o 3).negX) :
    oppH P q false = oppV P p false ∨ oppH P q false = 2 * oppV P p false ∨
      oppV P p false = 2 * oppH P q false := by
  have hW := F.x5_le
  have hH := F.y5_le
  have hx := F.x5_pos
  have hy := F.y5_pos
  simp only [Orient.W, Orient.H, h4, Bool.false_eq_true, ite_false] at hW hH
  have hb := K.hb
  exact sr_two_core F.toFrame5 S K (oL := x5) (oR := a - p - x5) (oB := y5)
    (oT := a - q - y5) (N := a - p) (by omega) (by omega) (by omega) (by omega) (by omega)
    h02 h13
    (fun c h0 h1 => (sr_sides F S hq A K h4 h0 h1).1)
    (fun c h0 h1 => (sr_sides F S hq A K h4 h0 h1).2.1)
    (fun c h0 h1 => (sr_sides F S hq A K h4 h0 h1).2.2.1)
    (fun c h0 h1 => (sr_sides F S hq A K h4 h0 h1).2.2.2)

/-! ### The four polynomial equations -/

/-- `X_j(z)`: the polynomial of the column counts of `P`, read from `A`
(`j = false`) or from `C` (`j = true`). -/
noncomputable def profX (P : Finset Cell) (p : ℤ) (j : Bool) : ℤ[X] :=
  ∑ c ∈ Finset.range p.toNat, C (colCount P (if j then p - 1 - c else c)) * X ^ c

/-- `Y_j(z)`: the polynomial of the row counts of `P`. -/
noncomputable def profY (P : Finset Cell) (q : ℤ) (j : Bool) : ℤ[X] :=
  ∑ c ∈ Finset.range q.toNat, C (rowCount P (if j then q - 1 - c else c)) * X ^ c

/-- `w = (X_A, X_C, Y_A, Y_C)`. -/
noncomputable def prof72 (P : Finset Cell) (p q : ℤ) : Fin 4 → ℤ[X] :=
  ![profX P p false, profX P p true, profY P q false, profY P q true]

/-- `[s] = 1 + z + ... + z^(s - 1)`. -/
noncomputable def geom (s : ℕ) : ℤ[X] := ∑ c ∈ Finset.range s, X ^ c

/-- `1` if the switch is on, else `0`. -/
noncomputable def ind (j : Bool) : ℤ[X] := if j then 1 else 0

/-- The matrix `M(z)` of `report-A2.md`, 7.2, "Divisibility", for `T_5` wide:
the rows are the column sums read from the left and from the right and the row
sums read from the bottom and from the top; the columns are `X_A`, `X_C`, `Y_A`,
`Y_C`. `m1, ..., m4` are the marks (`true` for `C`), `jL`, `jB` the occupied
corners of `T_5` on the left and on the bottom side of its box, and `j_R = j_L'`,
`j_T = j_B'`. Tested against direct counts by `tools/frame5_check.py`, part 4. -/
noncomputable def M72 (N K oL oR oB oT : ℕ) (m1 m2 m3 m4 jL jB : Bool) :
    Matrix (Fin 4) (Fin 4) ℤ[X] :=
  Matrix.of ![
    ![ind (!m1) + X ^ N * ind m3 + X ^ oL * ind (!jL),
      ind m1 + X ^ N * ind (!m3) + X ^ oL * ind jL,
      ind (!m4) + X ^ K * ind m2,
      ind m4 + X ^ K * ind (!m2)],
    ![ind (!m3) + X ^ N * ind m1 + X ^ oR * ind jL,
      ind m3 + X ^ N * ind (!m1) + X ^ oR * ind (!jL),
      ind (!m2) + X ^ K * ind m4,
      ind m2 + X ^ K * ind (!m4)],
    ![ind (!m2) + X ^ N * ind m4,
      ind m2 + X ^ N * ind (!m4),
      ind (!m1) + X ^ K * ind m3 + X ^ oB * ind (!jB),
      ind m1 + X ^ K * ind (!m3) + X ^ oB * ind jB],
    ![ind (!m4) + X ^ N * ind m2,
      ind m4 + X ^ N * ind (!m2),
      ind (!m3) + X ^ K * ind m1 + X ^ oT * ind jB,
      ind m3 + X ^ K * ind (!m1) + X ^ oT * ind (!jB)]]

/-- A shifted profile: if `u x = f (x - d)` on `[0, L)` and `f` vanishes outside
`[0, n)`, with `0 ≤ d` and `d + n ≤ L`, then the generating polynomial of `u` on
`[0, L)` is `z^d` times that of `f` on `[0, n)`. -/
private theorem sp_shift (f u : ℤ → ℤ) {n L d : ℤ} (hd : 0 ≤ d) (hdn : d + n ≤ L)
    (hf : ∀ x, x < 0 ∨ n ≤ x → f x = 0) (hu : ∀ x : ℤ, 0 ≤ x → x < L → u x = f (x - d)) :
    ∑ x ∈ Finset.range L.toNat, C (u x) * X ^ x =
      X ^ d.toNat * ∑ c ∈ Finset.range n.toNat, C (f c) * X ^ c := by
  ext k
  rw [Polynomial.coeff_X_pow_mul', Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow, Finset.sum_ite_eq,
    Finset.mem_range]
  by_cases h1 : k < L.toNat
  · rw [ite_eq_left h1, hu k (by omega) (by omega)]
    by_cases h2 : d.toNat ≤ k
    · rw [ite_eq_left h2]
      by_cases h3 : k - d.toNat < n.toNat
      · rw [ite_eq_left h3]
        congr 1
        omega
      · rw [ite_eq_right h3]
        exact hf _ (Or.inr (by omega))
    · rw [ite_eq_right h2]
      exact hf _ (Or.inl (by omega))
  · rw [ite_eq_right h1]
    by_cases h2 : d.toNat ≤ k
    · rw [ite_eq_left h2, ite_eq_right (by omega)]
    · rw [ite_eq_right h2]

/-- A tile term that reads the columns of `P` (`X_A` or `X_C`, chosen by `j`)
shifted by `d`. -/
private theorem sp_termX (F : Frame5 P p q a b t o x5 y5) (j : Bool) (u : ℤ → ℤ) {L d : ℤ}
    (hd : 0 ≤ d) (hdn : d + p ≤ L)
    (hu : ∀ x : ℤ, 0 ≤ x → x < L → u x = colCount P (if j then p - 1 - (x - d) else x - d)) :
    ∑ x ∈ Finset.range L.toNat, C (u x) * X ^ x =
      X ^ d.toNat * (ind (!j) * profX P p false + ind j * profX P p true) := by
  have h : ind (!j) * profX P p false + ind j * profX P p true = profX P p j := by
    cases j <;> simp [ind]
  rw [h, profX]
  refine sp_shift (fun c => colCount P (if j then p - 1 - c else c)) u hd hdn ?_ hu
  intro x hx
  cases j
  · exact F.colCount_zero (by simpa using hx)
  · exact F.colCount_zero (by simp only [ite_true]; omega)

/-- A tile term that reads the rows of `P` (`Y_A` or `Y_C`, chosen by `j`)
shifted by `d`. -/
private theorem sp_termY (F : Frame5 P p q a b t o x5 y5) (j : Bool) (u : ℤ → ℤ) {L d : ℤ}
    (hd : 0 ≤ d) (hdn : d + q ≤ L)
    (hu : ∀ x : ℤ, 0 ≤ x → x < L → u x = rowCount P (if j then q - 1 - (x - d) else x - d)) :
    ∑ x ∈ Finset.range L.toNat, C (u x) * X ^ x =
      X ^ d.toNat * (ind (!j) * profY P q false + ind j * profY P q true) := by
  have h : ind (!j) * profY P q false + ind j * profY P q true = profY P q j := by
    cases j <;> simp [ind]
  rw [h, profY]
  refine sp_shift (fun c => rowCount P (if j then q - 1 - c else c)) u hd hdn ?_ hu
  intro x hx
  cases j
  · exact F.rowCount_zero (by simpa using hx)
  · exact F.rowCount_zero (by simp only [ite_true]; omega)


/-- A local column of a wide code is a column of `P`. -/
private theorem sp_colW (c : Orient) (hs : c.swap = false) (z : ℤ) :
    c.colLine p q P z = colCount P (if c.negX then p - 1 - z else z) := by
  simp only [Orient.colLine, hs, Bool.false_eq_true, ↓reduceIte]

/-- A local column of a tall code is a row of `P`. -/
private theorem sp_colT (c : Orient) (hs : c.swap = true) (z : ℤ) :
    c.colLine p q P z = rowCount P (if c.negY then q - 1 - z else z) := by
  simp only [Orient.colLine, hs, ↓reduceIte]

/-- A local row of a wide code is a row of `P`. -/
private theorem sp_rowW (c : Orient) (hs : c.swap = false) (z : ℤ) :
    c.rowLine p q P z = rowCount P (if c.negY then q - 1 - z else z) := by
  simp only [Orient.rowLine, hs, Bool.false_eq_true, ↓reduceIte]

/-- A local row of a tall code is a column of `P`. -/
private theorem sp_rowT (c : Orient) (hs : c.swap = true) (z : ℤ) :
    c.rowLine p q P z = colCount P (if c.negX then p - 1 - z else z) := by
  simp only [Orient.rowLine, hs, ↓reduceIte]

/-- A line read forwards from the shift `d`. -/
private theorem sp_fwd (g : ℤ → ℤ) (j : Bool) {n y x d : ℤ} (h : y = x - d) :
    g (if j then n - 1 - y else y) = g (if j then n - 1 - (x - d) else x - d) := by
  rw [h]

/-- A line read backwards: the far end `d + n - 1`, read from the other corner. -/
private theorem sp_rev (g : ℤ → ℤ) (j : Bool) {n y x d : ℤ} (h : y = d + n - 1 - x) :
    g (if j then n - 1 - y else y) = g (if !j then n - 1 - (x - d) else x - d) := by
  subst h
  cases j
  · simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    congr 1
    ring
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    congr 1
    ring

/-- **`report-A2.md`, 7.2, "Divisibility", the four equations.** All columns,
columns from the right, rows, rows from the top, by (2) (`Frame5.col_sum`,
`Frame5.row_sum`), as one equation `M(z) w = s [s] (1, 1, 1, 1)`. With
`N = s - p`, `K = s - q`: `T_3` is read from column `N`, `T_2` from column `K`,
`T_4` from row `N`, `T_3` from row `K`, and `T_5` from its margins. -/
theorem n72_poly (F : FrameN P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (K : Setup72 P p q a b) (h4 : (o 4).swap = false) :
    (M72 (a - p).toNat (a - q).toNat x5.toNat (a - p - x5).toNat y5.toNat (a - q - y5).toNat
      (o 0).negX (o 1).negX (o 2).negX (o 3).negX (o 4).negX (o 4).negY).mulVec (prof72 P p q) =
      fun _ => C a * geom a.toNat := by
  have _ := hq -- not needed: the four equations hold for any `p`, `q`
  have F5 := F.toFrame5
  rw [K.hb] at F5
  have m0 := S.toOpposite.mark F.toFrame5 (i := 0) (by decide)
  have m1 := S.toOpposite.mark F.toFrame5 (i := 1) (by decide)
  have m2 := S.toOpposite.mark F.toFrame5 (i := 2) (by decide)
  have m3 := S.toOpposite.mark F.toFrame5 (i := 3) (by decide)
  have hp0 : p ≤ a - 1 := by simpa [Orient.W, A.w0] using F5.W_le (i := 0) (by decide)
  have hq1 : q ≤ a - 1 := by simpa [Orient.W, A.t1] using F5.W_le (i := 1) (by decide)
  have hx5 := F.x5_pos
  have hy5 := F.y5_pos
  have hx5' : x5 + p ≤ a - 1 := by simpa [Orient.W, h4] using F.x5_le
  have hy5' : y5 + q ≤ a - 1 := by
    have := F.y5_le
    rw [K.hb] at this
    simpa [Orient.H, h4] using this
  -- Row 0: all columns, read from the left.
  have r0 : ∑ x ∈ Finset.range a.toNat,
      C ((o 0).colLine p q P x + (o 1).colLine p q P (a - 1 - x) +
        (o 2).colLine p q P (a - 1 - x) + (o 3).colLine p q P x +
        (o 4).colLine p q P (x - x5)) * X ^ x = C a * geom a.toNat := by
    rw [geom, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.mem_range.1 hx
    rw [F5.col_sum (by omega) (by omega)]
  have e00 : ∑ x ∈ Finset.range a.toNat, C ((o 0).colLine p q P x) * X ^ x =
      X ^ (0 : ℤ).toNat * (ind (!(o 0).negX) * profX P p false + ind (o 0).negX * profX P p true) :=
    sp_termX F5 (o 0).negX (fun z => (o 0).colLine p q P z) le_rfl (by omega)
      (fun x _ _ => by
        rw [sp_colW _ A.w0]
        exact sp_fwd _ _ (by ring))
  have e01 : ∑ x ∈ Finset.range a.toNat, C ((o 1).colLine p q P (a - 1 - x)) * X ^ x =
      X ^ (a - q).toNat * (ind (!!(o 1).negX) * profY P q false +
        ind (!(o 1).negX) * profY P q true) :=
    sp_termY F5 (!(o 1).negX) (fun z => (o 1).colLine p q P (a - 1 - z)) (by omega) (by omega)
      (fun x _ _ => by
        rw [sp_colT _ A.t1, m1]
        exact sp_rev _ _ (by ring))
  have e02 : ∑ x ∈ Finset.range a.toNat, C ((o 2).colLine p q P (a - 1 - x)) * X ^ x =
      X ^ (a - p).toNat * (ind (!!(o 2).negX) * profX P p false +
        ind (!(o 2).negX) * profX P p true) :=
    sp_termX F5 (!(o 2).negX) (fun z => (o 2).colLine p q P (a - 1 - z)) (by omega) (by omega)
      (fun x _ _ => by
        rw [sp_colW _ A.w2]
        exact sp_rev _ _ (by ring))
  have e03 : ∑ x ∈ Finset.range a.toNat, C ((o 3).colLine p q P x) * X ^ x =
      X ^ (0 : ℤ).toNat * (ind (!(o 3).negX) * profY P q false + ind (o 3).negX * profY P q true) :=
    sp_termY F5 (o 3).negX (fun z => (o 3).colLine p q P z) le_rfl (by omega)
      (fun x _ _ => by
        rw [sp_colT _ A.t3, m3]
        exact sp_fwd _ _ (by ring))
  have e04 : ∑ x ∈ Finset.range a.toNat, C ((o 4).colLine p q P (x - x5)) * X ^ x =
      X ^ x5.toNat * (ind (!(o 4).negX) * profX P p false + ind (o 4).negX * profX P p true) :=
    sp_termX F5 (o 4).negX (fun z => (o 4).colLine p q P (z - x5)) (by omega) (by omega)
      (fun x _ _ => by
        rw [sp_colW _ h4])
  have row0 : (M72 (a - p).toNat (a - q).toNat x5.toNat (a - p - x5).toNat y5.toNat
      (a - q - y5).toNat (o 0).negX (o 1).negX (o 2).negX (o 3).negX (o 4).negX
      (o 4).negY).mulVec (prof72 P p q) 0 = C a * geom a.toNat := by
    rw [← r0]
    simp only [C_add, add_mul, Finset.sum_add_distrib]
    rw [e00, e01, e02, e03, e04]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, M72, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Matrix.cons_val_succ, prof72, Int.toNat_zero, pow_zero, one_mul, Bool.not_not]
    ring
  -- Row 1: all columns, read from the right.
  have r1 : ∑ x ∈ Finset.range a.toNat,
      C ((o 0).colLine p q P (a - 1 - x) + (o 1).colLine p q P (a - 1 - (a - 1 - x)) +
        (o 2).colLine p q P (a - 1 - (a - 1 - x)) + (o 3).colLine p q P (a - 1 - x) +
        (o 4).colLine p q P (a - 1 - x - x5)) * X ^ x = C a * geom a.toNat := by
    rw [geom, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.mem_range.1 hx
    rw [F5.col_sum (by omega) (by omega)]
  have e10 : ∑ x ∈ Finset.range a.toNat, C ((o 0).colLine p q P (a - 1 - x)) * X ^ x =
      X ^ (a - p).toNat * (ind (!!(o 0).negX) * profX P p false +
        ind (!(o 0).negX) * profX P p true) :=
    sp_termX F5 (!(o 0).negX) (fun z => (o 0).colLine p q P (a - 1 - z)) (by omega) (by omega)
      (fun x _ _ => by
        rw [sp_colW _ A.w0]
        exact sp_rev _ _ (by ring))
  have e11 : ∑ x ∈ Finset.range a.toNat,
      C ((o 1).colLine p q P (a - 1 - (a - 1 - x))) * X ^ x =
      X ^ (0 : ℤ).toNat * (ind (!(o 1).negX) * profY P q false + ind (o 1).negX * profY P q true) :=
    sp_termY F5 (o 1).negX (fun z => (o 1).colLine p q P (a - 1 - (a - 1 - z))) le_rfl
      (by omega)
      (fun x _ _ => by
        rw [sp_colT _ A.t1, m1]
        exact sp_fwd _ _ (by ring))
  have e12 : ∑ x ∈ Finset.range a.toNat,
      C ((o 2).colLine p q P (a - 1 - (a - 1 - x))) * X ^ x =
      X ^ (0 : ℤ).toNat * (ind (!(o 2).negX) * profX P p false + ind (o 2).negX * profX P p true) :=
    sp_termX F5 (o 2).negX (fun z => (o 2).colLine p q P (a - 1 - (a - 1 - z))) le_rfl
      (by omega)
      (fun x _ _ => by
        rw [sp_colW _ A.w2]
        exact sp_fwd _ _ (by ring))
  have e13 : ∑ x ∈ Finset.range a.toNat, C ((o 3).colLine p q P (a - 1 - x)) * X ^ x =
      X ^ (a - q).toNat * (ind (!!(o 3).negX) * profY P q false +
        ind (!(o 3).negX) * profY P q true) :=
    sp_termY F5 (!(o 3).negX) (fun z => (o 3).colLine p q P (a - 1 - z)) (by omega) (by omega)
      (fun x _ _ => by
        rw [sp_colT _ A.t3, m3]
        exact sp_rev _ _ (by ring))
  have e14 : ∑ x ∈ Finset.range a.toNat, C ((o 4).colLine p q P (a - 1 - x - x5)) * X ^ x =
      X ^ (a - p - x5).toNat * (ind (!!(o 4).negX) * profX P p false +
        ind (!(o 4).negX) * profX P p true) :=
    sp_termX F5 (!(o 4).negX) (fun z => (o 4).colLine p q P (a - 1 - z - x5)) (by omega)
      (by omega)
      (fun x _ _ => by
        rw [sp_colW _ h4]
        exact sp_rev _ _ (by ring))
  have row1 : (M72 (a - p).toNat (a - q).toNat x5.toNat (a - p - x5).toNat y5.toNat
      (a - q - y5).toNat (o 0).negX (o 1).negX (o 2).negX (o 3).negX (o 4).negX
      (o 4).negY).mulVec (prof72 P p q) 1 = C a * geom a.toNat := by
    rw [← r1]
    simp only [C_add, add_mul, Finset.sum_add_distrib]
    rw [e10, e11, e12, e13, e14]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, M72, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Matrix.cons_val_succ, prof72, Int.toNat_zero, pow_zero, one_mul, Bool.not_not]
    ring
  -- Row 2: all rows, read from the bottom.
  have r2 : ∑ x ∈ Finset.range a.toNat,
      C ((o 0).rowLine p q P x + (o 1).rowLine p q P x + (o 2).rowLine p q P (a - 1 - x) +
        (o 3).rowLine p q P (a - 1 - x) + (o 4).rowLine p q P (x - y5)) * X ^ x =
      C a * geom a.toNat := by
    rw [geom, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.mem_range.1 hx
    rw [F5.row_sum (by omega) (by omega)]
  have e20 : ∑ x ∈ Finset.range a.toNat, C ((o 0).rowLine p q P x) * X ^ x =
      X ^ (0 : ℤ).toNat * (ind (!(o 0).negX) * profY P q false + ind (o 0).negX * profY P q true) :=
    sp_termY F5 (o 0).negX (fun z => (o 0).rowLine p q P z) le_rfl (by omega)
      (fun x _ _ => by
        rw [sp_rowW _ A.w0, m0]
        exact sp_fwd _ _ (by ring))
  have e21 : ∑ x ∈ Finset.range a.toNat, C ((o 1).rowLine p q P x) * X ^ x =
      X ^ (0 : ℤ).toNat * (ind (!(o 1).negX) * profX P p false + ind (o 1).negX * profX P p true) :=
    sp_termX F5 (o 1).negX (fun z => (o 1).rowLine p q P z) le_rfl (by omega)
      (fun x _ _ => by
        rw [sp_rowT _ A.t1]
        exact sp_fwd _ _ (by ring))
  have e22 : ∑ x ∈ Finset.range a.toNat, C ((o 2).rowLine p q P (a - 1 - x)) * X ^ x =
      X ^ (a - q).toNat * (ind (!!(o 2).negX) * profY P q false +
        ind (!(o 2).negX) * profY P q true) :=
    sp_termY F5 (!(o 2).negX) (fun z => (o 2).rowLine p q P (a - 1 - z)) (by omega) (by omega)
      (fun x _ _ => by
        rw [sp_rowW _ A.w2, m2]
        exact sp_rev _ _ (by ring))
  have e23 : ∑ x ∈ Finset.range a.toNat, C ((o 3).rowLine p q P (a - 1 - x)) * X ^ x =
      X ^ (a - p).toNat * (ind (!!(o 3).negX) * profX P p false +
        ind (!(o 3).negX) * profX P p true) :=
    sp_termX F5 (!(o 3).negX) (fun z => (o 3).rowLine p q P (a - 1 - z)) (by omega) (by omega)
      (fun x _ _ => by
        rw [sp_rowT _ A.t3]
        exact sp_rev _ _ (by ring))
  have e24 : ∑ x ∈ Finset.range a.toNat, C ((o 4).rowLine p q P (x - y5)) * X ^ x =
      X ^ y5.toNat * (ind (!(o 4).negY) * profY P q false + ind (o 4).negY * profY P q true) :=
    sp_termY F5 (o 4).negY (fun z => (o 4).rowLine p q P (z - y5)) (by omega) (by omega)
      (fun x _ _ => by
        rw [sp_rowW _ h4])
  have row2 : (M72 (a - p).toNat (a - q).toNat x5.toNat (a - p - x5).toNat y5.toNat
      (a - q - y5).toNat (o 0).negX (o 1).negX (o 2).negX (o 3).negX (o 4).negX
      (o 4).negY).mulVec (prof72 P p q) 2 = C a * geom a.toNat := by
    rw [← r2]
    simp only [C_add, add_mul, Finset.sum_add_distrib]
    rw [e20, e21, e22, e23, e24]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, M72, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Matrix.cons_val_succ, prof72, Int.toNat_zero, pow_zero, one_mul, Bool.not_not]
    ring
  -- Row 3: all rows, read from the top.
  have r3 : ∑ x ∈ Finset.range a.toNat,
      C ((o 0).rowLine p q P (a - 1 - x) + (o 1).rowLine p q P (a - 1 - x) +
        (o 2).rowLine p q P (a - 1 - (a - 1 - x)) + (o 3).rowLine p q P (a - 1 - (a - 1 - x)) +
        (o 4).rowLine p q P (a - 1 - x - y5)) * X ^ x = C a * geom a.toNat := by
    rw [geom, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.mem_range.1 hx
    rw [F5.row_sum (by omega) (by omega)]
  have e30 : ∑ x ∈ Finset.range a.toNat, C ((o 0).rowLine p q P (a - 1 - x)) * X ^ x =
      X ^ (a - q).toNat * (ind (!!(o 0).negX) * profY P q false +
        ind (!(o 0).negX) * profY P q true) :=
    sp_termY F5 (!(o 0).negX) (fun z => (o 0).rowLine p q P (a - 1 - z)) (by omega) (by omega)
      (fun x _ _ => by
        rw [sp_rowW _ A.w0, m0]
        exact sp_rev _ _ (by ring))
  have e31 : ∑ x ∈ Finset.range a.toNat, C ((o 1).rowLine p q P (a - 1 - x)) * X ^ x =
      X ^ (a - p).toNat * (ind (!!(o 1).negX) * profX P p false +
        ind (!(o 1).negX) * profX P p true) :=
    sp_termX F5 (!(o 1).negX) (fun z => (o 1).rowLine p q P (a - 1 - z)) (by omega) (by omega)
      (fun x _ _ => by
        rw [sp_rowT _ A.t1]
        exact sp_rev _ _ (by ring))
  have e32 : ∑ x ∈ Finset.range a.toNat,
      C ((o 2).rowLine p q P (a - 1 - (a - 1 - x))) * X ^ x =
      X ^ (0 : ℤ).toNat * (ind (!(o 2).negX) * profY P q false + ind (o 2).negX * profY P q true) :=
    sp_termY F5 (o 2).negX (fun z => (o 2).rowLine p q P (a - 1 - (a - 1 - z))) le_rfl
      (by omega)
      (fun x _ _ => by
        rw [sp_rowW _ A.w2, m2]
        exact sp_fwd _ _ (by ring))
  have e33 : ∑ x ∈ Finset.range a.toNat,
      C ((o 3).rowLine p q P (a - 1 - (a - 1 - x))) * X ^ x =
      X ^ (0 : ℤ).toNat * (ind (!(o 3).negX) * profX P p false + ind (o 3).negX * profX P p true) :=
    sp_termX F5 (o 3).negX (fun z => (o 3).rowLine p q P (a - 1 - (a - 1 - z))) le_rfl
      (by omega)
      (fun x _ _ => by
        rw [sp_rowT _ A.t3]
        exact sp_fwd _ _ (by ring))
  have e34 : ∑ x ∈ Finset.range a.toNat, C ((o 4).rowLine p q P (a - 1 - x - y5)) * X ^ x =
      X ^ (a - q - y5).toNat * (ind (!!(o 4).negY) * profY P q false +
        ind (!(o 4).negY) * profY P q true) :=
    sp_termY F5 (!(o 4).negY) (fun z => (o 4).rowLine p q P (a - 1 - z - y5)) (by omega)
      (by omega)
      (fun x _ _ => by
        rw [sp_rowW _ h4]
        exact sp_rev _ _ (by ring))
  have row3 : (M72 (a - p).toNat (a - q).toNat x5.toNat (a - p - x5).toNat y5.toNat
      (a - q - y5).toNat (o 0).negX (o 1).negX (o 2).negX (o 3).negX (o 4).negX
      (o 4).negY).mulVec (prof72 P p q) 3 = C a * geom a.toNat := by
    rw [← r3]
    simp only [C_add, add_mul, Finset.sum_add_distrib]
    rw [e30, e31, e32, e33, e34]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, M72, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Matrix.cons_val_succ, prof72, Int.toNat_zero, pow_zero, one_mul, Bool.not_not]
    ring
  funext i
  fin_cases i
  exacts [row0, row1, row2, row3]


/-- The value of a switch at `z = 1`: `ind j` evaluated at `1`. -/
private def sp_b (j : Bool) : ℤ := if j then 1 else 0

private theorem sp_eval_ind (j : Bool) : (ind j).eval 1 = sp_b j := by
  cases j <;> simp [ind, sp_b]

/-- `M(1)`: the integer matrix of the values of `M72` at `z = 1`; it depends only
on the six switches. -/
private def sp_M1 (m1 m2 m3 m4 jL jB : Bool) : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of ![
    ![sp_b (!m1) + sp_b m3 + sp_b (!jL), sp_b m1 + sp_b (!m3) + sp_b jL,
      sp_b (!m4) + sp_b m2, sp_b m4 + sp_b (!m2)],
    ![sp_b (!m3) + sp_b m1 + sp_b jL, sp_b m3 + sp_b (!m1) + sp_b (!jL),
      sp_b (!m2) + sp_b m4, sp_b m2 + sp_b (!m4)],
    ![sp_b (!m2) + sp_b m4, sp_b m2 + sp_b (!m4),
      sp_b (!m1) + sp_b m3 + sp_b (!jB), sp_b m1 + sp_b (!m3) + sp_b jB],
    ![sp_b (!m4) + sp_b m2, sp_b m4 + sp_b (!m2),
      sp_b (!m3) + sp_b m1 + sp_b jB, sp_b m3 + sp_b (!m1) + sp_b (!jB)]]

/-- `det M(1)` through `det_eval_one`. -/
private theorem sp_det_M1 (N K oL oR oB oT : ℕ) (m1 m2 m3 m4 jL jB : Bool) :
    (M72 N K oL oR oB oT m1 m2 m3 m4 jL jB).det.eval 1 = (sp_M1 m1 m2 m3 m4 jL jB).det := by
  rw [det_eval_one]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M72, sp_M1, sp_eval_ind]

/-- (15): `det M(1) = 5 ((σ_1 - σ_3 + τ)(σ_1 - σ_3 + ω) + (σ_2 - σ_4)^2)` with
`σ_i = 1 - 2 [m_i = C]`, `τ = 1 - 2 [j_L = C]`, `ω = 1 - 2 [j_B = C]`, checked
for the 64 choices of switches. -/
private theorem sp_det_formula (m1 m2 m3 m4 jL jB : Bool) :
    (sp_M1 m1 m2 m3 m4 jL jB).det =
      5 * ((1 - 2 * sp_b m1 - (1 - 2 * sp_b m3) + (1 - 2 * sp_b jL)) *
        (1 - 2 * sp_b m1 - (1 - 2 * sp_b m3) + (1 - 2 * sp_b jB)) +
        (1 - 2 * sp_b m2 - (1 - 2 * sp_b m4)) ^ 2) := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [Matrix.det_fin_three]
  cases m1 <;> cases m2 <;> cases m3 <;> cases m4 <;> cases jL <;> cases jB <;> decide

/-- **`report-A2.md`, 7.2, (15):** `det M(1)` is odd. By `det_eval_one` this is
the determinant of an integer matrix that depends only on the six switches. -/
theorem n72_det_odd (N K oL oR oB oT : ℕ) (m1 m2 m3 m4 jL jB : Bool) :
    ¬ ((2 : ℕ) : ℤ) ∣ (M72 N K oL oR oB oT m1 m2 m3 m4 jL jB).det.eval 1 := by
  rw [sp_det_M1, sp_det_formula]
  cases m1 <;> cases m2 <;> cases m3 <;> cases m4 <;> cases jL <;> cases jB <;> decide

/-- **`report-A2.md`, 7.2, (15):** in the case "two and two, neighbouring"
`det M(1)` is 25, 35 or 65 and not divisible by 3. -/
theorem n72_det_three (N K oL oR oB oT : ℕ) (m1 m2 m3 m4 jL jB : Bool) (h13 : m1 ≠ m3)
    (h24 : m2 ≠ m4) :
    ¬ ((3 : ℕ) : ℤ) ∣ (M72 N K oL oR oB oT m1 m2 m3 m4 jL jB).det.eval 1 := by
  rw [sp_det_M1, sp_det_formula]
  revert h13 h24
  cases m1 <;> cases m2 <;> cases m3 <;> cases m4 <;> cases jL <;> cases jB <;> decide

/-- The coefficient of `z^0` in `X_A(z)` is `v_A`. -/
theorem profX_coeff_zero (P : Finset Cell) {p : ℤ} (hp : 1 ≤ p) :
    (profX P p false).coeff 0 = oppV P p false := by
  have h0 : 0 ∈ Finset.range p.toNat := Finset.mem_range.2 (by omega)
  simp only [profX, oppV, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single_of_mem 0 h0]
  · simp
  · intro c _ hc
    simp [Ne.symm hc]

/-- The coefficient of `z^0` in `Y_A(z)` is `h_A`. -/
theorem profY_coeff_zero (P : Finset Cell) {q : ℤ} (hq : 1 ≤ q) :
    (profY P q false).coeff 0 = oppH P q false := by
  have h0 : 0 ∈ Finset.range q.toNat := Finset.mem_range.2 (by omega)
  simp only [profY, oppH, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single_of_mem 0 h0]
  · simp
  · intro c _ hc
    simp [Ne.symm hc]

/-- **`report-A2.md`, 7.2, "Divisibility".** If the prime `l` does not divide
`det M(1)`, every power of `l` that divides `s` divides `v = X_A(0)` and
`h = Y_A(0)` (`pow_dvd_coeff_of_mulVec`). -/
theorem n72_pow_dvd (F : FrameN P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (K : Setup72 P p q a b) (h4 : (o 4).swap = false) (l : ℕ) [Fact l.Prime]
    (hdet : ¬ (l : ℤ) ∣ (M72 (a - p).toNat (a - q).toNat x5.toNat (a - p - x5).toNat y5.toNat
      (a - q - y5).toNat (o 0).negX (o 1).negX (o 2).negX (o 3).negX (o 4).negX
      (o 4).negY).det.eval 1)
    (k : ℕ) (hk : (l : ℤ) ^ k ∣ a) :
    (l : ℤ) ^ k ∣ oppV P p false ∧ (l : ℤ) ^ k ∣ oppH P q false := by
  obtain ⟨s', hs'⟩ := hk
  have hpoly := n72_poly F S hq A K h4
  have key := pow_dvd_coeff_of_mulVec _ l hdet k (prof72 P p q)
    (fun _ => C s' * geom a.toNat) (by
      rw [hpoly]
      funext i
      rw [← mul_assoc, ← C_mul, ← hs'])
  have hp := F.two_le_p
  have hq' := F.two_le_q
  refine ⟨?_, ?_⟩
  · have h := key 0 0
    rwa [show prof72 P p q 0 = profX P p false from rfl, profX_coeff_zero P (by omega)] at h
  · have h := key 2 0
    rwa [show prof72 P p q 2 = profY P q false from rfl, profY_coeff_zero P (by omega)] at h

/-- If every power of `l` that divides `s = l v` divides `v ≥ 1`, then all
powers of `l` divide `v`. -/
theorem no_pow_tower {l : ℕ} (hl : 2 ≤ l) {s v : ℤ} (hv : 1 ≤ v) (hs : s = l * v)
    (h : ∀ k : ℕ, (l : ℤ) ^ k ∣ s → (l : ℤ) ^ k ∣ v) : False := by
  have hall : ∀ k : ℕ, (l : ℤ) ^ k ∣ v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      apply h
      have e : (l : ℤ) ^ (k + 1) = l * l ^ k := by ring
      rw [hs, e]
      exact mul_dvd_mul_left _ ih
  have h1 := Int.le_of_dvd (by omega) (hall v.toNat)
  have h2 : v.toNat < l ^ v.toNat := Nat.lt_pow_self hl
  have h3 : ((v.toNat : ℕ) : ℤ) < (l : ℤ) ^ v.toNat := by exact_mod_cast h2
  have h4 : ((v.toNat : ℕ) : ℤ) = v := Int.toNat_of_nonneg (by omega)
  omega

/-- `report-A2.md`, 7.2, "Divisibility", first bullet: `h = v`. Then `s = 2v`,
and `det M(1)` is odd. -/
theorem n72_h_eq_v (F : FrameN P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (K : Setup72 P p q a b) (h4 : (o 4).swap = false)
    (hhv : oppH P q false = oppV P p false) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine no_pow_tower (l := 2) le_rfl (S.v_pos false) (s := a) ?_ ?_
  · rw [K.ha, hhv]
    push_cast
    ring
  · intro k hk
    exact (n72_pow_dvd F S hq A K h4 2 (n72_det_odd _ _ _ _ _ _ _ _ _ _ _ _) k hk).1

/-- `report-A2.md`, 7.2, "Divisibility", second bullet, `h = 2v`: `s = 3v`, and
`det M(1)` is not divisible by 3. -/
theorem n72_h_2v (F : FrameN P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (K : Setup72 P p q a b) (h4 : (o 4).swap = false)
    (h02 : (o 0).negX ≠ (o 2).negX) (h13 : (o 1).negX ≠ (o 3).negX)
    (hhv : oppH P q false = 2 * oppV P p false) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine no_pow_tower (l := 3) (by norm_num) (S.v_pos false) (s := a) ?_ ?_
  · rw [K.ha, hhv]
    push_cast
    ring
  · intro k hk
    exact (n72_pow_dvd F S hq A K h4 3 (n72_det_three _ _ _ _ _ _ _ _ _ _ _ _ h02 h13) k hk).1

/-- `report-A2.md`, 7.2, "Divisibility", second bullet, `v = 2h`: `s = 3h`. -/
theorem n72_v_2h (F : FrameN P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (K : Setup72 P p q a b) (h4 : (o 4).swap = false)
    (h02 : (o 0).negX ≠ (o 2).negX) (h13 : (o 1).negX ≠ (o 3).negX)
    (hhv : oppV P p false = 2 * oppH P q false) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine no_pow_tower (l := 3) (by norm_num) (S.h_pos false) (s := a) ?_ ?_
  · rw [K.ha, hhv]
    push_cast
    ring
  · intro k hk
    exact (n72_pow_dvd F S hq A K h4 3 (n72_det_three _ _ _ _ _ _ _ _ _ _ _ _ h02 h13) k hk).2

/-- `report-A2.md`, 7.2, with `T_5` wide. -/
theorem n72_wide (F : FrameN P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (h4 : (o 4).swap = false) : False := by
  have K := n72_setup F S hq A
  by_cases h02 : (o 0).negX = (o 2).negX
  · by_cases h13 : (o 1).negX = (o 3).negX
    · exact n72_period F S hq A h02 h13
    · exact n72_h_eq_v F S hq A K h4 (n72_ratio_three F S hq A K h4 (Or.inl ⟨h02, h13⟩))
  · by_cases h13 : (o 1).negX = (o 3).negX
    · exact n72_h_eq_v F S hq A K h4 (n72_ratio_three F S hq A K h4 (Or.inr ⟨h02, h13⟩))
    · rcases n72_ratio_two F S hq A K h4 h02 h13 with h | h | h
      · exact n72_h_eq_v F S hq A K h4 h
      · exact n72_h_2v F S hq A K h4 h02 h13 h
      · exact n72_v_2h F S hq A K h4 h02 h13 h

/-- **`report-A2.md`, 7.2.** "The frame is invariant under a quarter turn of R,
so let T_5 be wide": the quarter turn is `FrameN.transpose` followed by
`FrameN.flipX`; it keeps the normal form of 7.1 and exchanges wide and tall for
`T_5`. -/
theorem n72 (F : FrameN P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p) (A : Alt o) :
    False := by
  cases h4 : (o 4).swap
  · exact n72_wide F S hq A h4
  · obtain ⟨t', F'⟩ := F.transpose
    obtain ⟨t'', F''⟩ := F'.flipX
    exact n72_wide F'' S hq ⟨by simp [A.t3], by simp [A.w0], by simp [A.t1], by simp [A.w2]⟩
      (by simp [h4])

/-- **`report-A2.md`, 7.2.** Pattern N does not occur with two opposite occupied
corners. -/
theorem opp_N (F : FrameN P p q a b t o x5 y5) (S : Opposite P p q) (hpq : q ≤ p) : False := by
  have S' := S.full F.toFrame5
  obtain ⟨hne, h02, h13, h01⟩ := opp_alt F.toFrame5 S' F.y5_le F.x5_pos F.x5_le
  have hq : q < p := by omega
  cases h0 : (o 0).swap
  · exact n72 F S' hq (Alt.of h0 h02 h13 h01)
  · obtain ⟨t', F'⟩ := F.flipX
    exact n72 F' S' hq (Alt.flip h0 h02 h13 h01 _)

end PolyominoOddOrder
