module

public import PolyominoOddOrder.OppositeN

/-!
# Case (I), two opposite occupied corners, pattern O (`OppositeO.lean`)

Blueprint unit C8 (third increment). `report-A2.md`, section 7.3. The setting is
that of `OppositeN.lean`: `OppFull P p q`, `q < p`, and the normal form `Alt o`
of 7.1 (`T_1`, `T_3` wide, `T_2`, `T_4` tall), reached in pattern O by the
reflection of `R a b` in its vertical midline.

| report | Lean |
|---|---|
| (1) with the runs of the marks, before (14) | `o73_sides` |
| case (a) / (b) / (c) | `m_1 = m_3`, `m_2 ≠ m_4` / `m_2 = m_4`, `m_1 ≠ m_3` / `m_1 ≠ m_3`, `m_2 ≠ m_4`, as equations between `(o i).negX` |
| `T_5` wide: `K` at the lower left / right of `box(T_5)` | `(o 4).negX = (o 4).negY` / `≠`; `K = C` iff `(o 4).negY = true`; `mu = h_K` (`o73_mu_wide`) |
| `T_5` tall: `K` at the lower left / right | `(o 4).negX = (o 4).negY` / `≠`; `K = C` iff `(o 4).negX = true`; `mu = v_K` (`o73_mu_tall`) |
| (16) | `o73_16` |
| (17), (19) | in `o73_wide_left`, `o73_tall_right` |
| "Let m_1 = A, m_3 = C (names)" | the half turn of `P`: `FrameO.flipPX`, `FrameO.flipPY`, `Opposite.turnP` (`o73_wide_c`) |

The steps of 7.3 that are arithmetic on (1) are proved here (`o73_wide_a`,
`o73_wide_b`, `o73_tall_b`, `o73_tall_a`); the open nodes are the cell and line
arguments.

Entry statement (binding): `opp_O`.

Source: `theoretician/report-A2.md` (goals lab, commit `076d663`), section 7.3.
-/

@[expose] public section

namespace PolyominoOddOrder

open Orient (cornerP)

variable {P : Finset Cell} {p q a b : ℤ} {t : Fin 5 → Finset Cell} {o : Fin 5 → Orient}
  {x5 y5 : ℤ}

/-- (1) in pattern O with the boxes of 7.1, in the runs of the marks: the four
equations behind (14). -/
theorem o73_sides (F : FrameO P p q a b t o x5 y5) (S : OppFull P p q) (A : Alt o) :
    oppH P q (o 0).negX + (o 4).rowLine p q P 0 + oppV P p (o 1).negX = a ∧
      oppH P q (o 2).negX + oppV P p (o 3).negX = a ∧
      oppV P p (o 0).negX + oppH P q (o 3).negX = b ∧
      oppH P q (o 1).negX + oppV P p (o 2).negX = b := by
  have hb := F.side_bottom
  have ht := F.side_top
  have hl := F.side_left
  have hr := F.side_right
  rw [S.toOpposite.hrun F.toFrame5 (i := 0) (by decide),
    S.toOpposite.hrun F.toFrame5 (i := 1) (by decide), A.w0, A.t1] at hb
  rw [S.toOpposite.hrun F.toFrame5 (i := 2) (by decide),
    S.toOpposite.hrun F.toFrame5 (i := 3) (by decide), A.w2, A.t3] at ht
  rw [S.toOpposite.vrun F.toFrame5 (i := 0) (by decide),
    S.toOpposite.vrun F.toFrame5 (i := 3) (by decide), A.w0, A.t3] at hl
  rw [S.toOpposite.vrun F.toFrame5 (i := 1) (by decide),
    S.toOpposite.vrun F.toFrame5 (i := 2) (by decide), A.t1, A.w2] at hr
  exact ⟨by simpa using hb, by simpa using ht, by simpa using hl, by simpa using hr⟩

/-- `mu = h_K` if `T_5` is wide; `K = C` iff `(o 4).negY`. -/
theorem o73_mu_wide (h4 : (o 4).swap = false) :
    (o 4).rowLine p q P 0 = oppH P q (o 4).negY := by
  simp [Orient.hrun_eq, h4, oppH]

/-- `mu = v_K` if `T_5` is tall; `K = C` iff `(o 4).negX`. -/
theorem o73_mu_tall (h4 : (o 4).swap = true) :
    (o 4).rowLine p q P 0 = oppV P p (o 4).negX := by
  simp [Orient.hrun_eq, h4, oppV]

/-- `T_1` contains `(p - 1, q - 1)`: "T_1 contains (p-1, q-1)" (`report-A2.md`,
7.3), the corner of `box(T_1)` opposite to its mark. -/
private theorem oa7_far0 (F : FrameO P p q a b t o x5 y5) (S : OppFull P p q) (A : Alt o) :
    ((p - 1, q - 1) : Cell) ∈ t 0 := by
  have h := S.toOpposite.far_mem F.toFrame5 (i := 0) (by decide)
  have hW0 : (o 0).W p q = p := by simp [Orient.W, A.w0]
  have hH0 : (o 0).H p q = q := by simp [Orient.H, A.w0]
  rw [hW0, hH0] at h
  exact (F.toFrame5.mem0 _).2 h

/-- The top row of a box holds a cell of `P`, whatever the code; for `q < p`
its local row is at least `q - 1` (`H_5 ≥ q` in `report-A2.md`, 7.3). -/
private theorem oa7_fwd_up (F : Frame5 P p q a b t o x5 y5) (hq : q < p) (c : Orient) :
    ∃ d ∈ P, q - 1 ≤ (c.fwd p q d).2 := by
  obtain ⟨y, hl⟩ := F.left
  obtain ⟨y', hr⟩ := F.right
  obtain ⟨x, hb⟩ := F.bottom
  obtain ⟨x', ht⟩ := F.top
  rcases c with ⟨_ | _, _ | _, _ | _⟩
  · exact ⟨_, ht, by simp [Orient.fwd]⟩
  · exact ⟨_, hb, by simp [Orient.fwd]⟩
  · exact ⟨_, ht, by simp [Orient.fwd]⟩
  · exact ⟨_, hb, by simp [Orient.fwd]⟩
  · exact ⟨_, hr, by simp [Orient.fwd]; omega⟩
  · exact ⟨_, hr, by simp [Orient.fwd]; omega⟩
  · exact ⟨_, hl, by simp [Orient.fwd]; omega⟩
  · exact ⟨_, hl, by simp [Orient.fwd]; omega⟩

/-- `T_5` has a cell in a row `≥ q - 1` ("H_5 >= q", `report-A2.md`, 7.3). -/
private theorem oa7_up4 (F : FrameO P p q a b t o x5 y5) (hq : q < p) :
    ∃ c ∈ t 4, q - 1 ≤ c.2 := by
  obtain ⟨d, hd, hd2⟩ := oa7_fwd_up F.toFrame5 hq (o 4)
  refine ⟨(((o 4).fwd p q d).1 + x5, ((o 4).fwd p q d).2), ?_, hd2⟩
  rw [F.toFrame5.mem4, F.y5_eq]
  simpa [Orient.back_fwd] using hd

/-- **`report-A2.md`, 7.3, (16).** `T_5` has a cell in row `q - 1` in a column
`≥ p`: (T2)(a) (`crossing_T2a`) for `T = T_1` (rows `[0, q)`, cells `(0, 0)` and
`(p - 1, q - 1)`) and `T' = T_5` (`H_5 ≥ q`). -/
theorem o73_16 (F : FrameO P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p) (A : Alt o) :
    ∃ x : ℤ, p ≤ x ∧ ((x, q - 1) : Cell) ∈ t 4 := by
  have F' := F.toFrame5
  have hH0 : (o 0).H p q = q := by simp [Orient.H, A.w0]
  have hu := (F'.hrun_bounds 0).1
  have hmu := F.mu_pos
  have h40 : (((o 0).rowLine p q P 0, 0) : Cell) ∈ t 4 :=
    (F.bottom4 _).2 ⟨le_rfl, by omega⟩
  obtain ⟨c, hc, hcq⟩ := oa7_up4 F hq
  obtain ⟨x, hx, hxt⟩ := crossing_T2a (F'.sub_R 0) (F'.conn 0) (F'.sub_R 4) (F'.conn 4)
    (F'.tiling.disjoint 0 4 (by decide)) (H := q)
    (fun c hc => by have := (F'.box0 hc).2.2; rwa [hH0] at this)
    F'.corner0 (oa7_far0 F S A) h40 ⟨c, hc, hcq⟩ (by omega)
  exact ⟨x, by omega, hxt⟩

/-! ## `T_5` wide -/

/-- The lower corners of a wide box with two opposite occupied corners: the
local cell `(0, 0)` is in `P` if the mark is `A` or `C`, and otherwise the local
cells `(p - 1, 0)` and `(0, q - 1)` are. -/
private theorem oa7_wide_corners (S : Opposite P p q) {c : Orient} (hc : c.swap = false) :
    (c.negX = c.negY → c.back p q (0, 0) ∈ P) ∧
      (c.negX ≠ c.negY → c.back p q (p - 1, 0) ∈ P ∧ c.back p q (0, q - 1) ∈ P) := by
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;> simp_all [Orient.back, S.hA, S.hC]

/-- A cell of `T_5` in pattern O by its local position in `box(T_5)`. -/
private theorem oa7_mem4 (F : FrameO P p q a b t o x5 y5) (x y : ℤ) :
    ((x5 + x, y) : Cell) ∈ t 4 ↔ (o 4).back p q (x, y) ∈ P := by
  rw [F.toFrame5.mem4, F.y5_eq]
  simp

/-- **`report-A2.md`, 7.3, "T_5 wide", first lines.** `K` at the lower right is
against (T2)(b) (`crossing_T2b` for `T_1` and `T_5`, rows `[0, q)`):
`x5 ≥ p`, but `x5 + p = h_{m_1} + h_K ≤ 2p - 2`. So `K` is at the lower left,
`x5 = h_{m_1}`, and `x5 + p ≤ a - 1` is (17). -/
theorem o73_wide_left (F : FrameO P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (h4 : (o 4).swap = false) :
    (o 4).negX = (o 4).negY ∧ x5 = oppH P q (o 0).negX ∧
      p + 1 ≤ oppH P q (o 4).negY + oppV P p (o 1).negX := by
  -- the proof does not use `q < p`: `T_5` wide fixes `W_5 = p`, `H_5 = q`
  have _ := hq
  have F' := F.toFrame5
  have hy5 := F.y5_eq
  have hW4 : (o 4).W p q = p := by simp [Orient.W, h4]
  have hH4 : (o 4).H p q = q := by simp [Orient.H, h4]
  have hH0 : (o 0).H p q = q := by simp [Orient.H, A.w0]
  have hu0 : (o 0).rowLine p q P 0 = oppH P q (o 0).negX := by
    rw [S.toOpposite.hrun F' (i := 0) (by decide), A.w0]
    simp
  have hmu := o73_mu_wide (P := P) (p := p) (q := q) h4
  have a0 := S.h_lt (o 0).negX
  have a4 := S.h_lt (o 4).negY
  have hx5 := F.x5_le
  have hx1 := F.x5_pos
  have hmu1 := F.mu_pos
  obtain ⟨sb, -, -, -⟩ := o73_sides F S A
  have hc := oa7_wide_corners S.toOpposite h4
  have hK : (o 4).negX = (o 4).negY := by
    by_contra hne
    obtain ⟨hr, hl⟩ := hc.2 hne
    have hr' := (oa7_mem4 F (p - 1) 0).2 hr
    have hlt := crossing_T2b (F'.sub_R 0) (F'.conn 0) (F'.sub_R 4) (F'.conn 4)
      (F'.tiling.disjoint 0 4 (by decide)) (H := q)
      (fun c hc => by have := (F'.box0 hc).2.2; rwa [hH0] at this)
      (fun c hc => by have := (F'.box4 hc).2.2; rwa [hH4, hy5, zero_add] at this)
      F'.corner0 (oa7_far0 F S A) hr' ((oa7_mem4 F 0 (q - 1)).2 hl) (by omega)
    have := ((F.bottom4 _).1 hr').2
    omega
  have hll := (oa7_mem4 F 0 0).2 (hc.1 hK)
  have h1 := ((F.bottom4 _).1 hll).1
  have h2 := (F'.box4 ((F.bottom4 ((o 0).rowLine p q P 0)).2 ⟨le_rfl, by omega⟩)).1.1
  exact ⟨hK, by omega, by omega⟩

/-- `report-A2.md`, 7.3, "T_5 wide", case (a), and `d = e = 0`: with
`m_1 = m_3` the bottom and the top side give `v_{m_4} = v_{m_2} + h_K`, which is
`≥ p + 1 > q` by (17). -/
theorem o73_wide_a (F : FrameO P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (h4 : (o 4).swap = false) (h02 : (o 0).negX = (o 2).negX) : False := by
  obtain ⟨-, -, h17⟩ := o73_wide_left F S hq A h4
  obtain ⟨sb, st, -, -⟩ := o73_sides F S A
  rw [o73_mu_wide h4] at sb
  rw [← h02] at st
  have b3 := S.v_lt false
  have b4 := S.v_lt true
  revert h17 sb st
  cases (o 0).negX <;> cases (o 1).negX <;> cases (o 3).negX <;> cases (o 4).negY <;>
    intro h17 sb st <;> omega

/-- The side equations of 7.3 with `K = m_1`, `m_1 ≠ m_3`: `h_{m_3} > h_{m_1}`
(`report-A2.md`, 7.3, "T_5 wide", `K = m_1`: "h_{m_3} > h_{m_1}", from (1) in
cases (b) and (c)). -/
private theorem oa7_h_lt (h v : Bool → ℤ) (a b : ℤ) (m0 m1 m2 m3 : Bool) (h02 : m0 ≠ m2)
    (hpos : ∀ j, 1 ≤ h j) (sb : h m0 + h m0 + v m1 = a) (st : h m2 + v m3 = a)
    (sl : v m0 + h m3 = b) (sr : h m1 + v m2 = b) : h m0 < h m2 := by
  have := hpos false
  have := hpos true
  cases m0 <;> cases m1 <;> cases m2 <;> cases m3 <;> first | exact absurd rfl h02 | omega

/-- Two wide codes with the marks `A` and `C`: the local cell
`(p - 1 - x, q - 1)` of the first is the local cell `(x, 0)` of the second. -/
private theorem oa7_back_opp {c d : Orient} (hc : c.swap = false) (hd : d.swap = false)
    (hc' : c.negX = c.negY) (hd' : d.negY = d.negX) (hne : c.negX ≠ d.negX) (p q x : ℤ) :
    c.back p q (p - 1 - x, q - 1) = d.back p q (x, 0) := by
  rcases c with ⟨_ | _, _ | _, _ | _⟩ <;> rcases d with ⟨_ | _, _ | _, _ | _⟩ <;>
    simp_all [Orient.back]

/-- **`report-A2.md`, 7.3, "T_5 wide", `K = m_1`** (cases (b), (c)).
`T_5 = T_1 + (h_{m_1}, 0)`. In row `q - 1`, `T_1` has the run of `m_1'` that
ends at column `p - 1` and `T_5` its translate; disjoint, so
`h_{m_1'} ≤ h_{m_1}`. But `m_1' = m_3` and `h_{m_3} > h_{m_1}` (bottom and top
side). -/
theorem o73_wide_K1 (F : FrameO P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (h4 : (o 4).swap = false) (h02 : (o 0).negX ≠ (o 2).negX)
    (hK : (o 4).negY = (o 0).negX) : False := by
  have F' := F.toFrame5
  obtain ⟨hK4, hx5, -⟩ := o73_wide_left F S hq A h4
  obtain ⟨sb, st, sl, sr⟩ := o73_sides F S A
  rw [o73_mu_wide h4, hK] at sb
  have hgt := oa7_h_lt (oppH P q) (oppV P p) a b (o 0).negX (o 1).negX (o 2).negX (o 3).negX
    h02 S.h_pos sb st sl sr
  have hu2 : (o 2).rowLine p q P 0 = oppH P q (o 2).negX := by
    rw [S.toOpposite.hrun F' (i := 2) (by decide), A.w2]
    simp
  have h5 : ((p - 1, q - 1) : Cell) ∈ t 4 := by
    rw [F'.mem4, F.y5_eq, sub_zero]
    rw [oa7_back_opp h4 A.w2 hK4 (S.toOpposite.mark F' (i := 2) (by decide))
      (by rw [hK4, hK]; exact h02) p q x5]
    rw [F'.hside (i := 2) (by decide), hu2]
    have := F.x5_pos
    constructor <;> omega
  exact absurd (F'.tile_unique (oa7_far0 F S A) h5) (by decide)

/-- `report-A2.md`, 7.3, "T_5 wide", case (b): `K = m_3` and
`h_{m_3} = h_{m_1} + h_K`, so `h_{m_1} = 0`. -/
theorem o73_wide_b (F : FrameO P p q a b t o x5 y5) (S : OppFull P p q)
    (A : Alt o) (h4 : (o 4).swap = false) (h02 : (o 0).negX ≠ (o 2).negX)
    (hK : (o 4).negY ≠ (o 0).negX) (h13 : (o 1).negX = (o 3).negX) : False := by
  obtain ⟨sb, st, -, -⟩ := o73_sides F S A
  rw [o73_mu_wide h4] at sb
  rw [← h13] at st
  have a1 := S.h_pos false
  have a2 := S.h_pos true
  revert h02 hK sb st
  cases (o 0).negX <;> cases (o 1).negX <;> cases (o 2).negX <;> cases (o 4).negY <;>
    intro h02 hK sb st <;> first | exact (h02 rfl).elim | exact (hK rfl).elim | omega

/-- `report-A2.md`, 7.3, "T_5 wide", case (c), `K = m_3`, with the names
`m_1 = A`, `m_3 = C`: the codes of `T_1`, `T_3` (marks `A`, `C`, wide) and of
`T_5` (`K = C` at the lower left, by `o73_wide_left`), `x5 = h_A`, and
`N = b - p ≥ 1` (`H_2 = p ≤ b - 1`). -/
private theorem oc7_codes (F : FrameO P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (h4 : (o 4).swap = false) (m0 : (o 0).negX = false) (m2 : (o 2).negX = true)
    (hK : (o 4).negY = true) :
    o 0 = ⟨false, false, false⟩ ∧ o 2 = ⟨false, true, true⟩ ∧ o 4 = ⟨false, true, true⟩ ∧
      x5 = rowCount P 0 ∧ p + 1 ≤ b := by
  have F5 := F.toFrame5
  obtain ⟨hl, hx5, -⟩ := o73_wide_left F S hq A h4
  refine ⟨Orient.ext A.w0 m0 ((S.toOpposite.mark F5 (i := 0) (by decide)).trans m0),
    Orient.ext A.w2 m2 ((S.toOpposite.mark F5 (i := 2) (by decide)).trans m2),
    Orient.ext h4 (hl.trans hK) hK, by simpa [oppH, m0] using hx5, ?_⟩
  have h := F5.H_le (i := 1) (by decide)
  simp only [Orient.H, A.t1, ↓reduceIte] at h
  omega

/-- **`report-A2.md`, 7.3, "T_5 wide", case (c), `K = m_3`, `(m_2, m_4) = (A, C)`**,
with the names `m_1 = A`, `m_3 = C`. `h_A = delta`, `h_C = 2 delta`, `x5 = delta`,
`a = v + 3 delta`, `b = v + 2 delta`; (18) for the columns `c < delta`; row `K_0`
from the bottom and (18) give `Y_A(K_0) + X_A(K_0 - N) = 0`, but
`X_A(K_0 - N) ≥ 1`. -/
theorem o73_wide_c_AC (F : FrameO P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (h4 : (o 4).swap = false) (m0 : (o 0).negX = false) (m2 : (o 2).negX = true)
    (hK : (o 4).negY = true) (m1 : (o 1).negX = false) (m3 : (o 3).negX = true) : False := by
  have F5 := F.toFrame5
  obtain ⟨e0, e2, e4, hx5, hpb⟩ := oc7_codes F S hq A h4 m0 m2 hK
  have e1 : o 1 = ⟨true, false, false⟩ :=
    Orient.ext A.t1 m1 ((S.toOpposite.mark F5 (i := 1) (by decide)).trans m1)
  have e3 : o 3 = ⟨true, true, true⟩ :=
    Orient.ext A.t3 m3 ((S.toOpposite.mark F5 (i := 3) (by decide)).trans m3)
  -- (1): `a - b = h_A`, `h_C = 2 h_A`, `v_C = v_A + h_A`
  obtain ⟨sb, st, sl, sr⟩ := o73_sides F S A
  rw [o73_mu_wide h4, m0, m1, hK] at sb
  rw [m2, m3] at st
  rw [m0, m3] at sl
  rw [m1, m2] at sr
  have vC := S.v_lt true
  have hA := S.h_pos false
  simp only [oppH, oppV, ↓reduceIte, Bool.false_eq_true] at sb st sl sr vC hA
  have hy5 := F.y5_eq
  have hq2 := F5.two_le_q
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℤ, K0 = b - q := ⟨_, rfl⟩
  -- (18) at `c = K_0`, and the row `K_0` from the bottom
  have c1 := F5.col_sum (x := K0) (by omega) (by omega)
  have r1 := F5.row_sum (y := K0) (by omega) (by omega)
  rw [e0, e1, e2, e3, e4] at c1 r1
  simp only [Orient.colLine_wide, Orient.colLine_wide_neg, Orient.colLine_tall,
    Orient.colLine_tall_neg, Orient.rowLine_wide, Orient.rowLine_wide_neg, Orient.rowLine_tall,
    Orient.rowLine_tall_neg] at c1 r1
  simp (disch := omega) only [F5.rowCount_zero, F5.colCount_zero, add_zero] at c1 r1
  have k1 : rowCount P (q - 1 - (b - 1 - K0)) = rowCount P 0 := by congr 1; omega
  have k2 : colCount P (p - 1 - (b - 1 - K0)) = colCount P (p - q) := by congr 1; omega
  have k3 : rowCount P (q - 1 - (K0 - y5)) = rowCount P (q - 1 - K0) := by congr 1; omega
  have x1 := F5.colCount_pos (x := p - q) (by omega) (by omega)
  have y1 := rowCount_nonneg P K0
  omega

/-- **`report-A2.md`, 7.3, "T_5 wide", case (c), `K = m_3`, `(m_2, m_4) = (C, A)`.**
(18), the columns `c < delta` from the right, the rows `c < delta` from the top;
`X_A(c) - X_C(c) = delta` for `c < K_0`; at `c = K_0`: `Y_A(K_0) = delta`,
`X_A(K_0) = b - delta`, and row `K_0` from the top gives `Y_C(K_0) < 0`. -/
theorem o73_wide_c_CA (F : FrameO P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (h4 : (o 4).swap = false) (m0 : (o 0).negX = false) (m2 : (o 2).negX = true)
    (hK : (o 4).negY = true) (m1 : (o 1).negX = true) (m3 : (o 3).negX = false) : False := by
  have F5 := F.toFrame5
  obtain ⟨e0, e2, e4, hx5, hpb⟩ := oc7_codes F S hq A h4 m0 m2 hK
  have e1 : o 1 = ⟨true, true, true⟩ :=
    Orient.ext A.t1 m1 ((S.toOpposite.mark F5 (i := 1) (by decide)).trans m1)
  have e3 : o 3 = ⟨true, false, false⟩ :=
    Orient.ext A.t3 m3 ((S.toOpposite.mark F5 (i := 3) (by decide)).trans m3)
  -- (1): `a - b = h_A`, `h_C = 2 h_A`, `v_A = v_C + h_A`
  obtain ⟨sb, st, sl, sr⟩ := o73_sides F S A
  rw [o73_mu_wide h4, m0, m1, hK] at sb
  rw [m2, m3] at st
  rw [m0, m3] at sl
  rw [m1, m2] at sr
  have vA := S.v_lt false
  have hA := S.h_pos false
  simp only [oppH, oppV, ↓reduceIte, Bool.false_eq_true] at sb st sl sr vA hA
  have hy5 := F.y5_eq
  have hq2 := F5.two_le_q
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℤ, K0 = b - q := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℤ, D = p - q := ⟨_, rfl⟩
  -- (18) at `c = K_0`; the columns `K_0` and `D = K_0 - N` from the right; the
  -- rows `D` and `K_0` from the top; the row `K_0` from the bottom
  have c1 := F5.col_sum (x := K0) (by omega) (by omega)
  have c2 := F5.col_sum (x := a - 1 - K0) (by omega) (by omega)
  have c3 := F5.col_sum (x := a - 1 - D) (by omega) (by omega)
  have r1 := F5.row_sum (y := b - 1 - D) (by omega) (by omega)
  have r2 := F5.row_sum (y := b - 1 - K0) (by omega) (by omega)
  have r3 := F5.row_sum (y := K0) (by omega) (by omega)
  rw [e0, e1, e2, e3, e4] at c1 c2 c3 r1 r2 r3
  simp only [Orient.colLine_wide, Orient.colLine_wide_neg, Orient.colLine_tall,
    Orient.colLine_tall_neg, Orient.rowLine_wide, Orient.rowLine_wide_neg, Orient.rowLine_tall,
    Orient.rowLine_tall_neg] at c1 c2 c3 r1 r2 r3
  simp (disch := omega) only [F5.rowCount_zero, F5.colCount_zero, add_zero, zero_add]
    at c1 c2 c3 r1 r2 r3
  -- the column `K_0` from the right
  have k1 : rowCount P (q - 1 - (a - 1 - (a - 1 - K0))) = rowCount P (q - 1 - K0) := by
    congr 1; omega
  have k2 : colCount P (p - 1 - (a - 1 - (a - 1 - K0))) = colCount P (p - 1 - K0) := by
    congr 1; omega
  have k3 : colCount P (p - 1 - (a - 1 - K0 - x5)) = colCount P D := by congr 1; omega
  -- the column `D` from the right
  have k4 : rowCount P (q - 1 - (a - 1 - (a - 1 - D))) = rowCount P (q - 1 - D) := by
    congr 1; omega
  have k5 : colCount P (p - 1 - (a - 1 - (a - 1 - D))) = colCount P (q - 1) := by
    congr 1; omega
  have k6 : colCount P (p - 1 - (a - 1 - D - x5)) = colCount P (2 * p - q - b) := by
    congr 1; omega
  -- the row `D` from the top
  have k7 : colCount P (p - 1 - (b - 1 - D)) = colCount P (2 * p - q - b) := by
    congr 1; omega
  have k8 : rowCount P (q - 1 - (b - 1 - (b - 1 - D))) = rowCount P (q - 1 - D) := by
    congr 1; omega
  have k9 : colCount P (b - 1 - (b - 1 - D)) = colCount P D := by congr 1; omega
  -- the row `K_0` from the top
  have k10 : rowCount P (b - 1 - K0) = rowCount P (q - 1) := by congr 1; omega
  have k11 : colCount P (p - 1 - (b - 1 - K0)) = colCount P D := by congr 1; omega
  have k12 : rowCount P (q - 1 - (b - 1 - (b - 1 - K0))) = rowCount P (q - 1 - K0) := by
    congr 1; omega
  have k13 : colCount P (b - 1 - (b - 1 - K0)) = colCount P K0 := by congr 1; omega
  have k14 : rowCount P (q - 1 - (b - 1 - K0 - y5)) = rowCount P 0 := by congr 1; omega
  -- the row `K_0` from the bottom
  have k15 : rowCount P (q - 1 - (b - 1 - K0)) = rowCount P 0 := by congr 1; omega
  have k16 : colCount P (b - 1 - K0) = colCount P (q - 1) := by congr 1; omega
  have k17 : rowCount P (q - 1 - (K0 - y5)) = rowCount P (q - 1 - K0) := by congr 1; omega
  have y1 := rowCount_nonneg P (q - 1 - K0)
  have x1 := colCount_nonneg P D
  omega

/-- Case (c) for `T_5` wide with the names `m_1 = A`, `m_3 = C`. -/
theorem o73_wide_c_norm (F : FrameO P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (h4 : (o 4).swap = false) (m0 : (o 0).negX = false) (m2 : (o 2).negX = true)
    (hK : (o 4).negY = true) (h13 : (o 1).negX ≠ (o 3).negX) : False := by
  cases m1 : (o 1).negX
  · rw [m1] at h13
    exact o73_wide_c_AC F S hq A h4 m0 m2 hK m1 (by simpa using h13.symm)
  · rw [m1] at h13
    exact o73_wide_c_CA F S hq A h4 m0 m2 hK m1 (by simpa using h13.symm)

/-- `report-A2.md`, 7.3, "T_5 wide", case (c), `K = m_3`. "Let m_1 = A, m_3 = C
(names)": the half turn of `P` in its box. -/
theorem o73_wide_c (F : FrameO P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (h4 : (o 4).swap = false) (h02 : (o 0).negX ≠ (o 2).negX)
    (hK : (o 4).negY ≠ (o 0).negX) (h13 : (o 1).negX ≠ (o 3).negX) : False := by
  cases m0 : (o 0).negX
  · rw [m0] at h02 hK
    exact o73_wide_c_norm F S hq A h4 m0 (by simpa using h02.symm) (by simpa using hK) h13
  · rw [m0] at h02 hK
    have F' := F.flipPX.flipPY
    have S' := (S.toOpposite.turnP).full F'.toFrame5
    exact o73_wide_c_norm F' S' hq
      ⟨by simpa using A.w0, by simpa using A.t1, by simpa using A.w2, by simpa using A.t3⟩
      (by simpa using h4) (by simp [m0]) (by simpa using h02.symm) (by simpa using hK)
      (by simpa using h13)

/-- **`report-A2.md`, 7.3, "T_5 wide".** -/
theorem o73_wide (F : FrameO P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (h4 : (o 4).swap = false) : False := by
  by_cases h02 : (o 0).negX = (o 2).negX
  · exact o73_wide_a F S hq A h4 h02
  · by_cases hK : (o 4).negY = (o 0).negX
    · exact o73_wide_K1 F S hq A h4 h02 hK
    · by_cases h13 : (o 1).negX = (o 3).negX
      · exact o73_wide_b F S A h4 h02 hK h13
      · exact o73_wide_c F S hq A h4 h02 hK h13

/-! ## `T_5` tall -/

/-- A cell of `P` given by its two coordinates. -/
private theorem ot7_of_eq {c d : Cell} (h1 : c.1 = d.1) (h2 : c.2 = d.2) (hd : d ∈ P) :
    c ∈ P := by
  rwa [Prod.ext h1 h2]

/-- The cells of a tall `T_5` in pattern O, in the coordinates of `box(P)`. -/
private theorem ot7_mem4 (F : FrameO P p q a b t o x5 y5) (h4 : (o 4).swap = true) (X Y : ℤ) :
    ((X, Y) : Cell) ∈ t 4 ↔
      ((if (o 4).negX then p - 1 - Y else Y,
        if (o 4).negY then q - 1 - (X - x5) else X - x5) : Cell) ∈ P := by
  rw [F.toFrame5.mem4, F.y5_eq]
  simp [Orient.back, h4]

/-- The cells of a tall `T_2` with mark `A` or `C`, in the coordinates of
`box(P)`. -/
private theorem ot7_mem1 (F : Frame5 P p q a b t o x5 y5) (S : Opposite P p q)
    (h1 : (o 1).swap = true) (X Y : ℤ) :
    ((X, Y) : Cell) ∈ t 1 ↔
      ((if (o 1).negX then p - 1 - Y else Y,
        if (o 1).negX then q - 1 - (a - 1 - X) else a - 1 - X) : Cell) ∈ P := by
  rw [F.mem1]
  simp [Orient.back, h1, S.mark F (i := 1) (by decide)]

/-- A tall `T_2` contains `(a - q, p - 1)`, the corner of its box opposite to the
mark ("T_2 contains (a-q, p-1)", 7.3). -/
private theorem ot7_far1 (F : Frame5 P p q a b t o x5 y5) (S : Opposite P p q)
    (h1 : (o 1).swap = true) : ((a - q, p - 1) : Cell) ∈ t 1 := by
  rw [ot7_mem1 F S h1]
  cases (o 1).negX
  · exact ot7_of_eq (by simp) (by simp) S.hC
  · exact ot7_of_eq (by simp) (by simp) S.hA

/-- **`report-A2.md`, 7.3, "T_5 tall", first lines.** `K` at the lower left is
against (T2)(b), mirrored (`T_5` and `T_2`, rows `[0, p)`): `x5 + q - 1 < a - q`,
but `a ≤ x5 + 2q - 2`. So `K` is at the lower right, `u_1 + mu = x5 + q`, and
(16) gives (19). -/
theorem o73_tall_right (F : FrameO P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (h4 : (o 4).swap = true) :
    (o 4).negX ≠ (o 4).negY ∧ oppH P q (o 0).negX + oppV P p (o 4).negX = x5 + q ∧
      p + 1 ≤ oppH P q (o 0).negX + oppV P p (o 4).negX := by
  have F' := F.toFrame5
  obtain ⟨sb, -, -, -⟩ := o73_sides F S A
  rw [o73_mu_tall h4] at sb
  -- the bottom row: `T_5` holds the columns `[u_1, u_1 + mu)`
  have hb4 : ∀ x : ℤ, ((x, 0) : Cell) ∈ t 4 ↔
      oppH P q (o 0).negX ≤ x ∧ x < oppH P q (o 0).negX + oppV P p (o 4).negX := by
    intro x
    rw [F.bottom4, o73_mu_tall h4, S.toOpposite.hrun F' (i := 0) (by decide), A.w0]
    simp
  have hW4 : (o 4).W p q = q := by simp [Orient.W, h4]
  have hH4 : (o 4).H p q = p := by simp [Orient.H, h4]
  have hH1 : (o 1).H p q = p := by simp [Orient.H, A.t1]
  have hq2 := F'.two_le_q
  have hv1 := S.v_lt (o 1).negX
  have hv4 := S.v_lt (o 4).negX
  have hmu := F.mu_pos
  rw [o73_mu_tall h4] at hmu
  have hy5 := F.y5_eq
  have hx5 := F.x5_le
  rw [hW4] at hx5
  -- the cells of `T_5` in row 0 lie in the columns `[x5, x5 + q)`
  have r1 := (hb4 (oppH P q (o 0).negX)).2 ⟨le_rfl, by omega⟩
  have r2 := (hb4 (oppH P q (o 0).negX + oppV P p (o 4).negX - 1)).2 ⟨by omega, by omega⟩
  have r1' := (F'.box4 r1).1
  have r2' := (F'.box4 r2).1
  rw [hW4] at r1' r2'
  simp only at r1' r2'
  -- `K` at the lower left: (T2)(b) for `T_5` and `T_2` in the rows `[0, p)`
  have hK : (o 4).negX ≠ (o 4).negY := by
    intro hxy
    have c1 : ((x5, 0) : Cell) ∈ t 4 := by
      rw [ot7_mem4 F h4, ← hxy]
      cases (o 4).negX
      · exact ot7_of_eq (by simp) (by simp) S.hA
      · exact ot7_of_eq (by simp) (by simp) S.hC
    have c2 : ((x5 + q - 1, p - 1) : Cell) ∈ t 4 := by
      rw [ot7_mem4 F h4, ← hxy]
      cases (o 4).negX
      · exact ot7_of_eq (by simp) (by simp; omega) S.hC
      · exact ot7_of_eq (by simp) (by simp; omega) S.hA
    have hlt := crossing_T2b (F'.sub_R 4) (F'.conn 4) (F'.sub_R 1) (F'.conn 1)
      (F'.tiling.disjoint 4 1 (by decide)) (H := p)
      (fun c hc => by have := (F'.box4 hc).2.2; rw [hH4, hy5] at this; omega)
      (fun c hc => by have := (F'.box1 hc).2.2; rw [hH1] at this; exact this)
      c1 c2 F'.corner1 (ot7_far1 F' S.toOpposite A.t1) (by omega)
    have := (hb4 x5).1 c1
    omega
  -- `K` at the lower right: the cell `(x5 + q - 1, 0)` is in `T_5`
  have c3 : ((x5 + q - 1, 0) : Cell) ∈ t 4 := by
    rw [ot7_mem4 F h4]
    revert hK
    cases (o 4).negX <;> cases (o 4).negY <;> intro hK
    · exact absurd rfl hK
    · exact ot7_of_eq (by simp) (by simp; omega) S.hA
    · exact ot7_of_eq (by simp) (by simp; omega) S.hC
    · exact absurd rfl hK
  have r3 := (hb4 (x5 + q - 1)).1 c3
  refine ⟨hK, by omega, ?_⟩
  -- (16)
  obtain ⟨x, hx, hx4⟩ := o73_16 F S hq A
  have := (F'.box4 hx4).1.2
  rw [hW4] at this
  simp only at this
  omega

/-- `report-A2.md`, 7.3, "T_5 tall": "So not (b)", and `d = e = 0`. The bottom and
the top side with (19) and `h_{m_3} ≤ p - 1` give `v_{m_4} ≥ v_{m_2} + 2`. -/
theorem o73_tall_b (F : FrameO P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (h4 : (o 4).swap = true) (h13 : (o 1).negX = (o 3).negX) : False := by
  obtain ⟨-, -, h19⟩ := o73_tall_right F S hq A h4
  obtain ⟨sb, st, -, -⟩ := o73_sides F S A
  rw [o73_mu_tall h4] at sb
  rw [← h13] at st
  have a3 := S.h_lt false
  have a4 := S.h_lt true
  revert h19 sb st
  cases (o 0).negX <;> cases (o 1).negX <;> cases (o 2).negX <;> cases (o 4).negX <;>
    intro h19 sb st <;> omega

/-- The run of a mark along the short side of `box(P)`: the column of `P` at the
mark `j` holds the first `v_j` cells from the mark ((R) of `report-A2.md`, 1.2). -/
private theorem ot7_vrunP (F : Frame5 P p q a b t o x5 y5) (S : Opposite P p q) {i : Fin 5}
    (hi : i ≠ 4) (y : ℤ) :
    ((if (o i).negX then p - 1 else 0, if (o i).negX then q - 1 - y else y) : Cell) ∈ P ↔
      0 ≤ y ∧ y < oppV P p (o i).negX := by
  have hm := S.mark F hi
  cases hs : (o i).swap
  · simpa [Orient.back, Orient.colLine, hs, hm, oppV] using F.vside hi y
  · simpa [Orient.back, Orient.rowLine, hs, hm, oppV] using F.hside hi y

/-- **`report-A2.md`, 7.3, "T_5 tall", `K = m_2`.** `T_5 = T_2 - (v_{m_2}, 0)`. In
row `p - 1`, `T_2` has the run of `m_2'` and `T_5` its translate; disjoint, so
`v_{m_2'} ≤ v_{m_2}`. But `m_2' = m_4` and `v_{m_4} > v_{m_2}`. The cell
`(a - q, p - 1)` is in both. -/
theorem o73_tall_K2 (F : FrameO P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (h4 : (o 4).swap = true) (h13 : (o 1).negX ≠ (o 3).negX)
    (hK : (o 4).negX = (o 1).negX) : False := by
  have F' := F.toFrame5
  obtain ⟨hKr, h5, h19⟩ := o73_tall_right F S hq A h4
  obtain ⟨sb, st, -, -⟩ := o73_sides F S A
  rw [o73_mu_tall h4] at sb
  have l2 := S.h_lt (o 2).negX
  have l1 := S.v_pos (o 1).negX
  -- `a - q - x5 = v_{m_2} < v_{m_4}`: the run of `m_4` in its column reaches it
  have hr := (ot7_vrunP F' S.toOpposite (i := 3) (by decide) (a - q - x5)).2
    ⟨by omega, by omega⟩
  have c4 : ((a - q, p - 1) : Cell) ∈ t 4 := by
    rw [ot7_mem4 F h4]
    revert h13 hK hKr hr
    cases (o 1).negX <;> cases (o 3).negX <;> cases (o 4).negX <;> cases (o 4).negY <;>
      intro h13 hK hKr hr <;>
      first
        | exact absurd rfl h13
        | exact absurd rfl hKr
        | exact absurd hK Bool.false_ne_true
        | exact absurd hK.symm Bool.false_ne_true
        | simpa using hr
  exact Finset.disjoint_left.1 (F'.tiling.disjoint 1 4 (by decide))
    (ot7_far1 F' S.toOpposite A.t1) c4

/-- `report-A2.md`, 7.3, "T_5 tall", case (a): `K = m_4` and
`v_{m_4} = v_{m_2} + v_K`, so `v_{m_2} = 0`. -/
theorem o73_tall_a (F : FrameO P p q a b t o x5 y5) (S : OppFull P p q)
    (A : Alt o) (h4 : (o 4).swap = true) (h13 : (o 1).negX ≠ (o 3).negX)
    (hK : (o 4).negX ≠ (o 1).negX) (h02 : (o 0).negX = (o 2).negX) : False := by
  obtain ⟨sb, st, -, -⟩ := o73_sides F S A
  rw [o73_mu_tall h4] at sb
  rw [← h02] at st
  have b1 := S.v_pos false
  have b2 := S.v_pos true
  revert h13 hK sb st
  cases (o 0).negX <;> cases (o 1).negX <;> cases (o 3).negX <;> cases (o 4).negX <;>
    intro h13 hK sb st <;> first | exact (h13 rfl).elim | exact (hK rfl).elim | omega

/-- The cells of a wide `T_1` with mark `A` or `C`, in the coordinates of
`box(P)`. -/
private theorem ot7_mem0 (F : Frame5 P p q a b t o x5 y5) (S : Opposite P p q)
    (h0 : (o 0).swap = false) (X Y : ℤ) :
    ((X, Y) : Cell) ∈ t 0 ↔
      ((if (o 0).negX then p - 1 - X else X, if (o 0).negX then q - 1 - Y else Y) : Cell) ∈ P := by
  rw [F.mem0]
  simp [Orient.back, h0, S.mark F (i := 0) (by decide)]

/-- The run of a mark along the long side of `box(P)`: the row of `P` at the
mark `j` holds the first `h_j` cells from the mark ((R) of `report-A2.md`, 1.2). -/
private theorem ot7_hrunP (F : Frame5 P p q a b t o x5 y5) (S : Opposite P p q) {i : Fin 5}
    (hi : i ≠ 4) (x : ℤ) :
    ((if (o i).negX then p - 1 - x else x, if (o i).negX then q - 1 else 0) : Cell) ∈ P ↔
      0 ≤ x ∧ x < oppH P q (o i).negX := by
  have hm := S.mark F hi
  cases hs : (o i).swap
  · simpa [Orient.back, Orient.rowLine, hs, hm, oppH] using F.hside hi x
  · simpa [Orient.back, Orient.colLine, hs, hm, oppH] using F.vside hi x

/-- **`report-A2.md`, 7.3, "T_5 tall", case (c), `K = m_4`.** `v_{m_2} = delta`,
`v_{m_4} = 2 delta`, `a = h_{m_1} + 3 delta`. The cell `(a - q, q - 1)` lies in
`T_1` (the run of `m_1' = m_3` in row `q - 1`) and in `T_2` (the run of
`m_2' = m_4` in column `a - q`). -/
theorem o73_tall_c (F : FrameO P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (h4 : (o 4).swap = true) (h13 : (o 1).negX ≠ (o 3).negX)
    (hK : (o 4).negX ≠ (o 1).negX) (h02 : (o 0).negX ≠ (o 2).negX) : False := by
  have F' := F.toFrame5
  obtain ⟨-, -, h19⟩ := o73_tall_right F S hq A h4
  obtain ⟨sb, st, sl, sr⟩ := o73_sides F S A
  rw [o73_mu_tall h4] at sb
  -- the arithmetic of case (c): `a - q < p`, `p - h_{m_3} ≤ a - q`, `p - q < h_{m_4}`
  have key : a - q ≤ p - 1 ∧ p - 1 - (a - q) < oppH P q (o 2).negX ∧
      p - q < oppH P q (o 3).negX := by
    have l2 := S.h_lt (o 2).negX
    have l1 := S.v_pos (o 1).negX
    have l3 := S.v_lt (o 3).negX
    have l4 := S.v_lt (o 4).negX
    revert h13 hK h02 h19 sb st sl sr l2 l1 l3 l4
    cases (o 0).negX <;> cases (o 1).negX <;> cases (o 2).negX <;> cases (o 3).negX <;>
      cases (o 4).negX <;> intro h13 hK h02 h19 sb st sl sr l2 l1 l3 l4 <;>
      first
        | exact absurd rfl h13
        | exact absurd rfl hK
        | exact absurd rfl h02
        | omega
  obtain ⟨k1, k2, k3⟩ := key
  -- `T_1` has in row `q - 1` the run of `m_1' = m_3`
  have x1 : ((a - q, q - 1) : Cell) ∈ t 0 := by
    have hr := (ot7_hrunP F' S.toOpposite (i := 2) (by decide) (p - 1 - (a - q))).2
      ⟨by omega, k2⟩
    rw [ot7_mem0 F' S.toOpposite A.w0]
    revert h02 hr
    cases (o 0).negX <;> cases (o 2).negX <;> intro h02 hr
    · exact absurd rfl h02
    · exact ot7_of_eq (by simp) (by simp) hr
    · exact ot7_of_eq (by simp) (by simp) hr
    · exact absurd rfl h02
  -- `T_2` has in column `a - q` the run of `m_2' = m_4`
  have x2 : ((a - q, q - 1) : Cell) ∈ t 1 := by
    have hr := (ot7_hrunP F' S.toOpposite (i := 3) (by decide) (p - q)).2 ⟨by omega, k3⟩
    rw [ot7_mem1 F' S.toOpposite A.t1]
    revert h13 hr
    cases (o 1).negX <;> cases (o 3).negX <;> intro h13 hr
    · exact absurd rfl h13
    · exact ot7_of_eq (by simp) (by simp) hr
    · exact ot7_of_eq (by simp) (by simp) hr
    · exact absurd rfl h13
  exact Finset.disjoint_left.1 (F'.tiling.disjoint 0 1 (by decide)) x1 x2

/-- **`report-A2.md`, 7.3, "T_5 tall".** -/
theorem o73_tall (F : FrameO P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p)
    (A : Alt o) (h4 : (o 4).swap = true) : False := by
  by_cases h13 : (o 1).negX = (o 3).negX
  · exact o73_tall_b F S hq A h4 h13
  · by_cases hK : (o 4).negX = (o 1).negX
    · exact o73_tall_K2 F S hq A h4 h13 hK
    · by_cases h02 : (o 0).negX = (o 2).negX
      · exact o73_tall_a F S A h4 h13 hK h02
      · exact o73_tall_c F S hq A h4 h13 hK h02

/-- `report-A2.md`, 7.3, in the normal form of 7.1. -/
theorem o73 (F : FrameO P p q a b t o x5 y5) (S : OppFull P p q) (hq : q < p) (A : Alt o) :
    False := by
  cases h4 : (o 4).swap
  · exact o73_wide F S hq A h4
  · exact o73_tall F S hq A h4

/-- **`report-A2.md`, 7.3.** Pattern O does not occur with two opposite occupied
corners. -/
theorem opp_O (F : FrameO P p q a b t o x5 y5) (S : Opposite P p q) (hpq : q ≤ p) : False := by
  have S' := S.full F.toFrame5
  obtain ⟨hne, h02, h13, h01⟩ := opp_alt F.toFrame5 S' F.y5_le F.x5_pos F.x5_le
  have hq : q < p := by omega
  cases h0 : (o 0).swap
  · exact o73 F S' hq (Alt.of h0 h02 h13 h01)
  · obtain ⟨t', F'⟩ := F.flipX
    exact o73 F' S' hq (Alt.flip h0 h02 h13 h01 _)

end PolyominoOddOrder
