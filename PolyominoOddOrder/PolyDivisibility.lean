module

public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Case (I), the divisibility step of section 7.2 (`PolyDivisibility.lean`)

No unit (third increment, proved). `report-A2.md`, section 7.2, "Divisibility":
the four column and row sums of the alternating pattern are four polynomial
equations `M F = s E` over `ℤ[X]`, where the entries of `M` are monomials `±X^n`,
the entries of `F` are the generating polynomials of the line counts of `P` and
`s` is `a` or `b`. If a prime `l` does not divide `det M(1)`, then `M` is
injective modulo `l`, so `l` divides every coefficient of `F`; dividing by `l`
and repeating gives every power of `l` that divides `s`.

Nothing here mentions cells or tilings. The statements:

* `C_pow_dvd_of_mulVec`, `pow_dvd_coeff_of_mulVec`: `M F = l^k G` and
  `l ∤ det M(1)` give `l^k ∣` every coefficient of every entry of `F`;
* `det_eval_one`: `det M(1)` is the determinant of the integer matrix of the
  values at `1`, which `decide` computes for the 64 choices of marks.

The proof was written and compiled by the algebra unit of this increment; this
file is its copy in the library.

Source: `theoretician/report-A2.md` (goals lab, commit `076d663`), section 7.2.
-/

@[expose] public section

open Polynomial

namespace PolyominoOddOrder

/-- `report-A2.md`, section 7.2 ("Divisibility"), the induction on `k`. If
`M F = l^k G` for a square matrix `M` of integer polynomials whose determinant
at `1` is not divisible by the prime `l`, then the constant `l^k` divides every
entry of `F`. -/
theorem C_pow_dvd_of_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ[X]) (l : ℕ) [hl : Fact l.Prime]
    (hdet : ¬ (l : ℤ) ∣ M.det.eval 1) (k : ℕ) :
    ∀ F G : Fin n → ℤ[X], M.mulVec F = (fun i => C ((l : ℤ) ^ k) * G i) →
      ∀ i, C ((l : ℤ) ^ k) ∣ F i := by
  induction k with
  | zero => intro F G _ i; simp
  | succ k ih =>
    intro F G h
    have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
    -- Reduce modulo `l`: the matrix stays invertible, the right side vanishes.
    let φ : ℤ[X] →+* (ZMod l)[X] := mapRingHom (Int.castRingHom (ZMod l))
    have hφC : φ (C ((l : ℤ) ^ (k + 1))) = 0 := by
      simp [φ, pow_succ]
    have hzero : (M.map φ).mulVec (fun i => φ (F i)) = 0 := by
      funext i
      have hi := congrArg φ (congrFun h i)
      rw [map_mul, hφC, zero_mul] at hi
      rw [Pi.zero_apply, ← hi]
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    have hdet' : (M.map φ).det ≠ 0 := by
      intro h0
      apply hdet
      have h1 : φ M.det = 0 := by
        rw [RingHom.map_det]; exact h0
      have h2 : (φ M.det).eval 1 = 0 := by rw [h1]; simp
      have h3 : (φ M.det).eval 1 = ((M.det.eval 1 : ℤ) : ZMod l) := by
        simp [φ]
      rw [h3] at h2
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h2
    have hF : (fun i => φ (F i)) = 0 :=
      Matrix.eq_zero_of_mulVec_eq_zero hdet' hzero
    -- So `l` divides every entry of `F`; divide by `l` and use the induction.
    have hdiv : ∀ i, C (l : ℤ) ∣ F i := by
      intro i
      rw [C_dvd_iff_dvd_coeff]
      intro j
      have hj := congrArg (fun p : (ZMod l)[X] => p.coeff j) (congrFun hF i)
      simp only [φ, coe_mapRingHom, coeff_map, Pi.zero_apply, coeff_zero, eq_intCast] at hj
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hj
    choose F' hF' using hdiv
    have hCl : (C (l : ℤ) : ℤ[X]) ≠ 0 := by simpa using hl0
    have h' : M.mulVec F' = fun i => C ((l : ℤ) ^ k) * G i := by
      funext i
      apply mul_left_cancel₀ hCl
      have hi := congrFun h i
      have e1 : M.mulVec F i = C (l : ℤ) * M.mulVec F' i := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hF' j]; ring
      rw [← e1, hi, pow_succ, C_mul]
      ring
    intro i
    obtain ⟨c, hc⟩ := ih F' G h' i
    refine ⟨c, ?_⟩
    rw [hF' i, hc, pow_succ, C_mul]
    ring

/-- `report-A2.md`, section 7.2 ("Divisibility"), coefficient form: under the
hypotheses of `C_pow_dvd_of_mulVec`, `l^k` divides every coefficient of every
entry of `F`. In 7.2 the entries of `F` are `X_A, X_C, Y_A, Y_C`, so the
coefficient `X_A(0) = v` (or `Y_A(0) = h`) is divisible by `l^k`. -/
theorem pow_dvd_coeff_of_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ[X]) (l : ℕ)
    [Fact l.Prime] (hdet : ¬ (l : ℤ) ∣ M.det.eval 1) (k : ℕ) (F G : Fin n → ℤ[X])
    (h : M.mulVec F = fun i => C ((l : ℤ) ^ k) * G i) (i : Fin n) (j : ℕ) :
    (l : ℤ) ^ k ∣ (F i).coeff j :=
  (C_dvd_iff_dvd_coeff _ _).1 (C_pow_dvd_of_mulVec M l hdet k F G h i) j

/-- `report-A2.md`, section 7.2, formula (15): the determinant at `1` is the
determinant of the integer matrix of the values at `1`. -/
theorem det_eval_one {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ[X]) :
    M.det.eval 1 = (M.map (fun p => p.eval 1)).det := by
  have h := RingHom.map_det (evalRingHom (1 : ℤ)) M
  simpa [RingHom.mapMatrix_apply, coe_evalRingHom] using h

end PolyominoOddOrder
