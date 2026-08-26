/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The low-degree factors of the remaining sixth-power equation on a square cylinder.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.LinearSquareCylinderBound
import ErdosProblems.Erdos477.Counting.SquareCylinderBound
import ErdosProblems.Erdos477.Geometry.PlaneQuadraticLinear
import ErdosProblems.Erdos477.Geometry.PlaneQuadraticNormalization
import ErdosProblems.Erdos477.Geometry.QuadraticSixthDivisor

namespace Erdos477.Counting

open Erdos477.Geometry
open Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

theorem exists_small_zero_trace_factor_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ c : ℤ, c ∉ PowerValues 6 →
      ∀ g : K[X], g.natDegree ≤ 2 → ∀ Q : MvPolynomial (Fin 2) K,
      Irreducible Q → Q.totalDegree ≤ 2 → Q ∣ zeroTraceEquation (c : K) g →
      ∀ B : ℝ, 1 ≤ B → ∀ S : Finset (Fin 3 → ℤ),
      (∀ z ∈ S, IntegerDiagonalPoint c z) →
      (∀ z ∈ S, (z 1 : K) ^ 2 = g.eval (z 2 : K)) →
      (∀ z ∈ S, MvPolynomial.eval ![(z 0 : K), (z 2 : K)] Q = 0) →
      (∀ z ∈ S, ∀ i, |(z i : ℝ)| ≤ B) →
      (S.card : ℝ) ≤ M * B ^ ((1 : ℝ) / 3 + ε) := by
  obtain ⟨V, hV, hvertical⟩ := exists_polynomial_vertical_fiber_bound (K := K) 2 ε hε
  obtain ⟨L, hL, hlinear⟩ := exists_linear_square_cylinder_bound (K := K) ε hε
  obtain ⟨T, hT, hsquare⟩ := exists_square_cylinder_bound (K := K) ε hε
  refine ⟨V + L + T, by positivity, ?_⟩
  intro c hc g hg Q hQ hdegree hdiv B hB S hS hy hroot hheight
  have hpower : 0 ≤ B ^ ((1 : ℝ) / 3 + ε) := Real.rpow_nonneg (by linarith) _
  let a : Fin 6 → K := fun i => Q.coeff (quadraticExponent i)
  have hQa : Q = planeQuadratic a := eq_planeQuadratic_of_totalDegree_le Q hdegree
  rw [hQa] at hQ hdiv hroot
  have hdiv' := map_dvd (bivariateEquiv K) hdiv
  rw [bivariateEquiv_zeroTraceEquation] at hdiv'
  by_cases ha : a 0 = 0
  · rw [bivariateEquiv_planeQuadratic_linear a ha] at hdiv'
    have hlin (z) (hz : z ∈ S) :
        (planeLinearCoefficient a).eval (z 2 : K) * (z 0 : K) +
          (planeConstantCoefficient a).eval (z 2 : K) = 0 := by
      simpa only [eval_planeQuadratic_linear a ha] using hroot z hz
    by_cases hd : planeLinearCoefficient a = 0
    · have hn := planeConstantCoefficient_ne_zero a ha hd hQ.ne_zero
      have hcount := hvertical c (planeConstantCoefficient a) hn
        (degree_planeConstantCoefficient a) B hB S hS (by
          intro z hz
          simpa only [hd, eval_zero, zero_mul, zero_add] using hlin z hz) hheight
      have hp : B ^ ((1 : ℝ) / 6 + ε) ≤ B ^ ((1 : ℝ) / 3 + ε) :=
        Real.rpow_le_rpow_of_exponent_le hB (by linarith)
      have hcount' := hcount.trans (mul_le_mul_of_nonneg_left hp hV.le)
      exact hcount'.trans (mul_le_mul_of_nonneg_right (by linarith) hpower)
    · have hcount := hlinear c hc g (-planeConstantCoefficient a) (planeLinearCoefficient a)
        hg (degree_planeLinearCoefficient a) hd
        (by simpa only [map_neg, sub_neg_eq_add] using hdiv')
        B hB S hS hy (by
          intro z hz
          rw [eval_neg]
          linear_combination -(hlin z hz)) hheight
      exact hcount.trans (mul_le_mul_of_nonneg_right (by linarith) hpower)
  · let b := normalizedQuadraticTrace a
    let q := normalizedQuadraticConstant a
    have hirr : Irreducible (X ^ 2 + C b * X + C q) :=
      irreducible_normalized_planeQuadratic a ha hQ
    rw [bivariateEquiv_planeQuadratic_normalized a ha] at hdiv'
    have hmono : X ^ 2 + C b * X + C q ∣ X ^ 6 - C (X ^ 6 + C (c : K) - g ^ 3) :=
      (dvd_mul_left _ _).trans hdiv'
    obtain ⟨hb, hrelation⟩ := irreducible_quadratic_sixth_divisor b q
      (X ^ 6 + C (c : K) - g ^ 3) hirr hmono
    have hcount := hsquare c hc (-q) g (by
      simpa only [natDegree_neg] using degree_normalizedQuadraticConstant a) hg (by
        linear_combination -hrelation) B hB S hS (by
          intro z hz
          refine ⟨?_, hy z hz⟩
          have hquad := (planeQuadratic_root_iff_normalized a ha (z 0 : K) (z 2 : K)).mp
            (hroot z hz)
          change (z 0 : K) ^ 2 + b.eval (z 2 : K) * (z 0 : K) + q.eval (z 2 : K) = 0 at hquad
          rw [hb, eval_zero, zero_mul, add_zero] at hquad
          rw [eval_neg]
          linear_combination hquad) hheight
    exact hcount.trans (mul_le_mul_of_nonneg_right (by linarith) hpower)

#print axioms exists_small_zero_trace_factor_bound
-- 'Erdos477.Counting.exists_small_zero_trace_factor_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
