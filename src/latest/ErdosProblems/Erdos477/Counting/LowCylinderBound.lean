/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform counting on every irreducible line or conic cylinder in the selected sextic surface.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.ZeroTraceCylinderBound
import ErdosProblems.Erdos477.Counting.QuadraticTraceBound
import ErdosProblems.Erdos477.Counting.RationalCylinderBound

namespace Erdos477.Counting

open Erdos477.Geometry
open Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

theorem exists_low_cylinder_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ c : ℤ, c ∉ PowerValues 6 →
      ∀ P : MvPolynomial (Fin 2) K, Irreducible P → P.totalDegree ≤ 2 →
      ∀ B : ℝ, 1 ≤ B → ∀ S : Finset (Fin 3 → ℤ),
      (∀ z ∈ S, IntegerDiagonalPoint c z ∧ 1 ≤ z 1) →
      (∀ z ∈ S, MvPolynomial.eval ![(z 1 : K), (z 2 : K)] P = 0) →
      (∀ z ∈ S, ∀ i, |(z i : ℝ)| ≤ B) →
      (S.card : ℝ) ≤ M * B ^ ((1 : ℝ) / 3 + ε) := by
  obtain ⟨V, hV, hvertical⟩ := exists_polynomial_vertical_fiber_bound (K := K) 2 ε hε
  obtain ⟨R, hR, hrational⟩ := exists_rational_cylinder_bound (K := K) ε hε
  obtain ⟨T, hT, htrace⟩ := exists_quadratic_trace_bound (K := K) ε hε
  obtain ⟨Z, hZ, hzero⟩ := exists_zero_trace_cylinder_bound (K := K) ε hε
  refine ⟨V + R + T + Z, by positivity, ?_⟩
  intro c hc P hP hdegree B hB S hS hroot hheight
  have hpower : 0 ≤ B ^ ((1 : ℝ) / 3 + ε) := Real.rpow_nonneg (by linarith) _
  let a : Fin 6 → K := fun i => P.coeff (quadraticExponent i)
  have hPa : P = planeQuadratic a := eq_planeQuadratic_of_totalDegree_le P hdegree
  rw [hPa] at hP hroot
  by_cases ha : a 0 = 0
  · have hlin (z) (hz : z ∈ S) :
        (planeLinearCoefficient a).eval (z 2 : K) * (z 1 : K) +
          (planeConstantCoefficient a).eval (z 2 : K) = 0 := by
      simpa only [eval_planeQuadratic_linear a ha] using hroot z hz
    by_cases hd : planeLinearCoefficient a = 0
    · have hn := planeConstantCoefficient_ne_zero a ha hd hP.ne_zero
      have hcount := hvertical c (planeConstantCoefficient a) hn
        (degree_planeConstantCoefficient a) B hB S (fun z hz => (hS z hz).1) (by
          intro z hz
          simpa only [hd, eval_zero, zero_mul, zero_add] using hlin z hz) hheight
      have hp : B ^ ((1 : ℝ) / 6 + ε) ≤ B ^ ((1 : ℝ) / 3 + ε) :=
        Real.rpow_le_rpow_of_exponent_le hB (by linarith)
      have hcount' := hcount.trans (mul_le_mul_of_nonneg_left hp hV.le)
      exact hcount'.trans (mul_le_mul_of_nonneg_right (by linarith) hpower)
    · have hcount := hrational c hc (-planeConstantCoefficient a) (planeLinearCoefficient a)
        (by simpa only [natDegree_neg] using degree_planeConstantCoefficient a)
        (degree_planeLinearCoefficient a) hd B hB S hS (by
          intro z hz
          rw [eval_neg]
          linear_combination -(hlin z hz)) hheight
      exact hcount.trans (mul_le_mul_of_nonneg_right (by linarith) hpower)
  · let b := normalizedQuadraticTrace a
    let q := normalizedQuadraticConstant a
    have hb : b.natDegree ≤ 1 := degree_normalizedQuadraticTrace a
    have hq : q.natDegree ≤ 2 := degree_normalizedQuadraticConstant a
    have hquad (z) (hz : z ∈ S) :
        (z 1 : K) ^ 2 + b.eval (z 2 : K) * (z 1 : K) + q.eval (z 2 : K) = 0 :=
      (planeQuadratic_root_iff_normalized a ha (z 1 : K) (z 2 : K)).mp (hroot z hz)
    by_cases hA : quadraticSixthLinear b q = 0
    · have hirr : Irreducible (X ^ 2 + C b * X + C q) :=
        irreducible_normalized_planeQuadratic a ha hP
      have hb0 := quadraticSixthLinear_zero_forces_zero_trace b q hirr hA
      have hcount := hzero c hc (-q) (by simpa only [natDegree_neg] using hq) B hB S
        (fun z hz => (hS z hz).1) (by
          intro z hz
          have heq := hquad z hz
          rw [hb0, eval_zero, zero_mul, add_zero] at heq
          rw [eval_neg]
          linear_combination heq) hheight
      exact hcount.trans (mul_le_mul_of_nonneg_right (by linarith) hpower)
    · have hcount := htrace c hc b q hb hq hA B hB S hS hquad hheight
      exact hcount.trans (mul_le_mul_of_nonneg_right (by linarith) hpower)

#print axioms exists_low_cylinder_bound
-- 'Erdos477.Counting.exists_low_cylinder_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
