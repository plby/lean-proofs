import ErdosProblems.Erdos633b.SixthRootPolynomialNorm

/-! Explicit rational polynomial coordinates for a quadratic expression
on x^2+xy+y^2=1, after adjoining a sixth root of unity. -/

namespace Erdos633b
open Polynomial

noncomputable def quadraticConicLift0 (a : Fin 5 → ℚ) : ℚ[X] :=
  C (a 3 - a 4) * X ^ 4 - C (a 1 + a 2) * X ^ 3 +
  C (-3 * a 0 - 2 * a 3 + a 4) * X ^ 2 + C (a 1 - 2 * a 2) * X + C (a 3)

noncomputable def quadraticConicLift1 (a : Fin 5 → ℚ) : ℚ[X] :=
  C (a 4) * X ^ 4 + C (2 * a 1 - a 2) * X ^ 3 + C (-2 * a 1 + a 2) * X - C (a 4)

theorem quadraticConicLift0_degree (a : Fin 5 → ℚ) :
    (quadraticConicLift0 a).natDegree ≤ 4 := by
  unfold quadraticConicLift0
  compute_degree

theorem quadraticConicLift1_degree (a : Fin 5 → ℚ) :
    (quadraticConicLift1 a).natDegree ≤ 4 := by
  unfold quadraticConicLift1
  compute_degree

theorem quadraticConicLifts_coeffs_zero (a : Fin 5 → ℚ)
    (h0 : quadraticConicLift0 a = 0) (h1 : quadraticConicLift1 a = 0) : ∀ i, a i = 0 := by
  have h4 : a 4 = 0 := by
    simpa [quadraticConicLift1, -map_add, -map_mul, -map_sub, -map_neg]
      using congrArg (fun p : ℚ[X] => p.coeff 4) h1
  have h3 : a 3 = 0 := by
    simpa [quadraticConicLift0, -map_add, -map_mul, -map_sub, -map_neg]
      using congrArg (fun p : ℚ[X] => p.coeff 0) h0
  have ha0 : -3 * a 0 = 0 := by
    simpa [quadraticConicLift0, -map_add, -map_mul, -map_sub, -map_neg, h3, h4]
      using congrArg (fun p : ℚ[X] => p.coeff 2) h0
  have ha1 : -(a 1 + a 2) = 0 := by
    simpa [quadraticConicLift0, -map_add, -map_mul, -map_sub, -map_neg]
      using congrArg (fun p : ℚ[X] => p.coeff 3) h0
  have ha2 : 2 * a 1 - a 2 = 0 := by
    simpa [quadraticConicLift1, -map_add, -map_mul, -map_sub, -map_neg]
      using congrArg (fun p : ℚ[X] => p.coeff 3) h1
  intro i
  fin_cases i
  · change a 0 = 0; linarith
  · change a 1 = 0; linarith
  · change a 2 = 0; linarith
  · exact h3
  · exact h4

theorem quadraticConicLifts_eval (a : Fin 5 → ℚ) (z ω : ℂ)
    (hω : ω ^ 2 - ω + 1 = 0) :
    aeval z (quadraticConicLift0 a) + ω * aeval z (quadraticConicLift1 a) =
      (a 0 : ℂ) * (2 * ω - 1) ^ 2 * z ^ 2 +
      a 1 * (2 * ω - 1) * z * (z ^ 2 - 1) +
      a 2 * (2 * ω - 1) * z * (ω * (1 + z ^ 2) - z ^ 2) +
      a 3 * (z ^ 2 - 1) ^ 2 + a 4 * (z ^ 2 - 1) * (ω * (1 + z ^ 2) - z ^ 2) := by
  simp only [quadraticConicLift0, quadraticConicLift1, map_add, map_sub, map_mul, map_pow,
    map_neg, aeval_C, aeval_X]
  have hcast (q : ℚ) : algebraMap ℚ ℂ q = (q : ℂ) := rfl
  simp only [hcast]
  push_cast
  linear_combination -(4 * (a 0 : ℂ) * z ^ 2 + 2 * a 2 * z * (1 + z ^ 2)) * hω

theorem quadraticConicLifts_eval_coordinates (a : Fin 5 → ℚ) (z ω x y : ℂ)
    (hω : ω ^ 2 - ω + 1 = 0)
    (hx : (2 * ω - 1) * z * x = z ^ 2 - 1)
    (hy : (2 * ω - 1) * z * y = ω * (1 + z ^ 2) - z ^ 2) :
    aeval z (quadraticConicLift0 a) + ω * aeval z (quadraticConicLift1 a) =
      (2 * ω - 1) ^ 2 * z ^ 2 *
        ((a 0 : ℂ) + a 1 * x + a 2 * y + a 3 * x ^ 2 + a 4 * x * y) := by
  rw [quadraticConicLifts_eval a z ω hω, ← hx, ← hy]
  ring

end Erdos633b
