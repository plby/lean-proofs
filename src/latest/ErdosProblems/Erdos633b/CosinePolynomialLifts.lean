import ErdosProblems.Erdos633b.CosineCyclotomicTransfer
import Mathlib.Tactic.ComputeDegree

/-! Explicit polynomial lifts of cubic and quartic relations in z+1/z.
Their coefficients and degree bounds are proved without numerical algebra. -/

namespace Erdos633b
open Polynomial

noncomputable def quarticCosineLift (a : Fin 5 → ℚ) : ℚ[X] :=
  C (a 4) * X ^ 8 + C (a 3) * X ^ 7 + C (a 2 + 4 * a 4) * X ^ 6 +
  C (a 1 + 3 * a 3) * X ^ 5 + C (a 0 + 2 * a 2 + 6 * a 4) * X ^ 4 +
  C (a 1 + 3 * a 3) * X ^ 3 + C (a 2 + 4 * a 4) * X ^ 2 + C (a 3) * X + C (a 4)

noncomputable def cubicCosineLift (a : Fin 4 → ℚ) : ℚ[X] :=
  C (a 3) * X ^ 6 + C (a 2) * X ^ 5 + C (a 1 + 3 * a 3) * X ^ 4 +
  C (a 0 + 2 * a 2) * X ^ 3 + C (a 1 + 3 * a 3) * X ^ 2 + C (a 2) * X + C (a 3)

theorem quarticCosineLift_degree (a : Fin 5 → ℚ) : (quarticCosineLift a).natDegree ≤ 8 := by
  unfold quarticCosineLift
  compute_degree

theorem cubicCosineLift_degree (a : Fin 4 → ℚ) : (cubicCosineLift a).natDegree ≤ 6 := by
  unfold cubicCosineLift
  compute_degree

theorem quarticCosineLift_coeffs_zero (a : Fin 5 → ℚ) (h : quarticCosineLift a = 0) :
    ∀ i, a i = 0 := by
  have h4 : a 4 = 0 := by
    simpa [quarticCosineLift, -map_add, -map_mul]
      using congrArg (fun p : ℚ[X] => p.coeff 8) h
  have h3 : a 3 = 0 := by
    simpa [quarticCosineLift, -map_add, -map_mul]
      using congrArg (fun p : ℚ[X] => p.coeff 7) h
  have h2 : a 2 = 0 := by
    simpa [quarticCosineLift, -map_add, -map_mul, h4]
      using congrArg (fun p : ℚ[X] => p.coeff 6) h
  have h1 : a 1 = 0 := by
    simpa [quarticCosineLift, -map_add, -map_mul, h3]
      using congrArg (fun p : ℚ[X] => p.coeff 5) h
  have h0 : a 0 = 0 := by
    simpa [quarticCosineLift, -map_add, -map_mul, h2, h4]
      using congrArg (fun p : ℚ[X] => p.coeff 4) h
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem cubicCosineLift_coeffs_zero (a : Fin 4 → ℚ) (h : cubicCosineLift a = 0) :
    ∀ i, a i = 0 := by
  have h3 : a 3 = 0 := by
    simpa [cubicCosineLift, -map_add, -map_mul]
      using congrArg (fun p : ℚ[X] => p.coeff 6) h
  have h2 : a 2 = 0 := by
    simpa [cubicCosineLift, -map_add, -map_mul]
      using congrArg (fun p : ℚ[X] => p.coeff 5) h
  have h1 : a 1 = 0 := by
    simpa [cubicCosineLift, -map_add, -map_mul, h3]
      using congrArg (fun p : ℚ[X] => p.coeff 4) h
  have h0 : a 0 = 0 := by
    simpa [cubicCosineLift, -map_add, -map_mul, h2]
      using congrArg (fun p : ℚ[X] => p.coeff 3) h
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem quarticCosineLift_eval (a : Fin 5 → ℚ) (z : ℂ) (hz : z ≠ 0) :
    aeval z (quarticCosineLift a) = z ^ 4 *
      ((a 0 : ℂ) + a 1 * (z + z⁻¹) + a 2 * (z + z⁻¹) ^ 2 +
        a 3 * (z + z⁻¹) ^ 3 + a 4 * (z + z⁻¹) ^ 4) := by
  simp only [quarticCosineLift, map_add, map_mul, map_pow, aeval_C, aeval_X]
  have hcast (q : ℚ) : algebraMap ℚ ℂ q = (q : ℂ) := rfl
  simp only [hcast]
  push_cast
  field_simp [hz]
  ring

theorem cubicCosineLift_eval (a : Fin 4 → ℚ) (z : ℂ) (hz : z ≠ 0) :
    aeval z (cubicCosineLift a) = z ^ 3 *
      ((a 0 : ℂ) + a 1 * (z + z⁻¹) + a 2 * (z + z⁻¹) ^ 2 + a 3 * (z + z⁻¹) ^ 3) := by
  simp only [cubicCosineLift, map_add, map_mul, map_pow, aeval_C, aeval_X]
  have hcast (q : ℚ) : algebraMap ℚ ℂ q = (q : ℂ) := rfl
  simp only [hcast]
  push_cast
  field_simp [hz]
  ring

theorem zero_of_primitive_root_and_small_degree (M : ℕ) (hM : 0 < M) (z : ℂ)
    (hz : IsPrimitiveRoot z M) (g : ℚ[X]) (hg : aeval z g = 0)
    (hdeg : g.natDegree < M.totient) : g = 0 := by
  by_contra hn
  have hd : cyclotomic M ℚ ∣ g := by
    rw [cyclotomic_eq_minpoly_rat hz hM]
    exact minpoly.dvd ℚ z hg
  have hb := Polynomial.natDegree_le_of_dvd hd hn
  rw [natDegree_cyclotomic] at hb
  omega

end Erdos633b
