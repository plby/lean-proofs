import ErdosProblems.Erdos633b.QuadraticConicLifts

/-! Cubic conic lifts of degree six, with exact coefficient recovery
and sixth-root evaluation identities. -/

namespace Erdos633b
open Polynomial

def conicQuadraticPrefix (a : Fin 7 → ℚ) : Fin 5 → ℚ := ![a 0, a 1, a 2, a 3, a 4]

noncomputable def cubicConicLift0 (a : Fin 7 → ℚ) : ℚ[X] :=
  X * (-quadraticConicLift0 (conicQuadraticPrefix a) -
    2 * quadraticConicLift1 (conicQuadraticPrefix a)) +
  C (a 5) * (X ^ 2 - 1) ^ 3 - C (a 6) * X ^ 2 * (X ^ 2 - 1) ^ 2

noncomputable def cubicConicLift1 (a : Fin 7 → ℚ) : ℚ[X] :=
  X * (2 * quadraticConicLift0 (conicQuadraticPrefix a) +
    quadraticConicLift1 (conicQuadraticPrefix a)) +
  C (a 6) * (X ^ 2 - 1) ^ 2 * (1 + X ^ 2)

theorem cubicConicLift0_degree (a : Fin 7 → ℚ) : (cubicConicLift0 a).natDegree ≤ 6 := by
  unfold cubicConicLift0 quadraticConicLift0 quadraticConicLift1
  compute_degree

theorem cubicConicLift1_degree (a : Fin 7 → ℚ) : (cubicConicLift1 a).natDegree ≤ 6 := by
  unfold cubicConicLift1 quadraticConicLift0 quadraticConicLift1
  compute_degree

theorem cubicConicLifts_coeffs_zero (a : Fin 7 → ℚ)
    (h0 : cubicConicLift0 a = 0) (h1 : cubicConicLift1 a = 0) : ∀ i, a i = 0 := by
  have h5 : a 5 = 0 := by
    simpa [cubicConicLift0] using congrArg (fun p : ℚ[X] => p.eval 0) h0
  have h6 : a 6 = 0 := by
    simpa [cubicConicLift1] using congrArg (fun p : ℚ[X] => p.eval 0) h1
  have hp : -quadraticConicLift0 (conicQuadraticPrefix a) -
      2 * quadraticConicLift1 (conicQuadraticPrefix a) = 0 := by
    have hh : X * (-quadraticConicLift0 (conicQuadraticPrefix a) -
        2 * quadraticConicLift1 (conicQuadraticPrefix a)) = 0 := by
      simpa [cubicConicLift0, h5, h6] using h0
    exact (mul_eq_zero.mp hh).resolve_left X_ne_zero
  have hq : 2 * quadraticConicLift0 (conicQuadraticPrefix a) +
      quadraticConicLift1 (conicQuadraticPrefix a) = 0 := by
    have hh : X * (2 * quadraticConicLift0 (conicQuadraticPrefix a) +
        quadraticConicLift1 (conicQuadraticPrefix a)) = 0 := by
      simpa [cubicConicLift1, h6] using h1
    exact (mul_eq_zero.mp hh).resolve_left X_ne_zero
  have hp0 : quadraticConicLift0 (conicQuadraticPrefix a) = 0 := by
    have hh : (3 : ℚ[X]) * quadraticConicLift0 (conicQuadraticPrefix a) = 0 := by
      linear_combination hp + 2 * hq
    exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
  have hp1 : quadraticConicLift1 (conicQuadraticPrefix a) = 0 := by
    have hh : (3 : ℚ[X]) * quadraticConicLift1 (conicQuadraticPrefix a) = 0 := by
      linear_combination -2 * hp - hq
    exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
  have hpre := quadraticConicLifts_coeffs_zero (conicQuadraticPrefix a) hp0 hp1
  intro i
  fin_cases i
  · exact hpre 0
  · exact hpre 1
  · exact hpre 2
  · exact hpre 3
  · exact hpre 4
  · exact h5
  · exact h6

theorem cubicConicLifts_eval (a : Fin 7 → ℚ) (z ω : ℂ) (hω : ω ^ 2 - ω + 1 = 0) :
    aeval z (cubicConicLift0 a) + ω * aeval z (cubicConicLift1 a) =
      (2 * ω - 1) * z * (aeval z (quadraticConicLift0 (conicQuadraticPrefix a)) +
        ω * aeval z (quadraticConicLift1 (conicQuadraticPrefix a))) +
      (a 5 : ℂ) * (z ^ 2 - 1) ^ 3 +
      a 6 * (z ^ 2 - 1) ^ 2 * (ω * (1 + z ^ 2) - z ^ 2) := by
  simp only [cubicConicLift0, cubicConicLift1, map_add, map_sub, map_mul, map_pow,
    map_neg, map_ofNat, map_one, aeval_C, aeval_X]
  have hcast (q : ℚ) : algebraMap ℚ ℂ q = (q : ℂ) := rfl
  simp only [hcast]
  linear_combination -2 * z * aeval z (quadraticConicLift1 (conicQuadraticPrefix a)) * hω

theorem cubicConicLifts_eval_coordinates (a : Fin 7 → ℚ) (z ω x y : ℂ)
    (hω : ω ^ 2 - ω + 1 = 0)
    (hx : (2 * ω - 1) * z * x = z ^ 2 - 1)
    (hy : (2 * ω - 1) * z * y = ω * (1 + z ^ 2) - z ^ 2) :
    aeval z (cubicConicLift0 a) + ω * aeval z (cubicConicLift1 a) =
      (2 * ω - 1) ^ 3 * z ^ 3 * ((a 0 : ℂ) + a 1 * x + a 2 * y +
        a 3 * x ^ 2 + a 4 * x * y + a 5 * x ^ 3 + a 6 * x ^ 2 * y) := by
  rw [cubicConicLifts_eval a z ω hω,
    quadraticConicLifts_eval_coordinates (conicQuadraticPrefix a) z ω x y hω hx hy,
    ← hx, ← hy]
  dsimp [conicQuadraticPrefix]
  ring

end Erdos633b
