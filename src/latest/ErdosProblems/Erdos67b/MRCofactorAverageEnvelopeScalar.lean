import ErdosProblems.Erdos67b.MRCofactorDistanceEnvelope
import ErdosProblems.Erdos67b.MRGSRiemannZetaUpper

/-! # One-pole scalar size of the averaged cofactor envelope -/

namespace Erdos67b

open MRHalaszBands EulerResidue EulerQuantitative

noncomputable section

def mrCofactorEulerBaseConstant : ℝ :=
  Real.exp (6 * gsA9WideSourceShiftConstant + 3 * primeQuadraticConstant + mrMaskProductSeries)

def mrCofactorAverageEnvelopeConstant : ℝ := 32 * Real.exp 1 * mrCofactorEulerBaseConstant

theorem mrCofactorEulerBase_le {X : ℕ} (hX : 1 < X) :
    mrCofactorEulerBase X ≤ mrCofactorEulerBaseConstant * (1 + Real.log (X : ℝ)) := by
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  have hζ : ‖riemannZeta (taoExponent X : ℂ)‖ ≤ 1 + Real.log (X : ℝ) := by
    have h := norm_riemannZeta_real_le_one_add_inv (inv_pos.mpr hlogX)
    simpa [taoExponent] using h
  have hexp : Real.exp (Real.log (riemannZeta (taoExponent X : ℂ)).re) ≤ 1 + Real.log (X : ℝ) := by
    by_cases hz : (riemannZeta (taoExponent X : ℂ)).re = 0
    · simp only [hz, Real.log_zero, Real.exp_zero]
      linarith
    · rw [Real.exp_log_eq_abs hz]
      exact (Complex.abs_re_le_norm _).trans hζ
  have hsplit : mrCofactorEulerBase X = mrCofactorEulerBaseConstant *
      Real.exp (Real.log (riemannZeta (taoExponent X : ℂ)).re) := by
    unfold mrCofactorEulerBase mrCofactorEulerBaseConstant
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le

theorem mrCofactorAverageEnvelope_le {N X : ℕ} (hN : 0 < N) (hX : 1 < X) :
    mrCofactorAverageEnvelope N X ≤
      mrCofactorAverageEnvelopeConstant * (1 + Real.log (X : ℝ)) / N := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hidentity : ((Real.exp (-1) / 16) * ((N : ℝ) / 2))⁻¹ = 32 * Real.exp 1 / N := by
    rw [Real.exp_neg]
    field_simp
    norm_num
  unfold mrCofactorAverageEnvelope
  rw [hidentity]
  calc
    _ ≤ (mrCofactorEulerBaseConstant * (1 + Real.log (X : ℝ))) * (32 * Real.exp 1 / N) :=
      mul_le_mul_of_nonneg_right (mrCofactorEulerBase_le hX) (by positivity)
    _ = _ := by unfold mrCofactorAverageEnvelopeConstant; ring

theorem mrCofactorAverageEnvelope_le_log {N X : ℕ} (hN : 0 < N) (hX : 1 < X)
    (hlogX : 1 ≤ Real.log (X : ℝ)) :
    mrCofactorAverageEnvelope N X ≤
      2 * mrCofactorAverageEnvelopeConstant * Real.log (X : ℝ) / N := by
  apply (mrCofactorAverageEnvelope_le hN hX).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have hC : 0 ≤ mrCofactorAverageEnvelopeConstant := by
    unfold mrCofactorAverageEnvelopeConstant mrCofactorEulerBaseConstant
    positivity
  calc
    _ ≤ mrCofactorAverageEnvelopeConstant * (2 * Real.log (X : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC
    _ = _ := by ring

end

end Erdos67b
