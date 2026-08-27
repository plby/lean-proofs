import ErdosProblems.Erdos587.HooleySmoothQuadratic

/-! # Conjugation of the full smooth quadratic sum -/

open scoped SchwartzMap ComplexConjugate

namespace Erdos587

lemma deltaSmoothQuadraticSum_conjugate (f : 𝓢(ℝ, ℂ)) (K α θ : ℝ) :
    deltaSmoothQuadraticSum (conjugateSchwartz f) K (-α) (-θ) =
      conj (deltaSmoothQuadraticSum f K α θ) := by
  unfold deltaSmoothQuadraticSum
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro n
  rw [map_mul (starRingEnd ℂ), ← phase_neg, conjugateSchwartz_apply]
  congr 1
  congr 1
  ring

lemma deltaSmoothQuadraticSum_norm_negative (f : 𝓢(ℝ, ℂ)) (K α θ : ℝ) :
    ‖deltaSmoothQuadraticSum f K (-α) θ‖ =
      ‖deltaSmoothQuadraticSum (conjugateSchwartz f) K α (-θ)‖ := by
  have h := deltaSmoothQuadraticSum_conjugate f K (-α) θ
  rw [neg_neg] at h
  rw [h, Complex.norm_conj]

end Erdos587
