import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarSeriesContinuous
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarCoefficient

/-!
# Recovery of the supplied Fourier coefficients

The genuine bounded Fourier coefficient functional commutes with the
convergent Banach-space series.  Orthogonality of the actual monomials then
recovers the original coefficient sequence.
-/

noncomputable section

open UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

theorem mFourierCoeff_continuousFourierSynthesis (c : (Fin 4 → ℤ) → ℂ)
    (hc : Summable c) (k : Fin 4 → ℤ) :
    mFourierCoeff (continuousFourierSynthesis c) k = c k := by
  change torusFourierCoeffCLM k (∑' m, c m • mFourier m) = c k
  rw [(torusFourierCoeffCLM k).map_tsum (summable_continuousFourierModes c hc)]
  simp only [map_smul, torusFourierCoeffCLM_apply, mFourierCoeff_mFourier,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
