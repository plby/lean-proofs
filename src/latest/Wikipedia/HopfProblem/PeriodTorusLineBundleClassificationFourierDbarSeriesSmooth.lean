import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarSeriesDerivative
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarSeriesCoefficient

/-!
# Smooth synthesis of rapid Fourier coefficients

Smoothness is proved by induction on the differentiability order. At each
step the actual derivative is a finite linear combination of syntheses of
rapid coefficient sequences, so the induction applies. No smoothness of
the infinite series is assumed.
-/

noncomputable section

open UnitAddTorus
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

theorem contDiff_nat_continuousFourierSynthesis (n : ℕ)
    (c : (Fin 4 → ℤ) → ℂ) (hc : RapidFourierCoefficients c) :
    ContDiff ℝ n (torusLift (continuousFourierSynthesis c)) := by
  induction n generalizing c with
  | zero =>
      exact contDiff_zero.mpr
        ((continuousFourierSynthesis c).continuous.comp torusQuotient_continuous)
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_hasFDerivAt]
      refine ⟨fourierSynthesisDerivative c, ?_,
        hasFDerivAt_continuousFourierSynthesis hc⟩
      unfold fourierSynthesisDerivative
      apply ContDiff.sum
      intro j _
      exact (ih (fourierDifferentiatedCoefficients c j) (hc.differentiated j)).smul_const
        (fourierCoordinateCLM j)

theorem contDiff_continuousFourierSynthesis (c : (Fin 4 → ℤ) → ℂ)
    (hc : RapidFourierCoefficients c) :
    ContDiff ℝ ∞ (torusLift (continuousFourierSynthesis c)) :=
  contDiff_infty.mpr fun n => contDiff_nat_continuousFourierSynthesis n c hc

/-- The actual smooth torus function constructed from rapid coefficients. -/
def smoothFourierSynthesis (c : (Fin 4 → ℤ) → ℂ) (hc : RapidFourierCoefficients c) :
    SmoothTorusFunction (Fin 4) where
  toContinuousMap := continuousFourierSynthesis c
  smooth_lift := contDiff_continuousFourierSynthesis c hc

@[simp]
theorem smoothFourierSynthesis_apply (c : (Fin 4 → ℤ) → ℂ)
    (hc : RapidFourierCoefficients c) (x : UnitAddTorus (Fin 4)) :
    smoothFourierSynthesis c hc x = continuousFourierSynthesis c x := rfl

/-- The actual Fourier coefficient of the constructed smooth sum is the
supplied coefficient, by the proved Banach-space synthesis identity. -/
theorem mFourierCoeff_smoothFourierSynthesis (c : (Fin 4 → ℤ) → ℂ)
    (hc : RapidFourierCoefficients c) (k : Fin 4 → ℤ) :
    mFourierCoeff (smoothFourierSynthesis c hc) k = c k :=
  mFourierCoeff_continuousFourierSynthesis c hc.summable k

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
