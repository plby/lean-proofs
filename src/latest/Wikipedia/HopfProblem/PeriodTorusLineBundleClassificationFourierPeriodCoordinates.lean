import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierPeriod
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationDbarPlane
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# The actual coordinate Dolbeault operator on transported torus functions

The coordinate-update definition of the antiholomorphic derivative is
identified with its real Fréchet formula. Consequently the genuine torus
operator, and not merely a formal multiplier, agrees with the coordinate
operator on the complex period cover.
-/

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open Complex HolomorphicCousin
open scoped ContDiff

/-- The literal coordinate-slice antiholomorphic derivative has the expected
real Fréchet formula at every point of real differentiability. -/
theorem dbarCoordinate_eq_fderiv {f : ComplexPlane₂ → ℂ} {z : ComplexPlane₂}
    (hf : DifferentiableAt ℝ f z) (i : Fin 2) :
    dbarCoordinate f i z =
      (fderiv ℝ f z (Pi.single i 1) +
        I * fderiv ℝ f z (I • Pi.single i 1)) / 2 := by
  have hf' : HasFDerivAt f (fderiv ℝ f z) (Function.update z i (z i)) := by
    simpa using hf.hasFDerivAt
  have he := (hf'.comp (z i) (hasFDerivAt_update (𝕜 := ℝ) z (z i))).fderiv
  change fderiv ℝ (fun w => f (Function.update z i w)) (z i) = _ at he
  have hsingle (w : ℂ) :
      ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℂ)) w =
        (Pi.single i w : ComplexPlane₂) := by
    ext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  have hi : Pi.single i I = I • (Pi.single i 1 : ComplexPlane₂) := by
    ext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  simp only [dbarCoordinate, dbar, he, ContinuousLinearMap.comp_apply, hsingle, hi]

/-- The genuine torus Dolbeault operator lifts to the actual coordinate
antiholomorphic derivative on the complex covering plane. -/
theorem dbarCoordinate_periodTorusLift (p : PeriodDomain)
    (f : SmoothTorusFunction (Fin 4)) (i : Fin 2) (z : ComplexPlane₂) :
    dbarCoordinate (periodTorusLift p f) i z = periodTorusLift p (torusDbar p f i) z := by
  rw [dbarCoordinate_eq_fderiv
    ((contDiff_periodTorusLift p f).differentiable (by simp) z)]
  exact (periodTorusLift_torusDbar p f i z).symm

/-- The actual coordinate derivative of an exponential mode has the proved
Dolbeault symbol, with the same sign and normalization as the torus operator. -/
theorem dbarCoordinate_frequencyMode (p : PeriodDomain) (v : Fin 4 → ℝ)
    (i : Fin 2) (z : ComplexPlane₂) :
    dbarCoordinate (frequencyMode p v) i z =
      dolbeaultSymbol p v i * frequencyMode p v z := by
  rw [dbarCoordinate_eq_fderiv (frequencyMode_hasFDerivAt p v z).differentiableAt]
  exact frequencyMode_dbar p v z i

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
