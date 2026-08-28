import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarSeriesContinuous
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarSeriesMode
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarSeriesRapid
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Differentiation of the constructed Fourier series

The derivative series has a summable, point-independent operator-norm
bound. The ordinary theorem on differentiation of a uniformly convergent
derivative series therefore gives the actual Fréchet derivative of the
continuous synthesis. Its coordinate components are themselves synthesized
from the explicitly differentiated coefficient sequences.
-/

noncomputable section

open UnitAddTorus
open scoped BigOperators

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

/-- The candidate derivative, expressed using actual convergent continuous
Fourier syntheses of the coordinate derivative coefficients. -/
def fourierSynthesisDerivative (c : (Fin 4 → ℤ) → ℂ) (x : Fin 4 → ℝ) :
    (Fin 4 → ℝ) →L[ℝ] ℂ :=
  ∑ j, torusLift (continuousFourierSynthesis (fourierDifferentiatedCoefficients c j)) x •
    fourierCoordinateCLM j

theorem summable_fourierModeDerivative_bound {c : (Fin 4 → ℤ) → ℂ}
    (hc : RapidFourierCoefficients c) :
    Summable (fun k : Fin 4 → ℤ => ∑ j, ‖fourierDifferentiatedCoefficients c j k‖) :=
  summable_sum fun j _ => (hc.differentiated j).norm_summable

theorem fourierSynthesisDerivative_hasSum {c : (Fin 4 → ℤ) → ℂ}
    (hc : RapidFourierCoefficients c) (x : Fin 4 → ℝ) :
    HasSum (fun k => fourierModeDerivative (c k) k x) (fourierSynthesisDerivative c x) := by
  unfold fourierModeDerivative fourierSynthesisDerivative
  apply hasSum_sum
  intro j _
  exact (continuousFourierSynthesis_hasSum_apply
    (fourierDifferentiatedCoefficients c j) (hc.differentiated j).summable
    (torusQuotient x)).smul_const (fourierCoordinateCLM j)

/-- The sum is differentiable with the displayed actual derivative. The
summability and all derivative bounds are derived from the rapid coefficients. -/
theorem hasFDerivAt_continuousFourierSynthesis {c : (Fin 4 → ℤ) → ℂ}
    (hc : RapidFourierCoefficients c) (x : Fin 4 → ℝ) :
    HasFDerivAt (torusLift (continuousFourierSynthesis c))
      (fourierSynthesisDerivative c x) x := by
  have hbase : Summable (fun k => c k * mFourier k (torusQuotient (0 : Fin 4 → ℝ))) :=
    (continuousFourierSynthesis_hasSum_apply c hc.summable
      (torusQuotient (0 : Fin 4 → ℝ))).summable
  have hd := hasFDerivAt_tsum (summable_fourierModeDerivative_bound hc)
    (fun k y => hasFDerivAt_fourierMode (c k) k y)
    (fun k y => fourierModeDerivative_norm_le (c k) k y) hbase x
  have he : (fun y => ∑' k, c k * mFourier k (torusQuotient y)) =
      torusLift (continuousFourierSynthesis c) := by
    funext y
    exact (continuousFourierSynthesis_lift c hc.summable y).symm
  rw [he, (fourierSynthesisDerivative_hasSum hc x).tsum_eq] at hd
  exact hd

theorem fderiv_continuousFourierSynthesis {c : (Fin 4 → ℤ) → ℂ}
    (hc : RapidFourierCoefficients c) :
    fderiv ℝ (torusLift (continuousFourierSynthesis c)) = fourierSynthesisDerivative c := by
  funext x
  exact (hasFDerivAt_continuousFourierSynthesis hc x).fderiv

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
