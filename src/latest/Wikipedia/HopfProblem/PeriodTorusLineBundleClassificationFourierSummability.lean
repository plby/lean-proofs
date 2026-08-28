import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDecay

/-!
# Absolute Fourier summability and reconstruction for smooth torus functions

Rapid decay is proved in the preceding file from actual smoothness. It gives
absolute summability after every polynomial frequency weight, and therefore
Mathlib's actual continuous Fourier series reconstructs the given function.
-/

noncomputable section

open UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

variable {d : Type*} [Fintype d]

/-- All polynomially weighted Fourier coefficients of an actual smooth
torus function are absolutely summable. -/
theorem torusFourierCoeff_polynomial_summable (f : SmoothTorusFunction d) (r : ℕ) :
    Summable (fun k : d → ℤ =>
      (1 + ‖(fun i => (k i : ℝ))‖) ^ r * ‖mFourierCoeff f k‖) := by
  obtain ⟨C, hC, hdecay⟩ := torusFourierCoeff_rapidDecay f (r + 1)
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (by positivity) r) (norm_nonneg _)) ?_
    ((summable_polynomial_mul_inv_fourierEllipticWeight (d := d) r).mul_left C)
  intro k
  calc
    (1 + ‖(fun i => (k i : ℝ))‖) ^ r * ‖mFourierCoeff f k‖ ≤
        (1 + ‖(fun i => (k i : ℝ))‖) ^ r *
          (C / fourierEllipticWeight k ^ (r + 1)) :=
      mul_le_mul_of_nonneg_left (hdecay k) (pow_nonneg (by positivity) r)
    _ = C * ((1 + ‖(fun i => (k i : ℝ))‖) ^ r /
        fourierEllipticWeight k ^ (r + 1)) := by ring

theorem torusFourierCoeff_norm_summable (f : SmoothTorusFunction d) :
    Summable (fun k : d → ℤ => ‖mFourierCoeff f k‖) := by
  simpa only [pow_zero, one_mul] using torusFourierCoeff_polynomial_summable f 0

theorem torusFourierCoeff_summable (f : SmoothTorusFunction d) :
    Summable (mFourierCoeff f) := (torusFourierCoeff_norm_summable f).of_norm

/-- The genuine Fourier series converges to the original continuous map in
its uniform norm; summability is a proved conclusion of smoothness. -/
theorem smoothTorus_hasSum_fourier (f : SmoothTorusFunction d) :
    HasSum (fun k : d → ℤ => mFourierCoeff f k • mFourier k) f.toContinuousMap :=
  hasSum_mFourier_series_of_summable (torusFourierCoeff_summable f)

theorem smoothTorus_hasSum_fourier_apply (f : SmoothTorusFunction d)
    (x : UnitAddTorus d) :
    HasSum (fun k : d → ℤ => mFourierCoeff f k • mFourier k x) (f x) :=
  hasSum_mFourier_series_apply_of_summable (torusFourierCoeff_summable f) x

theorem smoothTorus_fourier_tsum (f : SmoothTorusFunction d) (x : UnitAddTorus d) :
    (∑' k : d → ℤ, mFourierCoeff f k • mFourier k x) = f x :=
  (smoothTorus_hasSum_fourier_apply f x).tsum_eq

/-- In particular the usual polynomially weighted coefficient bounds follow
from actual absolute summability, without an additional decay hypothesis. -/
theorem torusFourierCoeff_rapid_norm (f : SmoothTorusFunction d) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : d → ℤ,
      (1 + ‖(fun i => (k i : ℝ))‖) ^ r * ‖mFourierCoeff f k‖ ≤ C := by
  let a : (d → ℤ) → ℝ := fun k =>
    (1 + ‖(fun i => (k i : ℝ))‖) ^ r * ‖mFourierCoeff f k‖
  have ha : ∀ k, 0 ≤ a k := fun k =>
    mul_nonneg (pow_nonneg (by positivity) r) (norm_nonneg _)
  refine ⟨∑' k, a k, tsum_nonneg ha, fun k => ?_⟩
  exact (torusFourierCoeff_polynomial_summable f r).le_tsum k (fun j _ => ha j)

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
