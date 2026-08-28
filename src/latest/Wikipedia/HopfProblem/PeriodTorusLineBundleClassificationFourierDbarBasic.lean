import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierSummability

/-!
# Rapid coefficient data for the periodic Dolbeault construction

The condition below is weighted absolute summability at every order.
The preceding Fourier family proves it for the actual coefficients of every
smooth torus function. Its elementary norm-domination properties will be used
to prove it for the constructed inverse-symbol coefficients as well.
-/

noncomputable section

open UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

/-- Absolute summability after every polynomial frequency weight. -/
def RapidFourierCoefficients (c : (Fin 4 → ℤ) → ℂ) : Prop :=
  ∀ r : ℕ, Summable (fun k : Fin 4 → ℤ =>
    (1 + ‖(fun i => (k i : ℝ))‖) ^ r * ‖c k‖)

theorem rapidFourierCoefficients_actual (f : SmoothTorusFunction (Fin 4)) :
    RapidFourierCoefficients (mFourierCoeff f) :=
  torusFourierCoeff_polynomial_summable f

theorem RapidFourierCoefficients.norm_summable {c : (Fin 4 → ℤ) → ℂ}
    (hc : RapidFourierCoefficients c) : Summable (fun k => ‖c k‖) := by
  simpa only [pow_zero, one_mul] using hc 0

theorem RapidFourierCoefficients.summable {c : (Fin 4 → ℤ) → ℂ}
    (hc : RapidFourierCoefficients c) : Summable c := hc.norm_summable.of_norm

/-- A uniform norm bound by two rapid sequences proves, rather than assumes,
weighted summability for a newly constructed sequence. -/
theorem rapidFourierCoefficients_of_norm_le_add {a b c : (Fin 4 → ℤ) → ℂ}
    (ha : RapidFourierCoefficients a) (hb : RapidFourierCoefficients b) (C : ℝ)
    (h : ∀ k, ‖c k‖ ≤ C * (‖a k‖ + ‖b k‖)) : RapidFourierCoefficients c := by
  intro r
  apply (((ha r).add (hb r)).mul_left C).of_nonneg_of_le
  · intro k
    exact mul_nonneg (pow_nonneg (by positivity) r) (norm_nonneg _)
  · intro k
    calc
      (1 + ‖(fun i => (k i : ℝ))‖) ^ r * ‖c k‖ ≤
          (1 + ‖(fun i => (k i : ℝ))‖) ^ r * (C * (‖a k‖ + ‖b k‖)) :=
        mul_le_mul_of_nonneg_left (h k) (pow_nonneg (by positivity) r)
      _ = C * ((1 + ‖(fun i => (k i : ℝ))‖) ^ r * ‖a k‖ +
          (1 + ‖(fun i => (k i : ℝ))‖) ^ r * ‖b k‖) := by ring

theorem rapidFourierCoefficients_zero :
    RapidFourierCoefficients (fun _ : Fin 4 → ℤ => (0 : ℂ)) := by
  intro r
  simp

theorem RapidFourierCoefficients.add {a b : (Fin 4 → ℤ) → ℂ}
    (ha : RapidFourierCoefficients a) (hb : RapidFourierCoefficients b) :
    RapidFourierCoefficients (fun k => a k + b k) := by
  apply rapidFourierCoefficients_of_norm_le_add ha hb 1
  intro k
  simpa only [one_mul] using norm_add_le (a k) (b k)

theorem RapidFourierCoefficients.const_mul {a : (Fin 4 → ℤ) → ℂ}
    (ha : RapidFourierCoefficients a) (c : ℂ) :
    RapidFourierCoefficients (fun k => c * a k) := by
  apply rapidFourierCoefficients_of_norm_le_add ha rapidFourierCoefficients_zero ‖c‖
  intro k
  simp only [norm_mul, norm_zero, add_zero, le_refl]

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
