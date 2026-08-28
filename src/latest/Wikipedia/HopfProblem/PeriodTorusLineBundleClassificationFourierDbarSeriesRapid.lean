import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarBasic

/-!
# Rapid decay is preserved by coordinate differentiation

Multiplication by a coordinate frequency costs exactly one polynomial
weight.  Thus the actual differentiated coefficient sequence is again
rapid, a fact used to prove smoothness of the synthesized series.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

/-- The exact coordinate multiplier for real Fourier differentiation. -/
def fourierDifferentiatedCoefficients (c : (Fin 4 → ℤ) → ℂ) (j : Fin 4)
    (k : Fin 4 → ℤ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) * c k

theorem RapidFourierCoefficients.differentiated {c : (Fin 4 → ℤ) → ℂ}
    (hc : RapidFourierCoefficients c) (j : Fin 4) :
    RapidFourierCoefficients (fourierDifferentiatedCoefficients c j) := by
  intro r
  apply ((hc (r + 1)).mul_left ‖2 * (Real.pi : ℂ) * Complex.I‖).of_nonneg_of_le
  · intro k
    exact mul_nonneg (pow_nonneg (by positivity) r) (norm_nonneg _)
  · intro k
    have hcoord : ‖(k j : ℂ)‖ ≤ 1 + ‖(fun i => (k i : ℝ))‖ := by
      calc
        ‖(k j : ℂ)‖ = ‖(k j : ℝ)‖ := by
          rw [← Complex.ofReal_intCast, Complex.norm_real]
        _ ≤ ‖(fun i => (k i : ℝ))‖ := norm_le_pi_norm (fun i => (k i : ℝ)) j
        _ ≤ 1 + ‖(fun i => (k i : ℝ))‖ := le_add_of_nonneg_left zero_le_one
    calc
      (1 + ‖(fun i => (k i : ℝ))‖) ^ r *
          ‖fourierDifferentiatedCoefficients c j k‖ =
        (‖2 * (Real.pi : ℂ) * Complex.I‖ *
          (1 + ‖(fun i => (k i : ℝ))‖) ^ r * ‖c k‖) * ‖(k j : ℂ)‖ := by
            simp only [fourierDifferentiatedCoefficients, norm_mul]
            ring
      _ ≤ (‖2 * (Real.pi : ℂ) * Complex.I‖ *
          (1 + ‖(fun i => (k i : ℝ))‖) ^ r * ‖c k‖) *
            (1 + ‖(fun i => (k i : ℝ))‖) :=
        mul_le_mul_of_nonneg_left hcoord (by positivity)
      _ = ‖2 * (Real.pi : ℂ) * Complex.I‖ *
          ((1 + ‖(fun i => (k i : ℝ))‖) ^ (r + 1) * ‖c k‖) := by
        rw [pow_succ]
        ring

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
