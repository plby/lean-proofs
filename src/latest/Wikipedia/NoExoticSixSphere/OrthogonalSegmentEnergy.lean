import Wikipedia.NoExoticSixSphere.OrthogonalPathEnergy

/-!
# Energy of a time-rescaled exponential segment

The actual ambient derivative gives the usual squared-increment divided by
time-length formula. The derivative statement also covers a degenerate interval,
with Lean's zero-division convention giving a constant segment in that case.
-/

namespace NoExoticSixSphere.OrthogonalPathEnergy

open GLOrthonormalization CayleyTransform OrthogonalExponential HilbertSchmidt

variable {n : ℕ}

noncomputable def rescaledSegment (a : OrthogonalOperators n) (K : SkewOperators n)
    (s u t : ℝ) : OrthogonalOperators n := a * exp (((t - s) / (u - s)) • K)

theorem rescaledSegment_start (a : OrthogonalOperators n) (K : SkewOperators n) (s u : ℝ) :
    rescaledSegment a K s u s = a := by
  simp only [rescaledSegment, sub_self, zero_div, zero_smul, exp_zero, mul_one]

theorem rescaledSegment_end (a : OrthogonalOperators n) (K : SkewOperators n) (s u : ℝ)
    (hsu : s ≠ u) : rescaledSegment a K s u u = a * exp K := by
  rw [rescaledSegment, div_self (sub_ne_zero.mpr (Ne.symm hsu)), one_smul]

theorem hasDerivAt_rescaledSegment (a : OrthogonalOperators n) (K : SkewOperators n)
    (s u t : ℝ) :
    HasDerivAt (fun r : ℝ ↦ (rescaledSegment a K s u r).1.1)
      ((1 / (u - s)) • a.1.1.comp
        ((exp (((t - s) / (u - s)) • K)).1.1.comp (K : Vector n →L[ℝ] Vector n))) t := by
  have ht : HasDerivAt (fun r : ℝ ↦ (r - s) / (u - s)) (1 / (u - s)) t :=
    ((hasDerivAt_id t).sub_const s).div_const (u - s)
  exact HasDerivAt.scomp (g₁ := fun r : ℝ ↦ (a * exp (r • K)).1.1)
    (h := fun r : ℝ ↦ (r - s) / (u - s)) t
    (hasDerivAt_left_exp a K ((t - s) / (u - s))) ht

theorem deriv_rescaledSegment (a : OrthogonalOperators n) (K : SkewOperators n) (s u t : ℝ) :
    deriv (fun r : ℝ ↦ (rescaledSegment a K s u r).1.1) t =
      (1 / (u - s)) • a.1.1.comp
        ((exp (((t - s) / (u - s)) • K)).1.1.comp (K : Vector n →L[ℝ] Vector n)) :=
  (hasDerivAt_rescaledSegment a K s u t).deriv

theorem squareNorm_deriv_rescaledSegment (a : OrthogonalOperators n) (K : SkewOperators n)
    (s u t : ℝ) :
    squareNorm (deriv (fun r : ℝ ↦ (rescaledSegment a K s u r).1.1) t) =
      (1 / (u - s)) ^ 2 * squareNorm (K : Vector n →L[ℝ] Vector n) := by
  rw [deriv_rescaledSegment, squareNorm_smul, squareNorm_left, squareNorm_left]

/-- Energy of the rescaled segment on its defining time interval. -/
theorem energy_rescaledSegment (a : OrthogonalOperators n) (K : SkewOperators n) (s u : ℝ) :
    energy (fun r : ℝ ↦ (rescaledSegment a K s u r).1.1) s u =
      squareNorm (K : Vector n →L[ℝ] Vector n) / (u - s) := by
  unfold energy
  simp only [squareNorm_deriv_rescaledSegment, intervalIntegral.integral_const, smul_eq_mul]
  by_cases h : u - s = 0
  · simp [h]
  · field_simp

end NoExoticSixSphere.OrthogonalPathEnergy
