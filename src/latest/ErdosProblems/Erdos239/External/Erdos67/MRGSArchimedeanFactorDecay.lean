import ErdosProblems.Erdos239.External.Erdos67.MRGSLemma71PrefixRenormalization

/-!
# Decay of the GS Archimedean prefix factor

The factor in equation (A.8) has modulus comparable to
`(1 + |u|)⁻¹`.  This module records a convenient explicit upper bound and
the elementary norm bridge used after the central A.9 estimate.
-/

namespace Erdos67

noncomputable section

/-- The denominator `1 - iu` dominates half of `1 + |u|`. -/
theorem one_add_abs_le_two_mul_norm_one_sub_I_mul (u : ℝ) :
    1 + |u| ≤ 2 * ‖(1 : ℂ) - Complex.I * (u : ℂ)‖ := by
  have hnormSq :
      ‖(1 : ℂ) - Complex.I * (u : ℂ)‖ ^ 2 = 1 + u ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    norm_num
    ring
  have habsSq : |u| ^ 2 = u ^ 2 := sq_abs u
  have hsmall :
      (1 + |u|) ^ 2 ≤
        (2 * ‖(1 : ℂ) - Complex.I * (u : ℂ)‖) ^ 2 := by
    rw [mul_pow, hnormSq]
    nlinarith [habsSq, sq_nonneg (|u| - 1), sq_nonneg u]
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsmall

/-- Explicit reciprocal decay of the GS Archimedean factor. -/
theorem norm_gsPrefixArchimedeanFactor_le_two_div_one_add_abs
    (u : ℝ) {N : ℕ} (hN : 0 < N) :
    ‖gsPrefixArchimedeanFactor u N‖ ≤ 2 / (1 + |u|) := by
  unfold gsPrefixArchimedeanFactor
  rw [norm_div, LogPhaseSum.norm_natLogTwist u hN]
  have hden : 0 < ‖(1 : ℂ) - Complex.I * (u : ℂ)‖ := by
    rw [norm_pos_iff]
    intro hz
    have hre := congrArg Complex.re hz
    norm_num at hre
  have hone : 0 < 1 + |u| := by positivity
  apply (div_le_div_iff₀ hden hone).2
  simpa only [one_mul] using one_add_abs_le_two_mul_norm_one_sub_I_mul u

/-- A renormalization estimate and a central mean bound give the reciprocal
pointwise shape used in the GS energy argument. -/
theorem norm_le_two_mul_inv_one_add_abs_mul_add_of_renormalized
    {Z A C : ℂ} {u E D : ℝ}
    (_hD : 0 ≤ D) (_hE : 0 ≤ E)
    (hA : ‖A‖ ≤ 2 / (1 + |u|))
    (hC : ‖C‖ ≤ E) (hrenorm : ‖Z - A * C‖ ≤ D) :
    ‖Z‖ ≤ 2 * E * (1 + |u|)⁻¹ + D := by
  have hden : 0 < 1 + |u| := by positivity
  have hA0 : 0 ≤ 2 / (1 + |u|) := by positivity
  calc
    ‖Z‖ = ‖(Z - A * C) + A * C‖ := by ring_nf
    _ ≤ ‖Z - A * C‖ + ‖A * C‖ := norm_add_le _ _
    _ ≤ D + (2 / (1 + |u|)) * E := by
      rw [norm_mul]
      gcongr
    _ = 2 * E * (1 + |u|)⁻¹ + D := by
      rw [div_eq_mul_inv]
      ring

/-- At zero displacement the normalized twisted prefix is exactly the
central untwisted prefix mean. -/
theorem gsTwistedPositivePrefixSum_div_eq_positivePrefixMean_archimedeanUntwist
    (f : ℕ → ℂ) (t : ℝ) {N : ℕ} (_hN : 0 < N) :
    gsTwistedPositivePrefixSum f t N / (N : ℂ) =
      positivePrefixMean (archimedeanUntwist f t) N := by
  let a : ℕ → ℂ := archimedeanUntwist f t
  have htwist := gsTwistedPositivePrefixSum_archimedeanUntwist_add f t 0 N
  have hzero : gsTwistedPositivePrefixSum a 0 N = positivePrefixSum a N := by
    unfold gsTwistedPositivePrefixSum
    have hphase :
        (∑ n ∈ Finset.Ioc 0 N, a n * LogPhaseSum.natLogTwist n 0) =
          ∑ n ∈ Finset.Ioc 0 N, a n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnpos : 0 < n := (Finset.mem_Ioc.mp hn).1
      simp [LogPhaseSum.natLogTwist, LogPhaseSum.logPhase]
    rw [hphase]
    have hsum := sum_Ioc_eq_positivePrefixSum_sub a (Nat.zero_le N)
    simpa [positivePrefixSum] using hsum
  rw [add_zero] at htwist
  rw [← htwist]
  change gsTwistedPositivePrefixSum a 0 N / (N : ℂ) =
    positivePrefixMean a N
  rw [hzero]
  rfl

/-- Uniform pointwise bridge including the zero displacement: A.9 controls
the central mean and A.8 is only needed when `u ≠ 0`. -/
theorem norm_normalized_twistedPrefix_le_reciprocal_add_of_centered
    (f : ℕ → ℂ) (t₁ u : ℝ) {N : ℕ} (hN : 0 < N)
    {E D : ℝ} (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hcentral : ‖positivePrefixMean (archimedeanUntwist f t₁) N‖ ≤ E)
    (hrenorm : u ≠ 0 →
      ‖gsTwistedPositivePrefixSum f (t₁ + u) N / (N : ℂ) -
          gsPrefixArchimedeanFactor u N *
            positivePrefixMean (archimedeanUntwist f t₁) N‖ ≤ D) :
    ‖gsTwistedPositivePrefixSum f (t₁ + u) N / (N : ℂ)‖ ≤
      2 * E * (1 + |u|)⁻¹ + D := by
  by_cases hu : u = 0
  · subst u
    rw [add_zero,
      gsTwistedPositivePrefixSum_div_eq_positivePrefixMean_archimedeanUntwist
        f t₁ hN]
    norm_num
    linarith
  · exact norm_le_two_mul_inv_one_add_abs_mul_add_of_renormalized
      hD hE (norm_gsPrefixArchimedeanFactor_le_two_div_one_add_abs u hN)
      hcentral (hrenorm hu)

end

end Erdos67
