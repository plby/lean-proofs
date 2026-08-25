import ErdosProblems.Erdos67.MRGSLemma71RealPrefix
import ErdosProblems.Erdos67.MRGSTwoBlockDeletion

/-!
# Prefix form of the finite GS renormalization

The convolution statement in `MRGSLemma71` initially produces a reciprocal
Möbius main term.  The same finite convolution identity at twist zero shows
that this reciprocal main differs from the ordinary normalized prefix by at
most one Halberstam--Richert partial sum divided by the prefix length.
Combining the two estimates gives the exact prefix-to-prefix form of the GS
renormalization on the currently formalized range `|t| ≤ 1`.

This is the finite algebraic part of source equation (A.8).  Extending the
range to `|t| ≤ log(X)^(1/16)` requires the sharper logarithmic power-sum
estimate from GS Lemma 7.1 and is deliberately not asserted here.
-/

open scoped BigOperators
open Finset

namespace Erdos67

noncomputable section

/-- The reciprocal Möbius main differs from the normalized prefix only by
the accumulated floor errors. -/
theorem norm_positivePrefixMean_sub_gsReciprocalMoebiusSum_le
    (f : ℕ → ℂ) {N : ℕ} (hN : 0 < N) :
    ‖positivePrefixMean f N - gsReciprocalMoebiusSum f N‖ ≤
      (1 / (N : ℝ)) *
        HalberstamScratch.partialSum (gsMoebiusNorm f) N := by
  rw [positivePrefixMean_eq_sum_Ioc_gsMoebius_mul_floorRatio f hN]
  unfold gsReciprocalMoebiusSum
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ d ∈ Finset.Ioc 0 N,
        (gsMoebiusCoefficient f d * gsFloorRatio N d -
          gsMoebiusCoefficient f d / (d : ℂ))‖ ≤
        ∑ d ∈ Finset.Ioc 0 N,
          ‖gsMoebiusCoefficient f d * gsFloorRatio N d -
            gsMoebiusCoefficient f d / (d : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Ioc 0 N,
        gsMoebiusNorm f d * (1 / (N : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Ioc.mp hd).1
      rw [div_eq_mul_inv, ← mul_sub, norm_mul, gsMoebiusNorm]
      exact mul_le_mul_of_nonneg_left
        (norm_gsFloorRatio_sub_inv_le hN hdpos) (norm_nonneg _)
    _ = (1 / (N : ℝ)) *
        HalberstamScratch.partialSum (gsMoebiusNorm f) N := by
      unfold HalberstamScratch.partialSum
      have hset : Finset.Ioc 0 N = Finset.Icc 1 N := by
        ext n
        simp only [Finset.mem_Ioc, Finset.mem_Icc]
        omega
      rw [hset, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      ring

/-- The Archimedean factor occurring in the source prefix renormalization. -/
def gsPrefixArchimedeanFactor (t : ℝ) (N : ℕ) : ℂ :=
  LogPhaseSum.natLogTwist N t /
    (1 - Complex.I * (t : ℂ))

theorem archimedeanUntwist_mul_natLogTwist_add
    (f : ℕ → ℂ) (t u : ℝ) {n : ℕ} (hn : 0 < n) :
    archimedeanUntwist f t n * LogPhaseSum.natLogTwist n u =
      f n * LogPhaseSum.natLogTwist n (t + u) := by
  rw [archimedeanUntwist, if_neg hn.ne', conj_archimedeanTwist]
  unfold LogPhaseSum.natLogTwist LogPhaseSum.logPhase
  rw [Complex.ofReal_natCast]
  rw [mul_assoc, ← Complex.cpow_add _ _ (by exact_mod_cast hn.ne')]
  congr 2
  push_cast
  ring

theorem gsTwistedPositivePrefixSum_archimedeanUntwist_add
    (f : ℕ → ℂ) (t u : ℝ) (N : ℕ) :
    gsTwistedPositivePrefixSum (archimedeanUntwist f t) u N =
      gsTwistedPositivePrefixSum f (t + u) N := by
  unfold gsTwistedPositivePrefixSum
  apply Finset.sum_congr rfl
  intro n hn
  exact archimedeanUntwist_mul_natLogTwist_add f t u
    (Finset.mem_Ioc.mp hn).1

theorem norm_gsPrefixArchimedeanFactor_le_one
    (t : ℝ) {N : ℕ} (hN : 0 < N) :
    ‖gsPrefixArchimedeanFactor t N‖ ≤ 1 := by
  unfold gsPrefixArchimedeanFactor
  rw [norm_div, LogPhaseSum.norm_natLogTwist t hN]
  apply (div_le_one (norm_pos_iff.mpr ?_)).2
  · rw [Complex.norm_def]
    apply (Real.le_sqrt zero_le_one (Complex.normSq_nonneg _)).2
    rw [Complex.normSq_apply]
    norm_num
    nlinarith [sq_nonneg t]
  · intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre

/-- GS Lemma 7.1 in prefix-to-prefix form, normalized by `N`.  This is the
formalized small-window version of source equation (A.8). -/
theorem norm_normalized_gsTwistedPrefix_sub_archimedeanFactor_mul_prefixMean_le
    (f : ℕ → ℂ) (t : ℝ) {N : ℕ} (hN : 0 < N)
    (ht : t ≠ 0) (ht_small : |t| ≤ 1) :
    ‖gsTwistedPositivePrefixSum f t N / (N : ℂ) -
        gsPrefixArchimedeanFactor t N * positivePrefixMean f N‖ ≤
      (5 / (N : ℝ)) *
        HalberstamScratch.partialSum (gsMoebiusNorm f) N := by
  let R : ℂ := gsReciprocalMoebiusSum f N
  let A : ℂ := gsPrefixArchimedeanFactor t N
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hraw := norm_gsTwistedPositivePrefixSum_sub_archimedeanFactor_le
    f t hN ht ht_small
  have hraw' :
      ‖gsTwistedPositivePrefixSum f t N / (N : ℂ) - A * R‖ ≤
        (4 / (N : ℝ)) *
          HalberstamScratch.partialSum (gsMoebiusNorm f) N := by
    have heq :
        gsTwistedPositivePrefixSum f t N / (N : ℂ) - A * R =
          (gsTwistedPositivePrefixSum f t N -
            (((N : ℂ) * LogPhaseSum.natLogTwist N t) /
                (1 - Complex.I * (t : ℂ))) *
              ∑ d ∈ Finset.Ioc 0 N,
                gsMoebiusCoefficient f d / (d : ℂ)) / (N : ℂ) := by
      dsimp [A, R, gsPrefixArchimedeanFactor, gsReciprocalMoebiusSum]
      field_simp [hNC]
    rw [heq, norm_div, Complex.norm_natCast]
    calc
      ‖gsTwistedPositivePrefixSum f t N -
          (((N : ℂ) * LogPhaseSum.natLogTwist N t) /
              (1 - Complex.I * (t : ℂ))) *
            ∑ d ∈ Finset.Ioc 0 N,
              gsMoebiusCoefficient f d / (d : ℂ)‖ / (N : ℝ) ≤
          (4 * HalberstamScratch.partialSum (gsMoebiusNorm f) N) /
            (N : ℝ) := div_le_div_of_nonneg_right hraw hNR.le
      _ = (4 / (N : ℝ)) *
          HalberstamScratch.partialSum (gsMoebiusNorm f) N := by ring
  have hmean := norm_positivePrefixMean_sub_gsReciprocalMoebiusSum_le f hN
  have hA : ‖A‖ ≤ 1 := by
    exact norm_gsPrefixArchimedeanFactor_le_one t hN
  have htail : ‖A * (R - positivePrefixMean f N)‖ ≤
      (1 / (N : ℝ)) *
        HalberstamScratch.partialSum (gsMoebiusNorm f) N := by
    rw [norm_mul]
    calc
      ‖A‖ * ‖R - positivePrefixMean f N‖ ≤
          1 * ‖R - positivePrefixMean f N‖ :=
        mul_le_mul_of_nonneg_right hA (norm_nonneg _)
      _ = ‖positivePrefixMean f N - R‖ := by
        rw [one_mul, norm_sub_rev]
      _ ≤ (1 / (N : ℝ)) *
          HalberstamScratch.partialSum (gsMoebiusNorm f) N := by
        simpa only [R] using hmean
  calc
    ‖gsTwistedPositivePrefixSum f t N / (N : ℂ) -
        A * positivePrefixMean f N‖ =
      ‖(gsTwistedPositivePrefixSum f t N / (N : ℂ) - A * R) +
        A * (R - positivePrefixMean f N)‖ := by ring_nf
    _ ≤ ‖gsTwistedPositivePrefixSum f t N / (N : ℂ) - A * R‖ +
        ‖A * (R - positivePrefixMean f N)‖ := norm_add_le _ _
    _ ≤ (4 / (N : ℝ)) *
          HalberstamScratch.partialSum (gsMoebiusNorm f) N +
        (1 / (N : ℝ)) *
          HalberstamScratch.partialSum (gsMoebiusNorm f) N :=
      add_le_add hraw' htail
    _ = (5 / (N : ℝ)) *
        HalberstamScratch.partialSum (gsMoebiusNorm f) N := by ring

/-- Halberstam--Richert specialization of the prefix-to-prefix
renormalization. -/
theorem norm_normalized_gsTwistedPrefix_sub_archimedeanFactor_mul_prefixMean_le_exp
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (t : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (ht : t ≠ 0) (ht_small : |t| ≤ 1) :
    ‖gsTwistedPositivePrefixSum f t N / (N : ℂ) -
        gsPrefixArchimedeanFactor t N * positivePrefixMean f N‖ ≤
      5 * (HalberstamScratch.explicitMassConstant 2 1 + 1) /
        Real.log (N : ℝ) * Real.exp (gsEulerExponent f N) := by
  refine (norm_normalized_gsTwistedPrefix_sub_archimedeanFactor_mul_prefixMean_le
    f t (by omega) ht ht_small).trans ?_
  have hHR := gsMoebiusNorm_partialSum_le_exp hmul hbound N hN
  have hNR : (0 : ℝ) < N := by positivity
  calc
    (5 / (N : ℝ)) * HalberstamScratch.partialSum (gsMoebiusNorm f) N ≤
        (5 / (N : ℝ)) *
          ((HalberstamScratch.explicitMassConstant 2 1 + 1) *
            (N : ℝ) / Real.log (N : ℝ) * Real.exp (gsEulerExponent f N)) :=
      mul_le_mul_of_nonneg_left hHR (by positivity)
    _ = 5 * (HalberstamScratch.explicitMassConstant 2 1 + 1) /
        Real.log (N : ℝ) * Real.exp (gsEulerExponent f N) := by
      field_simp

end

end Erdos67
