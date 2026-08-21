import ErdosProblems.Erdos239.External.Erdos67.MRGSPowerSumLinear
import ErdosProblems.Erdos239.External.Erdos67.MRGSLemma71PrefixRenormalization

/-!
# Linear-height GS prefix renormalization

This is the source-range version of the finite Granville--Soundararajan
renormalization.  The power-sum error is retained as `O(1 + |t|)`, so the
result remains useful on the growing central window of Appendix A.
-/

open scoped BigOperators
open Finset

namespace Erdos67

noncomputable section

/-- The divisor-convolution remainder with the source-sharp linear height
dependence. -/
theorem norm_gsTwistedPositivePrefixSum_sub_convolutionMain_le_linear
    (f : ℕ → ℂ) (t : ℝ) {N : ℕ} (_hN : 0 < N) (ht : t ≠ 0) :
    ‖gsTwistedPositivePrefixSum f t N -
        ∑ d ∈ Finset.Ioc 0 N,
          gsMoebiusCoefficient f d * LogPhaseSum.natLogTwist d t *
            (((((N : ℝ) / (d : ℝ) : ℝ) : ℂ) ^
                (1 - Complex.I * (t : ℂ))) /
              (1 - Complex.I * (t : ℂ)))‖ ≤
      9 * (1 + |t|) * HalberstamScratch.partialSum (gsMoebiusNorm f) N := by
  rw [gsTwistedPositivePrefixSum_eq_moebius_convolution]
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ d ∈ Finset.Ioc 0 N,
        (gsMoebiusCoefficient f d * LogPhaseSum.natLogTwist d t *
            (∑ m ∈ Finset.Ioc 0 (N / d),
              LogPhaseSum.natLogTwist m t) -
          gsMoebiusCoefficient f d * LogPhaseSum.natLogTwist d t *
            (((((N : ℝ) / (d : ℝ) : ℝ) : ℂ) ^
                (1 - Complex.I * (t : ℂ))) /
              (1 - Complex.I * (t : ℂ))))‖ ≤
        ∑ d ∈ Finset.Ioc 0 N,
          ‖gsMoebiusCoefficient f d * LogPhaseSum.natLogTwist d t *
              (∑ m ∈ Finset.Ioc 0 (N / d),
                LogPhaseSum.natLogTwist m t) -
            gsMoebiusCoefficient f d * LogPhaseSum.natLogTwist d t *
              (((((N : ℝ) / (d : ℝ) : ℝ) : ℂ) ^
                  (1 - Complex.I * (t : ℂ))) /
                (1 - Complex.I * (t : ℂ)))‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Ioc 0 N,
        9 * (1 + |t|) * gsMoebiusNorm f d := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Ioc.mp hd).1
      have hdN : d ≤ N := (Finset.mem_Ioc.mp hd).2
      have hp := norm_sum_Ioc_natLogTwist_sub_realQuotient_main_le_linear
        t hdpos hdN ht
      rw [← mul_sub, norm_mul, norm_mul,
        LogPhaseSum.norm_natLogTwist t hdpos, mul_one, gsMoebiusNorm]
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        (mul_le_mul_of_nonneg_left hp
          (norm_nonneg (gsMoebiusCoefficient f d)))
    _ = 9 * (1 + |t|) *
        HalberstamScratch.partialSum (gsMoebiusNorm f) N := by
      unfold HalberstamScratch.partialSum
      have hset : Finset.Ioc 0 N = Finset.Icc 1 N := by
        ext n
        simp only [Finset.mem_Ioc, Finset.mem_Icc]
        omega
      rw [hset, Finset.mul_sum]

/-- The finite factorized form of GS Lemma 7.1 with error linear in the
frequency displacement. -/
theorem norm_gsTwistedPositivePrefixSum_sub_archimedeanFactor_le_linear
    (f : ℕ → ℂ) (t : ℝ) {N : ℕ} (hN : 0 < N) (ht : t ≠ 0) :
    ‖gsTwistedPositivePrefixSum f t N -
        (((N : ℂ) * LogPhaseSum.natLogTwist N t) /
            (1 - Complex.I * (t : ℂ))) *
          ∑ d ∈ Finset.Ioc 0 N,
            gsMoebiusCoefficient f d / (d : ℂ)‖ ≤
      9 * (1 + |t|) *
        HalberstamScratch.partialSum (gsMoebiusNorm f) N := by
  rw [← convolutionMain_eq_archimedeanFactor_mul f t hN]
  exact norm_gsTwistedPositivePrefixSum_sub_convolutionMain_le_linear
    f t hN ht

/-- Prefix-to-prefix renormalization on an arbitrary nonzero frequency,
with the exact source dependence `1 + |t|`. -/
theorem norm_normalized_gsTwistedPrefix_sub_archimedeanFactor_mul_prefixMean_le_linear
    (f : ℕ → ℂ) (t : ℝ) {N : ℕ} (hN : 0 < N) (ht : t ≠ 0) :
    ‖gsTwistedPositivePrefixSum f t N / (N : ℂ) -
        gsPrefixArchimedeanFactor t N * positivePrefixMean f N‖ ≤
      (10 * (1 + |t|) / (N : ℝ)) *
        HalberstamScratch.partialSum (gsMoebiusNorm f) N := by
  let R : ℂ := gsReciprocalMoebiusSum f N
  let A : ℂ := gsPrefixArchimedeanFactor t N
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hraw := norm_gsTwistedPositivePrefixSum_sub_archimedeanFactor_le_linear
    f t hN ht
  have hraw' :
      ‖gsTwistedPositivePrefixSum f t N / (N : ℂ) - A * R‖ ≤
        (9 * (1 + |t|) / (N : ℝ)) *
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
          (9 * (1 + |t|) *
            HalberstamScratch.partialSum (gsMoebiusNorm f) N) /
              (N : ℝ) := div_le_div_of_nonneg_right hraw hNR.le
      _ = (9 * (1 + |t|) / (N : ℝ)) *
          HalberstamScratch.partialSum (gsMoebiusNorm f) N := by ring
  have hmean := norm_positivePrefixMean_sub_gsReciprocalMoebiusSum_le f hN
  have hA : ‖A‖ ≤ 1 := norm_gsPrefixArchimedeanFactor_le_one t hN
  have htail : ‖A * (R - positivePrefixMean f N)‖ ≤
      ((1 + |t|) / (N : ℝ)) *
        HalberstamScratch.partialSum (gsMoebiusNorm f) N := by
    have hbase : ‖A * (R - positivePrefixMean f N)‖ ≤
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
    refine hbase.trans ?_
    have hsum0 : 0 ≤ HalberstamScratch.partialSum (gsMoebiusNorm f) N := by
      unfold HalberstamScratch.partialSum gsMoebiusNorm
      positivity
    have hcoef : 1 / (N : ℝ) ≤ (1 + |t|) / (N : ℝ) := by
      exact div_le_div_of_nonneg_right (by linarith [abs_nonneg t]) hNR.le
    exact mul_le_mul_of_nonneg_right hcoef hsum0
  calc
    ‖gsTwistedPositivePrefixSum f t N / (N : ℂ) -
        A * positivePrefixMean f N‖ =
      ‖(gsTwistedPositivePrefixSum f t N / (N : ℂ) - A * R) +
        A * (R - positivePrefixMean f N)‖ := by ring_nf
    _ ≤ ‖gsTwistedPositivePrefixSum f t N / (N : ℂ) - A * R‖ +
        ‖A * (R - positivePrefixMean f N)‖ := norm_add_le _ _
    _ ≤ (9 * (1 + |t|) / (N : ℝ)) *
          HalberstamScratch.partialSum (gsMoebiusNorm f) N +
        ((1 + |t|) / (N : ℝ)) *
          HalberstamScratch.partialSum (gsMoebiusNorm f) N :=
      add_le_add hraw' htail
    _ = (10 * (1 + |t|) / (N : ℝ)) *
        HalberstamScratch.partialSum (gsMoebiusNorm f) N := by ring

/-- Halberstam--Richert specialization of the linear-height prefix
renormalization. -/
theorem norm_normalized_gsTwistedPrefix_sub_archimedeanFactor_mul_prefixMean_le_exp_linear
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (t : ℝ) {N : ℕ} (hN : 2 ≤ N) (ht : t ≠ 0) :
    ‖gsTwistedPositivePrefixSum f t N / (N : ℂ) -
        gsPrefixArchimedeanFactor t N * positivePrefixMean f N‖ ≤
      10 * (1 + |t|) *
        (HalberstamScratch.explicitMassConstant 2 1 + 1) /
          Real.log (N : ℝ) * Real.exp (gsEulerExponent f N) := by
  refine (norm_normalized_gsTwistedPrefix_sub_archimedeanFactor_mul_prefixMean_le_linear
    f t (by omega) ht).trans ?_
  have hHR := gsMoebiusNorm_partialSum_le_exp hmul hbound N hN
  have hNR : (0 : ℝ) < N := by positivity
  calc
    (10 * (1 + |t|) / (N : ℝ)) *
        HalberstamScratch.partialSum (gsMoebiusNorm f) N ≤
      (10 * (1 + |t|) / (N : ℝ)) *
        ((HalberstamScratch.explicitMassConstant 2 1 + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
            Real.exp (gsEulerExponent f N)) :=
      mul_le_mul_of_nonneg_left hHR (by positivity)
    _ = 10 * (1 + |t|) *
        (HalberstamScratch.explicitMassConstant 2 1 + 1) /
          Real.log (N : ℝ) * Real.exp (gsEulerExponent f N) := by
      field_simp

end

end Erdos67
