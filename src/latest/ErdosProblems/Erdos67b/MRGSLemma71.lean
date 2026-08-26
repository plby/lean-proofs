import ErdosProblems.Erdos67b.MRGSPowerSumFinal
import ErdosProblems.Erdos67b.MRGSTwistedEuler

/-!
# The finite convolution step in Granville--Soundararajan Lemma 7.1

This file rewrites a twisted prefix sum using `g = f * μ`.  It is the exact
finite identity to which the uniform logarithmic-phase power sum is applied;
there are no asymptotic or mean-value hypotheses.
-/

open scoped BigOperators ArithmeticFunction.Moebius
open Finset

namespace Erdos67b

noncomputable section

/-- Positive prefix sum with the logarithmic phase `n⁻ⁱᵗ`. -/
def gsTwistedPositivePrefixSum (f : ℕ → ℂ) (t : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 N, f n * LogPhaseSum.natLogTwist n t

private theorem Ioc_filter_dvd_eq_image_mul_zero
    (d N : ℕ) (hd : 0 < d) :
    (Finset.Ioc 0 N).filter (fun n => d ∣ n) =
      (Finset.Ioc 0 (N / d)).image (fun m => d * m) := by
  ext n
  constructor
  · intro hn
    have hnIoc := (Finset.mem_filter.mp hn).1
    obtain ⟨m, rfl⟩ := (Finset.mem_filter.mp hn).2
    rw [Finset.mem_image]
    refine ⟨m, ?_, rfl⟩
    rw [Finset.mem_Ioc]
    constructor
    · have hnpos := (Finset.mem_Ioc.mp hnIoc).1
      exact Nat.pos_of_mul_pos_left hnpos
    · apply (Nat.le_div_iff_mul_le hd).2
      simpa [Nat.mul_comm] using (Finset.mem_Ioc.mp hnIoc).2
  · intro hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    rw [Finset.mem_filter, Finset.mem_Ioc]
    have hmIoc := Finset.mem_Ioc.mp hm
    refine ⟨⟨Nat.mul_pos hd hmIoc.1, ?_⟩, dvd_mul_right d m⟩
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).1 hmIoc.2

/-- Exact divisor-convolution formula for the twisted positive prefix sum. -/
theorem gsTwistedPositivePrefixSum_eq_moebius_convolution
    (f : ℕ → ℂ) (t : ℝ) (N : ℕ) :
    gsTwistedPositivePrefixSum f t N =
      ∑ d ∈ Finset.Ioc 0 N,
        gsMoebiusCoefficient f d * LogPhaseSum.natLogTwist d t *
          (∑ m ∈ Finset.Ioc 0 (N / d),
            LogPhaseSum.natLogTwist m t) := by
  unfold gsTwistedPositivePrefixSum
  calc
    (∑ n ∈ Finset.Ioc 0 N,
        f n * LogPhaseSum.natLogTwist n t) =
        ∑ n ∈ Finset.Ioc 0 N,
          (∑ d ∈ n.divisors, gsMoebiusCoefficient f d) *
            LogPhaseSum.natLogTwist n t := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : n ≠ 0 := ne_of_gt (Finset.mem_Ioc.mp hn).1
      congr 1
      calc
        f n = positiveArithmeticFunction f n :=
          (positiveArithmeticFunction_apply hn0).symm
        _ = (gsMoebiusCoefficient f *
            (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) n := by
              rw [gsMoebiusCoefficient_mul_zeta]
        _ = ∑ d ∈ n.divisors, gsMoebiusCoefficient f d := by
              rw [ArithmeticFunction.coe_mul_zeta_apply]
    _ = ∑ n ∈ Finset.Ioc 0 N,
          ∑ d ∈ n.divisors,
            gsMoebiusCoefficient f d * LogPhaseSum.natLogTwist n t := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_mul]
    _ = ∑ n ∈ Finset.Ioc 0 N,
          ∑ d ∈ (Finset.Ioc 0 N).filter (fun d => d ∣ n),
            gsMoebiusCoefficient f d * LogPhaseSum.natLogTwist n t := by
      apply Finset.sum_congr rfl
      intro n hn
      refine Finset.sum_congr ?_ fun d hd => rfl
      ext d
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      have hnpos := (Finset.mem_Ioc.mp hn).1
      have hnN := (Finset.mem_Ioc.mp hn).2
      constructor
      · intro hd
        have hdvd := (Nat.mem_divisors.mp hd).1
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd hnpos,
          (Nat.le_of_dvd hnpos hdvd).trans hnN⟩, hdvd⟩
      · rintro ⟨⟨hdpos, hdN⟩, hdvd⟩
        exact Nat.mem_divisors.mpr ⟨hdvd, ne_of_gt hnpos⟩
    _ = ∑ d ∈ Finset.Ioc 0 N,
          ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => d ∣ n),
            gsMoebiusCoefficient f d * LogPhaseSum.natLogTwist n t := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Ioc 0 N,
        gsMoebiusCoefficient f d * LogPhaseSum.natLogTwist d t *
          (∑ m ∈ Finset.Ioc 0 (N / d),
            LogPhaseSum.natLogTwist m t) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos := (Finset.mem_Ioc.mp hd).1
      rw [Ioc_filter_dvd_eq_image_mul_zero d N hdpos]
      have hinj : Set.InjOn (fun m : ℕ => d * m)
          ↑(Finset.Ioc 0 (N / d)) := by
        intro m hm n hn h
        exact Nat.eq_of_mul_eq_mul_left hdpos h
      rw [Finset.sum_image hinj, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hmpos := (Finset.mem_Ioc.mp hm).1
      rw [LogPhaseSum.natLogTwist_eq_archimedeanTwist_neg,
        LogPhaseSum.natLogTwist_eq_archimedeanTwist_neg,
        LogPhaseSum.natLogTwist_eq_archimedeanTwist_neg,
        archimedeanTwist_mul (-t) hdpos hmpos]
      ring

private theorem logPhase_mul_of_pos
    (t : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    LogPhaseSum.logPhase t x * LogPhaseSum.logPhase t y =
      LogPhaseSum.logPhase t (x * y) := by
  unfold LogPhaseSum.logPhase
  simpa only [Complex.ofReal_mul] using
    (Complex.mul_cpow_ofReal_nonneg hx.le hy.le
      (-(Complex.I * (t : ℂ)))).symm

private theorem real_cpow_one_sub_I_mul_eq_mul_logPhase
    (t : ℝ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (1 - Complex.I * (t : ℂ)) =
      (x : ℂ) * LogPhaseSum.logPhase t x := by
  rw [show (1 : ℂ) - Complex.I * (t : ℂ) =
      1 + (-(Complex.I * (t : ℂ))) by ring]
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
  simp [LogPhaseSum.logPhase]

/-- Algebraic identity converting the real-quotient power-sum main term
back to the untwisted prefix coefficient. -/
theorem natLogTwist_mul_realQuotient_main
    (t : ℝ) {N d : ℕ} (hN : 0 < N) (hd : 0 < d) :
    LogPhaseSum.natLogTwist d t *
        (((((N : ℝ) / (d : ℝ) : ℝ) : ℂ) ^
            (1 - Complex.I * (t : ℂ))) /
          (1 - Complex.I * (t : ℂ))) =
      (((N : ℂ) / (d : ℂ)) * LogPhaseSum.natLogTwist N t) /
        (1 - Complex.I * (t : ℂ)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hz : 0 < (N : ℝ) / (d : ℝ) := div_pos hNreal hdR
  have hprod : (d : ℝ) * ((N : ℝ) / (d : ℝ)) = (N : ℝ) := by
    field_simp
  rw [real_cpow_one_sub_I_mul_eq_mul_logPhase t hz]
  have hphase : LogPhaseSum.natLogTwist d t *
      LogPhaseSum.logPhase t ((N : ℝ) / (d : ℝ)) =
        LogPhaseSum.natLogTwist N t := by
    unfold LogPhaseSum.natLogTwist
    rw [logPhase_mul_of_pos t (Nat.cast_pos.mpr hd) hz, hprod]
  push_cast
  field_simp
  rw [← hphase]
  ring

/-- The divisor-convolution remainder in GS Lemma 7.1.  The power-sum
remainder is absolute on every divisor fiber, so the full error is bounded
by four times the ordinary partial sum of `|f * μ|`. -/
theorem norm_gsTwistedPositivePrefixSum_sub_convolutionMain_le
    (f : ℕ → ℂ) (t : ℝ) {N : ℕ} (hN : 0 < N)
    (ht : t ≠ 0) (ht_small : |t| ≤ 1) :
    ‖gsTwistedPositivePrefixSum f t N -
        ∑ d ∈ Finset.Ioc 0 N,
          gsMoebiusCoefficient f d * LogPhaseSum.natLogTwist d t *
            (((((N : ℝ) / (d : ℝ) : ℝ) : ℂ) ^
                (1 - Complex.I * (t : ℂ))) /
              (1 - Complex.I * (t : ℂ)))‖ ≤
      4 * HalberstamScratch.partialSum (gsMoebiusNorm f) N := by
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
              (1 - Complex.I * (t : ℂ))))‖
        ≤ ∑ d ∈ Finset.Ioc 0 N,
            ‖gsMoebiusCoefficient f d * LogPhaseSum.natLogTwist d t *
                (∑ m ∈ Finset.Ioc 0 (N / d),
                  LogPhaseSum.natLogTwist m t) -
              gsMoebiusCoefficient f d * LogPhaseSum.natLogTwist d t *
                (((((N : ℝ) / (d : ℝ) : ℝ) : ℂ) ^
                    (1 - Complex.I * (t : ℂ))) /
                  (1 - Complex.I * (t : ℂ)))‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Ioc 0 N, 4 * gsMoebiusNorm f d := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Ioc.mp hd).1
      have hdN : d ≤ N := (Finset.mem_Ioc.mp hd).2
      have hp := norm_sum_Ioc_natLogTwist_sub_realQuotient_main_le_four
        t hdpos hdN ht ht_small
      rw [← mul_sub, norm_mul, norm_mul,
        LogPhaseSum.norm_natLogTwist t hdpos, mul_one, gsMoebiusNorm]
      simpa only [mul_comm] using
        (mul_le_mul_of_nonneg_left hp
          (norm_nonneg (gsMoebiusCoefficient f d)))
    _ = 4 * HalberstamScratch.partialSum (gsMoebiusNorm f) N := by
      unfold HalberstamScratch.partialSum
      have hset : Finset.Ioc 0 N = Finset.Icc 1 N := by
        ext n
        simp only [Finset.mem_Ioc, Finset.mem_Icc]
        omega
      rw [hset, Finset.mul_sum]

/-- The main terms on the divisor fibers factor into a single Archimedean
phase and the reciprocal-weighted Möbius convolution. -/
theorem convolutionMain_eq_archimedeanFactor_mul
    (f : ℕ → ℂ) (t : ℝ) {N : ℕ} (hN : 0 < N) :
    (∑ d ∈ Finset.Ioc 0 N,
        gsMoebiusCoefficient f d * LogPhaseSum.natLogTwist d t *
          (((((N : ℝ) / (d : ℝ) : ℝ) : ℂ) ^
              (1 - Complex.I * (t : ℂ))) /
            (1 - Complex.I * (t : ℂ)))) =
      (((N : ℂ) * LogPhaseSum.natLogTwist N t) /
          (1 - Complex.I * (t : ℂ))) *
        ∑ d ∈ Finset.Ioc 0 N,
          gsMoebiusCoefficient f d / (d : ℂ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := (Finset.mem_Ioc.mp hd).1
  rw [mul_assoc, natLogTwist_mul_realQuotient_main t hN hdpos]
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
  field_simp [hdC]

/-- GS Lemma 7.1 in its finite factorized form, before inserting the
Halberstam--Richert upper bound for `|f * μ|`. -/
theorem norm_gsTwistedPositivePrefixSum_sub_archimedeanFactor_le
    (f : ℕ → ℂ) (t : ℝ) {N : ℕ} (hN : 0 < N)
    (ht : t ≠ 0) (ht_small : |t| ≤ 1) :
    ‖gsTwistedPositivePrefixSum f t N -
        (((N : ℂ) * LogPhaseSum.natLogTwist N t) /
            (1 - Complex.I * (t : ℂ))) *
          ∑ d ∈ Finset.Ioc 0 N,
            gsMoebiusCoefficient f d / (d : ℂ)‖ ≤
      4 * HalberstamScratch.partialSum (gsMoebiusNorm f) N := by
  rw [← convolutionMain_eq_archimedeanFactor_mul f t hN]
  exact norm_gsTwistedPositivePrefixSum_sub_convolutionMain_le
    f t hN ht ht_small

/-- Fully unconditional Halberstam--Richert specialization of the finite GS
Lemma 7.1 remainder. -/
theorem norm_gsTwistedPositivePrefixSum_sub_archimedeanFactor_le_exp
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (t : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (ht : t ≠ 0) (ht_small : |t| ≤ 1) :
    ‖gsTwistedPositivePrefixSum f t N -
        (((N : ℂ) * LogPhaseSum.natLogTwist N t) /
            (1 - Complex.I * (t : ℂ))) *
          ∑ d ∈ Finset.Ioc 0 N,
            gsMoebiusCoefficient f d / (d : ℂ)‖ ≤
      4 * ((HalberstamScratch.explicitMassConstant 2 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) * Real.exp (gsEulerExponent f N)) := by
  refine (norm_gsTwistedPositivePrefixSum_sub_archimedeanFactor_le
    f t (by omega) ht ht_small).trans ?_
  exact mul_le_mul_of_nonneg_left
    (gsMoebiusNorm_partialSum_le_exp hmul hbound N hN) (by norm_num)

end

end Erdos67b
