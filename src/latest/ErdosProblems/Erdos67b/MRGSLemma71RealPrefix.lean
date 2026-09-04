import ErdosProblems.Erdos67b.MRGSLemma71
import ErdosProblems.Erdos67b.MRGranvilleSoundararajanRealPrefixStability

/-!
# The GS near-twist estimate for an ordinary real prefix

This file specializes the finite factorized form of Granville--Soundararajan
Lemma 7.1 to the untwisted coefficient `f(n)n^(-it)`.  The logarithmic phase
then cancels exactly, leaving the ordinary positive prefix sum of `f`.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67b

noncomputable section

/-- The reciprocal-weighted Möbius coefficient in the GS main term. -/
def gsReciprocalMoebiusSum (f : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ d ∈ Finset.Ioc 0 N, gsMoebiusCoefficient f d / (d : ℂ)

/-- The normalized main term in GS Lemma 7.1. -/
def gsNearTwistNormalizedMain (f : ℕ → ℂ) (t : ℝ) (N : ℕ) : ℂ :=
  (LogPhaseSum.natLogTwist N (-t) /
      (1 - Complex.I * ((-t : ℝ) : ℂ))) *
    gsReciprocalMoebiusSum (archimedeanUntwist f t) N

/-- Fixed constant in the uniform near-twist norm-stability theorem. -/
def realGSNearTwistNormConstant : ℝ :=
  11 * (HalberstamScratch.explicitMassConstant 2 1 + 1)

theorem realGSNearTwistNormConstant_nonneg :
    0 ≤ realGSNearTwistNormConstant := by
  unfold realGSNearTwistNormConstant
  exact mul_nonneg (by norm_num)
    (add_nonneg
      (HalberstamScratch.explicitMassConstant_nonneg (by norm_num) (by norm_num))
      zero_le_one)

/-- Untwisting by `n^(it)` and then inserting the opposite logarithmic phase
recovers the original coefficient exactly on positive integers. -/
theorem archimedeanUntwist_mul_natLogTwist_neg
    (f : ℕ → ℂ) (t : ℝ) {n : ℕ} (hn : 0 < n) :
    archimedeanUntwist f t n * LogPhaseSum.natLogTwist n (-t) = f n := by
  rw [archimedeanUntwist, if_neg hn.ne',
    LogPhaseSum.natLogTwist_eq_archimedeanTwist_neg]
  have htwist : archimedeanTwist (-(-t)) n = archimedeanTwist t n := by
    congr 1
    ring
  rw [htwist, mul_assoc, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq, norm_archimedeanTwist hn]
  norm_num

/-- The twisted prefix of the untwisted coefficient is the ordinary prefix. -/
theorem gsTwistedPositivePrefixSum_archimedeanUntwist_neg
    (f : ℕ → ℂ) (t : ℝ) (N : ℕ) :
    gsTwistedPositivePrefixSum (archimedeanUntwist f t) (-t) N =
      positivePrefixSum f N := by
  unfold gsTwistedPositivePrefixSum
  have hprefix : positivePrefixSum f N = ∑ n ∈ Finset.Ioc 0 N, f n := by
    have h := sum_Ioc_eq_positivePrefixSum_sub f (Nat.zero_le N)
    simpa [positivePrefixSum] using h.symm
  rw [hprefix]
  apply Finset.sum_congr rfl
  intro n hn
  exact archimedeanUntwist_mul_natLogTwist_neg f t
    (Finset.mem_Ioc.mp hn).1

/-- Unconditional near-twist GS asymptotic for the ordinary positive prefix
sum.  Its error is expressed through the Euler exponent of the untwisted
coefficient; the next theorem inserts the pretentious-distance bound. -/
theorem norm_positivePrefixSum_sub_nearTwistFactor_le_exp
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (t : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (ht : t ≠ 0) (ht_small : |t| ≤ 1) :
    ‖positivePrefixSum f N -
        (((N : ℂ) * LogPhaseSum.natLogTwist N (-t)) /
            (1 - Complex.I * ((-t : ℝ) : ℂ))) *
          ∑ d ∈ Finset.Ioc 0 N,
            gsMoebiusCoefficient (archimedeanUntwist f t) d / (d : ℂ)‖ ≤
      4 * ((HalberstamScratch.explicitMassConstant 2 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          Real.exp (gsEulerExponent (archimedeanUntwist f t) N)) := by
  rw [← gsTwistedPositivePrefixSum_archimedeanUntwist_neg f t N]
  exact norm_gsTwistedPositivePrefixSum_sub_archimedeanFactor_le_exp
    (archimedeanUntwist_isMultiplicative hmul t)
    (norm_archimedeanUntwist_le_one hbound t) (-t) hN
    (neg_ne_zero.mpr ht) (by simpa using ht_small)

/-- Normalized form of the unconditional near-twist estimate. -/
theorem norm_positivePrefixMean_sub_gsNearTwistNormalizedMain_le_exp
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (t : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (ht : t ≠ 0) (ht_small : |t| ≤ 1) :
    ‖positivePrefixMean f N - gsNearTwistNormalizedMain f t N‖ ≤
      4 * (HalberstamScratch.explicitMassConstant 2 1 + 1) /
        Real.log (N : ℝ) *
          Real.exp (gsEulerExponent (archimedeanUntwist f t) N) := by
  have hNpos : 0 < N := by omega
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hNR : (0 : ℝ) < N := by positivity
  have hraw := norm_positivePrefixSum_sub_nearTwistFactor_le_exp
    hmul hbound t hN ht ht_small
  have heq : positivePrefixMean f N - gsNearTwistNormalizedMain f t N =
      (positivePrefixSum f N -
        (((N : ℂ) * LogPhaseSum.natLogTwist N (-t)) /
            (1 - Complex.I * ((-t : ℝ) : ℂ))) *
          gsReciprocalMoebiusSum (archimedeanUntwist f t) N) / (N : ℂ) := by
    unfold positivePrefixMean gsNearTwistNormalizedMain
    field_simp [hNC]
  rw [heq, norm_div, Complex.norm_natCast]
  calc
    ‖positivePrefixSum f N -
          (((N : ℂ) * LogPhaseSum.natLogTwist N (-t)) /
              (1 - Complex.I * ((-t : ℝ) : ℂ))) *
            gsReciprocalMoebiusSum (archimedeanUntwist f t) N‖ /
        (N : ℝ) ≤
        (4 * ((HalberstamScratch.explicitMassConstant 2 1 + 1) *
          (N : ℝ) / Real.log (N : ℝ) *
            Real.exp (gsEulerExponent (archimedeanUntwist f t) N))) /
          (N : ℝ) := by
      exact div_le_div_of_nonneg_right hraw hNR.le
    _ = 4 * (HalberstamScratch.explicitMassConstant 2 1 + 1) /
          Real.log (N : ℝ) *
            Real.exp (gsEulerExponent (archimedeanUntwist f t) N) := by
      field_simp

/-- Pretentious-distance form of the ordinary-prefix near-twist estimate. -/
theorem norm_positivePrefixSum_sub_nearTwistFactor_le_distance
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (t : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (ht : t ≠ 0) (ht_small : |t| ≤ 1) :
    ‖positivePrefixSum f N -
        (((N : ℂ) * LogPhaseSum.natLogTwist N (-t)) /
            (1 - Complex.I * ((-t : ℝ) : ℂ))) *
          ∑ d ∈ Finset.Ioc 0 N,
            gsMoebiusCoefficient (archimedeanUntwist f t) d / (d : ℂ)‖ ≤
      4 * ((HalberstamScratch.explicitMassConstant 2 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          Real.exp
            (Real.sqrt
                (2 * pretentiousDistSq f (archimedeanTwist t) N *
                  PrimeEstimates.primeReciprocals N) + 8)) := by
  refine (norm_positivePrefixSum_sub_nearTwistFactor_le_exp
    hmul hbound t hN ht ht_small).trans ?_
  have heuler := gsEulerExponent_archimedeanUntwist_le hbound t N
  have hexp : Real.exp (gsEulerExponent (archimedeanUntwist f t) N) ≤
      Real.exp
        (Real.sqrt
            (2 * pretentiousDistSq f (archimedeanTwist t) N *
              PrimeEstimates.primeReciprocals N) + 8) :=
    Real.exp_le_exp.mpr heuler
  have hconstant :
      0 ≤ HalberstamScratch.explicitMassConstant 2 1 + 1 :=
    add_nonneg
      (HalberstamScratch.explicitMassConstant_nonneg (by norm_num) (by norm_num))
      zero_le_one
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  gcongr

/-- The reciprocal Möbius factor varies by at most an ordinary
Halberstam--Richert partial sum divided by the left endpoint. -/
theorem norm_gsReciprocalMoebiusSum_sub_le_partialSum
    (f : ℕ → ℂ) {X Z : ℕ} (hX : 0 < X) (hXZ : X ≤ Z) :
    ‖gsReciprocalMoebiusSum f Z - gsReciprocalMoebiusSum f X‖ ≤
      (1 / (X : ℝ)) *
        HalberstamScratch.partialSum (gsMoebiusNorm f) Z := by
  have hsubset : Finset.Ioc 0 X ⊆ Finset.Ioc 0 Z := by
    intro d hd
    exact Finset.mem_Ioc.mpr
      ⟨(Finset.mem_Ioc.mp hd).1, (Finset.mem_Ioc.mp hd).2.trans hXZ⟩
  have hsdiff : Finset.Ioc 0 Z \ Finset.Ioc 0 X = Finset.Ioc X Z := by
    ext d
    simp only [Finset.mem_sdiff, Finset.mem_Ioc]
    omega
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have htailSubset : Finset.Ioc X Z ⊆ Finset.Icc 1 Z := by
    intro d hd
    have hd' := Finset.mem_Ioc.mp hd
    exact Finset.mem_Icc.mpr ⟨by omega, hd'.2⟩
  unfold gsReciprocalMoebiusSum
  rw [← Finset.sum_sdiff_eq_sub hsubset, hsdiff]
  calc
    ‖∑ d ∈ Finset.Ioc X Z,
        gsMoebiusCoefficient f d / (d : ℂ)‖ ≤
        ∑ d ∈ Finset.Ioc X Z,
          ‖gsMoebiusCoefficient f d / (d : ℂ)‖ := norm_sum_le _ _
    _ = ∑ d ∈ Finset.Ioc X Z,
          gsMoebiusNorm f d / (d : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos : 0 < d := hX.trans (Finset.mem_Ioc.mp hd).1
      rw [norm_div, gsMoebiusNorm, Complex.norm_natCast]
    _ ≤ ∑ d ∈ Finset.Ioc X Z,
          (1 / (X : ℝ)) * gsMoebiusNorm f d := by
      apply Finset.sum_le_sum
      intro d hd
      have hdX : X ≤ d := (Finset.mem_Ioc.mp hd).1.le
      have hinv : 1 / (d : ℝ) ≤ 1 / (X : ℝ) := by
        exact one_div_le_one_div_of_le hXR (by exact_mod_cast hdX)
      calc
        gsMoebiusNorm f d / (d : ℝ) =
            (1 / (d : ℝ)) * gsMoebiusNorm f d := by ring
        _ ≤ (1 / (X : ℝ)) * gsMoebiusNorm f d :=
          mul_le_mul_of_nonneg_right hinv (gsMoebiusNorm_nonneg f d)
    _ = (1 / (X : ℝ)) *
          ∑ d ∈ Finset.Ioc X Z, gsMoebiusNorm f d := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (X : ℝ)) *
          ∑ d ∈ Finset.Icc 1 Z, gsMoebiusNorm f d := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg htailSubset
          (fun d _ _ ↦ gsMoebiusNorm_nonneg f d))
        (by positivity)
    _ = (1 / (X : ℝ)) *
          HalberstamScratch.partialSum (gsMoebiusNorm f) Z := by
      rfl

/-- Halberstam--Richert specialization of the reciprocal-factor variation. -/
theorem norm_gsReciprocalMoebiusSum_sub_le_exp
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    {X Z : ℕ} (hX : 0 < X) (hXZ : X ≤ Z) (hZ : 2 ≤ Z) :
    ‖gsReciprocalMoebiusSum f Z - gsReciprocalMoebiusSum f X‖ ≤
      (1 / (X : ℝ)) *
        ((HalberstamScratch.explicitMassConstant 2 1 + 1) *
          (Z : ℝ) / Real.log (Z : ℝ) * Real.exp (gsEulerExponent f Z)) := by
  refine (norm_gsReciprocalMoebiusSum_sub_le_partialSum f hX hXZ).trans ?_
  exact mul_le_mul_of_nonneg_left
    (gsMoebiusNorm_partialSum_le_exp hmul hbound Z hZ) (by positivity)

/-- The unit Archimedean phase makes the norm of the normalized GS main
term depend only on the reciprocal Möbius factor. -/
theorem norm_gsNearTwistNormalizedMain
    (f : ℕ → ℂ) (t : ℝ) {N : ℕ} (hN : 0 < N) :
    ‖gsNearTwistNormalizedMain f t N‖ =
      ‖gsReciprocalMoebiusSum (archimedeanUntwist f t) N‖ /
        ‖1 - Complex.I * ((-t : ℝ) : ℂ)‖ := by
  unfold gsNearTwistNormalizedMain
  rw [norm_mul, norm_div, LogPhaseSum.norm_natLogTwist (-t) hN]
  ring

/-- The normalized GS main term has slowly varying absolute value; no phase
comparison is needed. -/
theorem abs_norm_gsNearTwistNormalizedMain_sub_norm_le
    (f : ℕ → ℂ) (t : ℝ) {X Z : ℕ}
    (hX : 0 < X) (hXZ : X ≤ Z) :
    |‖gsNearTwistNormalizedMain f t Z‖ -
        ‖gsNearTwistNormalizedMain f t X‖| ≤
      ‖gsReciprocalMoebiusSum (archimedeanUntwist f t) Z -
        gsReciprocalMoebiusSum (archimedeanUntwist f t) X‖ := by
  have hZ : 0 < Z := hX.trans_le hXZ
  let den : ℂ := 1 - Complex.I * ((-t : ℝ) : ℂ)
  have hden : 1 ≤ ‖den‖ := by
    calc
      (1 : ℝ) = |den.re| := by simp [den]
      _ ≤ ‖den‖ := Complex.abs_re_le_norm den
  have hdenpos : 0 < ‖den‖ := lt_of_lt_of_le zero_lt_one hden
  rw [norm_gsNearTwistNormalizedMain f t hZ,
    norm_gsNearTwistNormalizedMain f t hX]
  change |‖gsReciprocalMoebiusSum (archimedeanUntwist f t) Z‖ /‖den‖ -
      ‖gsReciprocalMoebiusSum (archimedeanUntwist f t) X‖ /‖den‖| ≤ _
  rw [← sub_div, abs_div, abs_of_pos hdenpos]
  calc
    |‖gsReciprocalMoebiusSum (archimedeanUntwist f t) Z‖ -
          ‖gsReciprocalMoebiusSum (archimedeanUntwist f t) X‖| /‖den‖ ≤
        |‖gsReciprocalMoebiusSum (archimedeanUntwist f t) Z‖ -
          ‖gsReciprocalMoebiusSum (archimedeanUntwist f t) X‖| := by
      exact (div_le_iff₀ hdenpos).2 (by
        nlinarith [abs_nonneg
          (‖gsReciprocalMoebiusSum (archimedeanUntwist f t) Z‖ -
            ‖gsReciprocalMoebiusSum (archimedeanUntwist f t) X‖)])
    _ ≤ ‖gsReciprocalMoebiusSum (archimedeanUntwist f t) Z -
          gsReciprocalMoebiusSum (archimedeanUntwist f t) X‖ :=
      abs_norm_sub_norm_le _ _

/-- Fully explicit finite GS norm-stability estimate in terms of the three
Euler exponents occurring at the two endpoints and in the coefficient
tail. -/
theorem abs_norm_positivePrefixMean_sub_norm_le_nearTwistEuler
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (t : ℝ) {X Z : ℕ} (hX : 2 ≤ X) (hXZ : X ≤ Z)
    (ht : t ≠ 0) (ht_small : |t| ≤ 1) :
    |‖positivePrefixMean f Z‖ - ‖positivePrefixMean f X‖| ≤
      4 * (HalberstamScratch.explicitMassConstant 2 1 + 1) /
          Real.log (Z : ℝ) *
            Real.exp (gsEulerExponent (archimedeanUntwist f t) Z) +
        (1 / (X : ℝ)) *
          ((HalberstamScratch.explicitMassConstant 2 1 + 1) *
            (Z : ℝ) / Real.log (Z : ℝ) *
              Real.exp (gsEulerExponent (archimedeanUntwist f t) Z)) +
        4 * (HalberstamScratch.explicitMassConstant 2 1 + 1) /
          Real.log (X : ℝ) *
            Real.exp (gsEulerExponent (archimedeanUntwist f t) X) := by
  have hZ : 2 ≤ Z := hX.trans hXZ
  have happroxZ :=
    norm_positivePrefixMean_sub_gsNearTwistNormalizedMain_le_exp
      hmul hbound t hZ ht ht_small
  have happroxX :=
    norm_positivePrefixMean_sub_gsNearTwistNormalizedMain_le_exp
      hmul hbound t hX ht ht_small
  have hmain := abs_norm_gsNearTwistNormalizedMain_sub_norm_le
    f t (show 0 < X by omega) hXZ
  have htail := norm_gsReciprocalMoebiusSum_sub_le_exp
    (archimedeanUntwist_isMultiplicative hmul t)
    (norm_archimedeanUntwist_le_one hbound t)
    (show 0 < X by omega) hXZ hZ
  calc
    |‖positivePrefixMean f Z‖ - ‖positivePrefixMean f X‖| =
        |(‖positivePrefixMean f Z‖ -
            ‖gsNearTwistNormalizedMain f t Z‖) +
          (‖gsNearTwistNormalizedMain f t Z‖ -
            ‖gsNearTwistNormalizedMain f t X‖) +
          (‖gsNearTwistNormalizedMain f t X‖ -
            ‖positivePrefixMean f X‖)| := by ring_nf
    _ ≤ |‖positivePrefixMean f Z‖ -
            ‖gsNearTwistNormalizedMain f t Z‖| +
          |‖gsNearTwistNormalizedMain f t Z‖ -
            ‖gsNearTwistNormalizedMain f t X‖| +
          |‖gsNearTwistNormalizedMain f t X‖ -
            ‖positivePrefixMean f X‖| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ‖positivePrefixMean f Z -
            gsNearTwistNormalizedMain f t Z‖ +
          ‖gsReciprocalMoebiusSum (archimedeanUntwist f t) Z -
            gsReciprocalMoebiusSum (archimedeanUntwist f t) X‖ +
          ‖positivePrefixMean f X -
            gsNearTwistNormalizedMain f t X‖ := by
      exact add_le_add
        (add_le_add (abs_norm_sub_norm_le _ _) hmain)
        (by
          simpa [norm_sub_rev] using
            (abs_norm_sub_norm_le
              (gsNearTwistNormalizedMain f t X) (positivePrefixMean f X)))
    _ ≤ _ := add_le_add (add_le_add happroxZ htail) happroxX

/-- Hierarchy-facing GS near-twist norm stability.  A common
pretentious-distance bound at `3X` controls all prefix norms on `[X,3X]`
with a fixed explicit constant. -/
theorem abs_norm_positivePrefixMean_sub_norm_le_nearTwistDistance
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (t : ℝ) {X Z : ℕ} (hX : 3 ≤ X) (hXZ : X ≤ Z)
    (hZ : Z ≤ 3 * X) (ht : t ≠ 0) (ht_small : |t| ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hdist : pretentiousDistSq f (archimedeanTwist t) (3 * X) ≤ M) :
    |‖positivePrefixMean f Z‖ - ‖positivePrefixMean f X‖| ≤
      realGSNearTwistNormConstant /
          Real.log (X : ℝ) *
        Real.exp
          (Real.sqrt
              (2 * M * PrimeEstimates.primeReciprocals (3 * X)) + 8) := by
  let C : ℝ := HalberstamScratch.explicitMassConstant 2 1 + 1
  let E : ℝ := Real.exp
    (Real.sqrt (2 * M * PrimeEstimates.primeReciprocals (3 * X)) + 8)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg
      (HalberstamScratch.explicitMassConstant_nonneg (by norm_num) (by norm_num))
      zero_le_one
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogZ : 0 < Real.log (Z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  have hlogmono : Real.log (X : ℝ) ≤ Real.log (Z : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hXZ)
  have hprimeMono (N : ℕ) (hN : N ≤ 3 * X) :
      PrimeEstimates.primeReciprocals N ≤
        PrimeEstimates.primeReciprocals (3 * X) := by
    have hi := PrimeEstimates.reciprocalPrimeInterval_nonneg N (3 * X)
    rw [PrimeEstimates.reciprocalPrimeInterval_eq_sub hN] at hi
    linarith
  have heuler (N : ℕ) (hN : N ≤ 3 * X) :
      gsEulerExponent (archimedeanUntwist f t) N ≤
        Real.sqrt
            (2 * M * PrimeEstimates.primeReciprocals (3 * X)) + 8 := by
    have hdistN : pretentiousDistSq f (archimedeanTwist t) N ≤ M := by
      exact (pretentiousDistSq_mono hN
        (fun n _ ↦ hbound n)
        (fun n hn ↦ (norm_archimedeanTwist hn.pos t).le)).trans hdist
    have hdist0 : 0 ≤ pretentiousDistSq f (archimedeanTwist t) N := by
      exact pretentiousDistSq_nonneg
        (fun n _ ↦ hbound n)
        (fun n hn ↦ (norm_archimedeanTwist hn.pos t).le)
    have hp0 : 0 ≤ PrimeEstimates.primeReciprocals N :=
      PrimeEstimates.primeReciprocals_nonneg N
    have hp3 : 0 ≤ PrimeEstimates.primeReciprocals (3 * X) :=
      PrimeEstimates.primeReciprocals_nonneg (3 * X)
    have hprod :
        2 * pretentiousDistSq f (archimedeanTwist t) N *
            PrimeEstimates.primeReciprocals N ≤
          2 * M * PrimeEstimates.primeReciprocals (3 * X) := by
      calc
        2 * pretentiousDistSq f (archimedeanTwist t) N *
              PrimeEstimates.primeReciprocals N ≤
            2 * M * PrimeEstimates.primeReciprocals N := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hdistN (by norm_num)) hp0
        _ ≤ 2 * M * PrimeEstimates.primeReciprocals (3 * X) := by
          exact mul_le_mul_of_nonneg_left (hprimeMono N hN)
            (mul_nonneg (by norm_num) hM)
    exact (gsEulerExponent_archimedeanUntwist_le hbound t N).trans
      (add_le_add (Real.sqrt_le_sqrt hprod) le_rfl)
  have hexpZ : Real.exp (gsEulerExponent (archimedeanUntwist f t) Z) ≤ E := by
    exact Real.exp_le_exp.mpr (heuler Z hZ)
  have hexpX : Real.exp (gsEulerExponent (archimedeanUntwist f t) X) ≤ E := by
    exact Real.exp_le_exp.mpr (heuler X (by omega))
  have hbase := abs_norm_positivePrefixMean_sub_norm_le_nearTwistEuler
    hmul hbound t (show 2 ≤ X by omega) hXZ ht ht_small
  have htermZ :
      4 * C / Real.log (Z : ℝ) *
          Real.exp (gsEulerExponent (archimedeanUntwist f t) Z) ≤
        4 * (C / Real.log (X : ℝ) * E) := by
    have hinv : (Real.log (Z : ℝ))⁻¹ ≤ (Real.log (X : ℝ))⁻¹ :=
      by simpa only [one_div] using one_div_le_one_div_of_le hlogX hlogmono
    calc
      4 * C / Real.log (Z : ℝ) *
          Real.exp (gsEulerExponent (archimedeanUntwist f t) Z) =
          4 * C * (Real.log (Z : ℝ))⁻¹ *
            Real.exp (gsEulerExponent (archimedeanUntwist f t) Z) := by ring
      _ ≤ 4 * C * (Real.log (X : ℝ))⁻¹ * E := by
        gcongr
      _ = 4 * (C / Real.log (X : ℝ) * E) := by ring
  have htermTail :
      (1 / (X : ℝ)) *
          (C * (Z : ℝ) / Real.log (Z : ℝ) *
            Real.exp (gsEulerExponent (archimedeanUntwist f t) Z)) ≤
        3 * (C / Real.log (X : ℝ) * E) := by
    have hratio : (Z : ℝ) / X ≤ 3 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < X)).2
      exact_mod_cast hZ
    have hinv : (Real.log (Z : ℝ))⁻¹ ≤ (Real.log (X : ℝ))⁻¹ :=
      by simpa only [one_div] using one_div_le_one_div_of_le hlogX hlogmono
    calc
      (1 / (X : ℝ)) *
          (C * (Z : ℝ) / Real.log (Z : ℝ) *
            Real.exp (gsEulerExponent (archimedeanUntwist f t) Z)) =
          ((Z : ℝ) / X) * C * (Real.log (Z : ℝ))⁻¹ *
            Real.exp (gsEulerExponent (archimedeanUntwist f t) Z) := by ring
      _ ≤ 3 * C * (Real.log (X : ℝ))⁻¹ * E := by
        gcongr
      _ = 3 * (C / Real.log (X : ℝ) * E) := by ring
  have htermX :
      4 * C / Real.log (X : ℝ) *
          Real.exp (gsEulerExponent (archimedeanUntwist f t) X) ≤
        4 * (C / Real.log (X : ℝ) * E) := by
    have hcoef : 0 ≤ 4 * C / Real.log (X : ℝ) :=
      div_nonneg (mul_nonneg (by norm_num) hC) hlogX.le
    calc
      4 * C / Real.log (X : ℝ) *
          Real.exp (gsEulerExponent (archimedeanUntwist f t) X) ≤
          (4 * C / Real.log (X : ℝ)) * E :=
        mul_le_mul_of_nonneg_left hexpX hcoef
      _ = 4 * (C / Real.log (X : ℝ) * E) := by ring
  change |‖positivePrefixMean f Z‖ - ‖positivePrefixMean f X‖| ≤
    11 * C / Real.log (X : ℝ) * E
  change |‖positivePrefixMean f Z‖ - ‖positivePrefixMean f X‖| ≤ _ at hbase
  calc
    |‖positivePrefixMean f Z‖ - ‖positivePrefixMean f X‖| ≤ _ := hbase
    _ ≤ 4 * (C / Real.log (X : ℝ) * E) +
          3 * (C / Real.log (X : ℝ) * E) +
          4 * (C / Real.log (X : ℝ) * E) :=
      add_le_add (add_le_add htermZ htermTail) htermX
    _ = 11 * C / Real.log (X : ℝ) * E := by ring

end

end Erdos67b
