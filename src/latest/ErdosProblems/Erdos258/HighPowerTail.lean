import ErdosProblems.Erdos258.HighPowerMoment
import ErdosProblems.Erdos248.MomentScaleBounds
import ErdosProblems.Erdos248.FinalReduction
import ErdosProblems.Erdos248.TailMarkov

/-!
# Uniform tail bound for sixth and higher prime powers
-/

open Erdos248 BoundedGaps.Maynard
open scoped BigOperators

namespace Erdos258

theorem sieveCoefficientMass_le_radiusCube {K : ℕ} (hK : 0 < K) :
    compatibleDivisorPairCoefficientMass (nearShifts K)
      (sieveDivisorSupport K) (sieveCoefficient K) ≤ (radiusProduct K : ℝ) ^ 3 := by
  have hnat : (2 * intervalExponent K) ^ (4 * K ^ 2) ≤ radiusProduct K := by
    have hpos : 0 < preSieveModulus K * 4 * 16 ^ K := by
      exact mul_pos (mul_pos (preSieveModulus_pos K) (by norm_num)) (by positivity)
    exact (Nat.le_mul_of_pos_left _ hpos).trans (nuisanceNaturalProduct_le_radiusProduct hK)
  have hpoly : (1 + Real.log (globalRadius K)) ^ (4 * K ^ 2) ≤ (radiusProduct K : ℝ) :=
    (polylogCoefficientEnvelope_le_natural K).trans (by exact_mod_cast hnat)
  calc
    compatibleDivisorPairCoefficientMass (nearShifts K)
        (sieveDivisorSupport K) (sieveCoefficient K) ≤
        (radiusProduct K : ℝ) ^ 2 * ((1 + Real.log (globalRadius K)) ^ (2 * K ^ 2)) ^ 2 :=
      sieveCoefficientMass_le_radiusProduct hK
    _ = (radiusProduct K : ℝ) ^ 2 * (1 + Real.log (globalRadius K)) ^ (4 * K ^ 2) := by
      rw [← pow_mul]
      congr 2
      ring
    _ ≤ (radiusProduct K : ℝ) ^ 2 * radiusProduct K :=
      mul_le_mul_of_nonneg_left hpoly (sq_nonneg _)
    _ = (radiusProduct K : ℝ) ^ 3 := by ring

theorem highPower_counting_error_lt_mass {A : ℝ} (hA : HasUniformWirsingBound A)
    {K : ℕ} (hreg : NormalizationRegular A K) :
    (shiftRadius K 1 : ℝ) ^ 6 *
      (2 * compatibleDivisorPairCoefficientMass (nearShifts K)
        (sieveDivisorSupport K) (sieveCoefficient K)) < sieveMass K := by
  have hR : (shiftRadius K 1 : ℝ) ≤ radiusProduct K := by
    exact_mod_cast largestRadius_le_radiusProduct hreg.1
  have hP : (1 : ℝ) ≤ radiusProduct K := by
    exact_mod_cast ((by norm_num : 1 ≤ 8192).trans (eightThousand_le_radiusProduct hreg.1))
  have hAcoef := sieveCoefficientMass_le_radiusCube hreg.1
  have hpow : (radiusProduct K : ℝ) ^ 5 ≤ (radiusProduct K : ℝ) ^ 6 :=
    pow_le_pow_right₀ hP (by norm_num)
  calc
    (shiftRadius K 1 : ℝ) ^ 6 *
        (2 * compatibleDivisorPairCoefficientMass (nearShifts K)
          (sieveDivisorSupport K) (sieveCoefficient K)) ≤
        (shiftRadius K 1 : ℝ) ^ 6 * (2 * (radiusProduct K : ℝ) ^ 3) := by gcongr
    _ = 2 * (shiftRadius K 1 : ℝ) ^ 4 *
        ((shiftRadius K 1 : ℝ) ^ 2 * (radiusProduct K : ℝ) ^ 3) := by ring
    _ ≤ 2 * (shiftRadius K 1 : ℝ) ^ 4 *
        ((radiusProduct K : ℝ) ^ 2 * (radiusProduct K : ℝ) ^ 3) := by gcongr
    _ = 2 * (shiftRadius K 1 : ℝ) ^ 4 * (radiusProduct K : ℝ) ^ 5 := by ring
    _ ≤ 2 * (shiftRadius K 1 : ℝ) ^ 4 * (radiusProduct K : ℝ) ^ 6 := by gcongr
    _ ≤ 16 * (shiftRadius K 1 : ℝ) ^ 4 * ((radiusProduct K : ℝ) ^ 6 * 257) := by
      nlinarith [show 0 ≤ (shiftRadius K 1 : ℝ) ^ 4 * (radiusProduct K : ℝ) ^ 6 by positivity]
    _ < sieveMass K := accumulatedFourthIntervalError_lt_sieveMass hA hreg le_rfl

noncomputable def highPowerMomentConstant : ℝ := 4 * (64 * highPowerGeometricConstant + 1)

theorem highPowerMomentConstant_pos : 0 < highPowerMomentConstant := by
  unfold highPowerMomentConstant
  nlinarith [highPowerGeometricConstant_nonneg]

theorem sieve_highPower_second_moment_le {A : ℝ} (hA : HasUniformWirsingBound A)
    {K : ℕ} (hreg : NormalizationRegular A K) (k : ℕ) :
    (∑ n ∈ Finset.Ico (intervalStart K) (2 * intervalStart K),
      sieveWeight K n * (highPrimePowerCount (n + k) (shiftRadius K 1) : ℝ) ^ 2) ≤
      highPowerMomentConstant * sieveMass K := by
  have hmass : 0 ≤ sieveMass K := (sieveMass_pos hA hreg).le
  have herr : 0 ≤ 2 * compatibleDivisorPairCoefficientMass (nearShifts K)
      (sieveDivisorSupport K) (sieveCoefficient K) := by
    unfold compatibleDivisorPairCoefficientMass
    positivity
  have h := highPower_second_moment_le (intervalStart K) (shiftRadius K 1) k
    (sieveWeight_nonneg K) hmass herr
    (fun p j hp hj _ => sieve_prime_pow_mass_le k hp (by omega))
  have he := highPower_counting_error_lt_mass hA hreg
  unfold highPowerMomentConstant
  nlinarith

noncomputable def highPowerBadMass (K T k : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (intervalStart K) (2 * intervalStart K),
    if T * k < highPrimePowerCount (n + k) (shiftRadius K 1) then sieveWeight K n else 0

theorem highPowerBadMass_nonneg (K T k : ℕ) : 0 ≤ highPowerBadMass K T k := by
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact sieveWeight_nonneg K n
  · exact le_rfl

theorem highPowerBadMass_mul_sq_le (K T k : ℕ) :
    ((T : ℝ) * k) ^ 2 * highPowerBadMass K T k ≤
      ∑ n ∈ Finset.Ico (intervalStart K) (2 * intervalStart K),
        sieveWeight K n * (highPrimePowerCount (n + k) (shiftRadius K 1) : ℝ) ^ 2 := by
  unfold highPowerBadMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hbad : T * k < highPrimePowerCount (n + k) (shiftRadius K 1)
  · rw [if_pos hbad, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (sieveWeight_nonneg K n)
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast hbad.le
  · rw [if_neg hbad, mul_zero]
    exact mul_nonneg (sieveWeight_nonneg K n) (sq_nonneg _)

theorem exists_uniform_highPower_tail : ∃ T : ℕ, 0 < T ∧
    ∀ {A : ℝ} {K : ℕ}, HasUniformWirsingBound A → NormalizationRegular A K →
      ∀ k, 1 ≤ k → highPowerBadMass K T k ≤ sieveMass K * (1 / (16 * (k : ℝ) ^ 2)) := by
  obtain ⟨T, hT, hTsq, _⟩ := exists_natural_moment_threshold
    highPowerMomentConstant highPowerMomentConstant_pos
  refine ⟨T, hT, ?_⟩
  intro A K hA hreg k hk
  apply tail_le_sixteenth_inv_sq_of_secondMoment
    (Nat.cast_pos.mpr hT) highPowerMomentConstant_pos (sieveMass_pos hA hreg).le
    (by exact_mod_cast hk) (highPowerBadMass_nonneg K T k) hTsq
  exact (highPowerBadMass_mul_sq_le K T k).trans (sieve_highPower_second_moment_le hA hreg k)

end Erdos258
