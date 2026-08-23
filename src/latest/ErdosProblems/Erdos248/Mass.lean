import ErdosProblems.Erdos248.IntervalError

/-!
# Erdős Problem 248: positivity of the sieve mass

The lower bound for the exact `Y`-diagonal dominates both the
cross-coordinate correction and the finite interval-counting error.  Thus
the square-divisor weight has strictly positive total mass on the dyadic
interval and can be normalized to a probability measure.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

theorem inverse_diagonal_scale_le_sieveBracket {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K : ℕ} (hreg : NormalizationRegular A K) :
    1 / (4 * 16 ^ K) ≤
      maynardYDiagonalSum (nearShifts K) (globalRadius K)
          (preSieveModulus K) (sieveY K) -
        incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
          (sieveDivisorSupport K) (sieveCoefficient K) := by
  have hlower := quarterDiagonalMass_le_sieveBracket hA hreg
  have hone := one_le_innerTupleMass K
  calc
    (1 : ℝ) / (4 * 16 ^ K) =
        (1 / 4 : ℝ) * (((1 / 4 : ℝ) ^ K) ^ 2) := by
      symm
      rw [div_pow]
      simp only [one_pow]
      rw [div_pow]
      simp only [one_pow]
      have hp : ((4 : ℝ) ^ K) ^ 2 = 16 ^ K := by
        rw [← pow_mul, show K * 2 = 2 * K by omega, pow_mul]
        norm_num
      rw [hp]
      ring
    _ ≤ (1 / 4 : ℝ) * (((1 / 4 : ℝ) ^ K) ^ 2) *
        innerTupleMass K := by
      have hscale : 0 ≤ (1 / 4 : ℝ) * (((1 / 4 : ℝ) ^ K) ^ 2) := by
        positivity
      simpa using mul_le_mul_of_nonneg_left hone hscale
    _ ≤ _ := hlower

theorem abs_sieveIntervalError_lt_sieveMain {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K : ℕ} (hreg : NormalizationRegular A K) :
    |compatibleDivisorPairErrorSum (nearShifts K) (sieveDivisorSupport K)
        0 (preSieveModulus K) (intervalStart K) (sieveCoefficient K)| <
      compatibleDivisorPairMainSum (nearShifts K) (sieveDivisorSupport K)
        (preSieveModulus K) (intervalStart K) (sieveCoefficient K) := by
  let E : ℝ := compatibleDivisorPairErrorSum (nearShifts K)
    (sieveDivisorSupport K) 0 (preSieveModulus K) (intervalStart K)
      (sieveCoefficient K)
  let B : ℝ := maynardYDiagonalSum (nearShifts K) (globalRadius K)
      (preSieveModulus K) (sieveY K) -
    incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
      (sieveDivisorSupport K) (sieveCoefficient K)
  have hK : 0 < K := hreg.1
  have hW : (0 : ℝ) < preSieveModulus K := by
    exact_mod_cast preSieveModulus_pos K
  have hx : (0 : ℝ) < intervalStart K := by
    exact_mod_cast intervalStart_pos K
  have hs : (0 : ℝ) < 4 * 16 ^ K := by positivity
  have hfactor : (0 : ℝ) < (preSieveModulus K : ℝ) * 4 * 16 ^ K := by
    positivity
  have hscaled : |E| *
      ((preSieveModulus K : ℝ) * 4 * 16 ^ K) < intervalStart K := by
    simpa [E] using scaled_abs_sieveIntervalError_lt_intervalStart hK
  have herror : |E| <
      (intervalStart K : ℝ) /
        ((preSieveModulus K : ℝ) * 4 * 16 ^ K) := by
    exact (lt_div_iff₀ hfactor).2 hscaled
  have hbracket : 1 / (4 * 16 ^ K) ≤ B := by
    simpa [B] using inverse_diagonal_scale_le_sieveBracket hA hreg
  have hcompare :
      (intervalStart K : ℝ) /
          ((preSieveModulus K : ℝ) * 4 * 16 ^ K) ≤
        (intervalStart K : ℝ) / preSieveModulus K * B := by
    calc
      (intervalStart K : ℝ) /
          ((preSieveModulus K : ℝ) * 4 * 16 ^ K) =
          ((intervalStart K : ℝ) / preSieveModulus K) *
            (1 / (4 * 16 ^ K)) := by
        field_simp
        <;> ring
      _ ≤ ((intervalStart K : ℝ) / preSieveModulus K) * B := by
        exact mul_le_mul_of_nonneg_left hbracket (by positivity)
  rw [sieveMain_eq_diagonal_sub_cross]
  simpa [E, B] using herror.trans_le hcompare

theorem sieveMass_pos {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K : ℕ} (hreg : NormalizationRegular A K) :
    0 < sieveMass K := by
  let M : ℝ := compatibleDivisorPairMainSum (nearShifts K)
    (sieveDivisorSupport K) (preSieveModulus K) (intervalStart K)
      (sieveCoefficient K)
  let E : ℝ := compatibleDivisorPairErrorSum (nearShifts K)
    (sieveDivisorSupport K) 0 (preSieveModulus K) (intervalStart K)
      (sieveCoefficient K)
  have hdom : |E| < M := by
    simpa [M, E] using abs_sieveIntervalError_lt_sieveMain hA hreg
  have hlower : -|E| ≤ E := neg_abs_le E
  rw [sieveMass_eq_main_add_error]
  change 0 < M + E
  linarith

end Erdos248
