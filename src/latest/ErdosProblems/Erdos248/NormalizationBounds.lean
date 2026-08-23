import ErdosProblems.Erdos248.Normalization

/-!
# Erdős Problem 248: explicit normalization inequalities

This file discharges the elementary scalar inequalities left by the exact
Y-diagonal and varying-box cross decompositions.  The deliberately generous
pre-sieve cutoff `2^(100*K)` absorbs every polynomial and fixed exponential
loss in the dimension.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

theorem exp_eight_le_two_pow_thirteen :
    Real.exp 8 ≤ (2 : ℝ) ^ 13 := by
  calc
    Real.exp 8 = Real.exp 1 ^ (8 : ℕ) := by
      simpa using (Real.exp_nat_mul (1 : ℝ) 8)
    _ ≤ (3 : ℝ) ^ 8 := by
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 8
    _ ≤ (2 : ℝ) ^ 13 := by norm_num

theorem nat_sq_le_two_pow_two_mul (K : ℕ) :
    K ^ 2 ≤ 2 ^ (2 * K) := by
  calc
    K ^ 2 ≤ (2 ^ K) ^ 2 :=
      Nat.pow_le_pow_left K.lt_two_pow_self.le 2
    _ = 2 ^ (2 * K) := by
      rw [← pow_mul]
      congr 1
      omega

theorem sixteen_mul_sq_le_tinyCutoff {K : ℕ} (hK : 0 < K) :
    16 * K ^ 2 ≤ tinyCutoff K := by
  calc
    16 * K ^ 2 ≤ 16 * 2 ^ (2 * K) :=
      Nat.mul_le_mul_left 16 (nat_sq_le_two_pow_two_mul K)
    _ = 2 ^ (4 + 2 * K) := by
      rw [pow_add]
      norm_num
    _ ≤ 2 ^ (100 * K) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = tinyCutoff K := by rfl

theorem two_pow_sixteen_mul_sq_le_tinyCutoff {K : ℕ} (hK : 0 < K) :
    2 ^ 16 * K ^ 2 ≤ tinyCutoff K := by
  calc
    2 ^ 16 * K ^ 2 ≤ 2 ^ 16 * 2 ^ (2 * K) :=
      Nat.mul_le_mul_left (2 ^ 16) (nat_sq_le_two_pow_two_mul K)
    _ = 2 ^ (16 + 2 * K) := by rw [pow_add]
    _ ≤ 2 ^ (100 * K) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = tinyCutoff K := by rfl

theorem innerCollisionFactor_le_half {K : ℕ} (hK : 0 < K) :
    ((offDiagonalPairs (nearShifts K)).card : ℝ) *
        (8 / (tinyCutoff K : ℝ)) ≤ 1 / 2 := by
  have hD : (0 : ℝ) < tinyCutoff K := by
    exact_mod_cast tinyCutoff_pos K
  have hcard : ((offDiagonalPairs (nearShifts K)).card : ℝ) ≤ K ^ 2 := by
    exact_mod_cast offDiagonalPairs_near_card_le K
  have hnat : (16 : ℝ) * K ^ 2 ≤ tinyCutoff K := by
    exact_mod_cast sixteen_mul_sq_le_tinyCutoff hK
  rw [show ((offDiagonalPairs (nearShifts K)).card : ℝ) *
      (8 / (tinyCutoff K : ℝ)) =
        (8 * ((offDiagonalPairs (nearShifts K)).card : ℝ)) /
          tinyCutoff K by ring]
  apply (div_le_iff₀ hD).2
  nlinarith

theorem roughCrossSmallness {K : ℕ} (hK : 0 < K) :
    (8 * Real.exp 8 / (tinyCutoff K : ℝ)) *
        ((offDiagonalPairs (nearShifts K)).card : ℝ) ≤ 1 := by
  have hD : (0 : ℝ) < tinyCutoff K := by
    exact_mod_cast tinyCutoff_pos K
  have hcard : ((offDiagonalPairs (nearShifts K)).card : ℝ) ≤ K ^ 2 := by
    exact_mod_cast offDiagonalPairs_near_card_le K
  have hexp := exp_eight_le_two_pow_thirteen
  have hnat : ((2 ^ 16 * K ^ 2 : ℕ) : ℝ) ≤ tinyCutoff K := by
    exact_mod_cast two_pow_sixteen_mul_sq_le_tinyCutoff hK
  rw [show (8 * Real.exp 8 / (tinyCutoff K : ℝ)) *
      ((offDiagonalPairs (nearShifts K)).card : ℝ) =
        (8 * Real.exp 8 *
          ((offDiagonalPairs (nearShifts K)).card : ℝ)) /
            tinyCutoff K by ring]
  apply (div_le_iff₀ hD).2
  calc
    8 * Real.exp 8 *
        ((offDiagonalPairs (nearShifts K)).card : ℝ) ≤
        8 * (2 : ℝ) ^ 13 * K ^ 2 := by gcongr
    _ = ((2 ^ 16 * K ^ 2 : ℕ) : ℝ) := by norm_num
    _ ≤ 1 * tinyCutoff K := by simpa using hnat

theorem roughCrossTail_le_explicit {K : ℕ} (hK : 0 < K) :
    roughCrossTupleTotientSquareTail (nearShifts K) (tinyCutoff K)
        (globalRadius K) ≤
      3 * (8 * Real.exp 8 / (tinyCutoff K : ℝ)) * K ^ 2 := by
  calc
    roughCrossTupleTotientSquareTail (nearShifts K) (tinyCutoff K)
        (globalRadius K) ≤
        3 * (8 * Real.exp 8 / (tinyCutoff K : ℝ)) *
          ((offDiagonalPairs (nearShifts K)).card : ℝ) :=
      roughCrossTupleTotientSquareTail_le_three_mul
        (tinyCutoff_pos K) (roughCrossSmallness hK)
    _ ≤ 3 * (8 * Real.exp 8 / (tinyCutoff K : ℝ)) * K ^ 2 := by
      gcongr
      exact_mod_cast offDiagonalPairs_near_card_le K

theorem innerCollisionMass_le_half {K : ℕ} (hK : 0 < K) :
    innerCollisionMass K ≤ (1 / 2 : ℝ) * innerTupleMass K := by
  have hM : 0 ≤ innerTupleMass K := by
    unfold innerTupleMass reciprocalTotientTupleWeight
    positivity
  calc
    innerCollisionMass K ≤
        ((offDiagonalPairs (nearShifts K)).card : ℝ) *
          (∏ h : nearShifts K, innerCoordinateMajorant K h) *
            (8 / (tinyCutoff K : ℝ)) :=
      innerCollisionMass_le_majorant hK
    _ = innerTupleMass K *
        (((offDiagonalPairs (nearShifts K)).card : ℝ) *
          (8 / (tinyCutoff K : ℝ))) := by
      rw [innerTupleMass_eq_majorant_product]
      ring
    _ ≤ innerTupleMass K * (1 / 2 : ℝ) := by
      exact mul_le_mul_of_nonneg_left (innerCollisionFactor_le_half hK) hM
    _ = (1 / 2 : ℝ) * innerTupleMass K := by ring

theorem half_innerTupleMass_le_sub_collision {K : ℕ} (hK : 0 < K) :
    (1 / 2 : ℝ) * innerTupleMass K ≤
      innerTupleMass K - innerCollisionMass K := by
  linarith [innerCollisionMass_le_half hK]

theorem varyingMajorantProduct_le {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K : ℕ} (hreg : NormalizationRegular A K) :
    (∏ h : nearShifts K, varyingCoordinateMajorant K h) ≤
      6 ^ K * innerTupleMass K := by
  calc
    (∏ h : nearShifts K, varyingCoordinateMajorant K h) ≤
        ∏ h : nearShifts K, (6 * innerCoordinateMajorant K h) := by
      apply Finset.prod_le_prod
      · intro h hh
        unfold varyingCoordinateMajorant squarefreeCoprimeInvTotientMean
        positivity
      · intro h hh
        exact varyingCoordinateMajorant_le_six_inner hA hreg h
    _ = (∏ _h : nearShifts K, (6 : ℝ)) *
        ∏ h : nearShifts K, innerCoordinateMajorant K h := by
      rw [Finset.prod_mul_distrib]
    _ = 6 ^ K * innerTupleMass K := by
      simp [Fintype.card_coe, nearShifts_card,
        innerTupleMass_eq_majorant_product]

theorem cross_numeric_numerator_le_tinyCutoff {K : ℕ} (hK : 0 < K) :
    3 * 2 ^ 18 * K ^ 2 * 96 ^ K ≤ tinyCutoff K := by
  calc
    3 * 2 ^ 18 * K ^ 2 * 96 ^ K ≤
        2 ^ 20 * 2 ^ (2 * K) * 96 ^ K := by
      exact Nat.mul_le_mul
        (Nat.mul_le_mul (by norm_num) (nat_sq_le_two_pow_two_mul K))
        (le_refl _)
    _ = 2 ^ 20 * (384 : ℕ) ^ K := by
      rw [show 2 ^ (2 * K) = (4 : ℕ) ^ K by
        rw [pow_mul]
        norm_num]
      rw [mul_assoc, ← mul_pow]
      norm_num
    _ ≤ 2 ^ 20 * (512 : ℕ) ^ K := by
      gcongr
      norm_num
    _ = 2 ^ (20 + 9 * K) := by
      rw [show (512 : ℕ) = 2 ^ 9 by norm_num, ← pow_mul, pow_add]
    _ ≤ 2 ^ (100 * K) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = tinyCutoff K := by rfl

/-- After the coordinatewise factor `6^K`, the complete cross correction is
still at most one quarter of the inner diagonal lower bound. -/
theorem roughCrossTimesSixPow_le_quarterDiagonalScale {K : ℕ} (hK : 0 < K) :
    (3 * (8 * Real.exp 8 / (tinyCutoff K : ℝ)) * K ^ 2) * 6 ^ K ≤
      (1 / 4 : ℝ) * ((1 / 4 : ℝ) ^ K) ^ 2 := by
  have hD : (0 : ℝ) < tinyCutoff K := by
    exact_mod_cast tinyCutoff_pos K
  have hden : (0 : ℝ) < 4 * 16 ^ K := by positivity
  have hnat : (((3 * 2 ^ 18 * K ^ 2 * 96 ^ K : ℕ) : ℝ)) ≤
      tinyCutoff K := by
    exact_mod_cast cross_numeric_numerator_le_tinyCutoff hK
  have hbig :
      (3 * 8 * Real.exp 8 * K ^ 2 * 6 ^ K) * (4 * 16 ^ K) ≤
        tinyCutoff K := by
    calc
      (3 * 8 * Real.exp 8 * K ^ 2 * 6 ^ K) * (4 * 16 ^ K) ≤
          (3 * 8 * (2 : ℝ) ^ 13 * K ^ 2 * 6 ^ K) *
            (4 * 16 ^ K) := by gcongr; exact exp_eight_le_two_pow_thirteen
      _ = (((3 * 2 ^ 18 * K ^ 2 * 96 ^ K : ℕ) : ℝ)) := by
        push_cast
        have hp : (6 : ℝ) ^ K * 16 ^ K = 96 ^ K := by
          rw [← mul_pow]
          norm_num
        rw [show
          (3 * 8 * (2 : ℝ) ^ 13 * (K : ℝ) ^ 2 * (6 : ℝ) ^ K) *
              (4 * (16 : ℝ) ^ K) =
              3 * 2 ^ 18 * (K : ℝ) ^ 2 *
                ((6 : ℝ) ^ K * (16 : ℝ) ^ K) by
          norm_num
          ring, hp]
        norm_num
      _ ≤ tinyCutoff K := hnat
  rw [show (3 * (8 * Real.exp 8 / (tinyCutoff K : ℝ)) * K ^ 2) *
      6 ^ K = (3 * 8 * Real.exp 8 * K ^ 2 * 6 ^ K) /
        tinyCutoff K by ring]
  rw [show (1 / 4 : ℝ) * ((1 / 4 : ℝ) ^ K) ^ 2 =
      1 / (4 * 16 ^ K) by
    rw [div_pow]
    simp only [one_pow]
    rw [div_pow]
    simp only [one_pow]
    have hp : ((4 : ℝ) ^ K) ^ 2 = 16 ^ K := by
      rw [← pow_mul, show K * 2 = 2 * K by omega, pow_mul]
      norm_num
    rw [hp]
    ring]
  exact (div_le_div_iff₀ hD hden).2 (by simpa using hbig)

theorem innerTupleMass_pos {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K : ℕ} (hreg : NormalizationRegular A K) :
    0 < innerTupleMass K := by
  rw [innerTupleMass_eq_majorant_product]
  apply Finset.prod_pos
  intro h hh
  have hlower := (innerCoordinateMajorant_bounds hA hreg h).1
  have hδ := sieveDensity_pos K
  have hlog : 0 < Real.log (innerShiftRadius K h) :=
    Real.log_pos (by exact_mod_cast one_lt_innerShiftRadius K h)
  have : 0 < (3 / 4 : ℝ) * sieveDensity K *
      Real.log (innerShiftRadius K h) := by positivity
  exact this.trans_le hlower

theorem sieveDiagonal_lower {K : ℕ} (hK : 0 < K) :
    (((1 / 4 : ℝ) ^ K) ^ 2) *
        ((1 / 2 : ℝ) * innerTupleMass K) ≤
      maynardYDiagonalSum (nearShifts K) (globalRadius K)
        (preSieveModulus K) (sieveY K) := by
  calc
    (((1 / 4 : ℝ) ^ K) ^ 2) *
        ((1 / 2 : ℝ) * innerTupleMass K) ≤
        (((1 / 4 : ℝ) ^ K) ^ 2) *
          (innerTupleMass K - innerCollisionMass K) := by
      gcongr
      exact half_innerTupleMass_le_sub_collision hK
    _ ≤ maynardYDiagonalSum (nearShifts K) (globalRadius K)
        (preSieveModulus K) (sieveY K) :=
      inner_mass_sub_collision_mul_le_diagonal hK

theorem abs_sieveCrossCorrection_le_quarterDiagonal {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K : ℕ} (hreg : NormalizationRegular A K) :
    |incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
        (sieveDivisorSupport K) (sieveCoefficient K)| ≤
      (1 / 4 : ℝ) * (((1 / 4 : ℝ) ^ K) ^ 2) *
        innerTupleMass K := by
  have hK := hreg.1
  have htail := roughCrossTail_le_explicit hK
  have hvary := varyingMajorantProduct_le hA hreg
  have hM : 0 ≤ innerTupleMass K := (innerTupleMass_pos hA hreg).le
  calc
    |incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
        (sieveDivisorSupport K) (sieveCoefficient K)| ≤
        roughCrossTupleTotientSquareTail (nearShifts K) (tinyCutoff K)
            (globalRadius K) *
          ∏ h : nearShifts K, varyingCoordinateMajorant K h :=
      abs_sieve_crossCorrection_le_varying hK
    _ ≤ (3 * (8 * Real.exp 8 / (tinyCutoff K : ℝ)) * K ^ 2) *
        (6 ^ K * innerTupleMass K) := by
      apply mul_le_mul htail hvary
      · unfold varyingCoordinateMajorant squarefreeCoprimeInvTotientMean
        positivity
      · positivity
    _ = ((3 * (8 * Real.exp 8 / (tinyCutoff K : ℝ)) * K ^ 2) *
        6 ^ K) * innerTupleMass K := by ring
    _ ≤ ((1 / 4 : ℝ) * (((1 / 4 : ℝ) ^ K) ^ 2)) *
        innerTupleMass K := by
      exact mul_le_mul_of_nonneg_right
        (roughCrossTimesSixPow_le_quarterDiagonalScale hK) hM
    _ = (1 / 4 : ℝ) * (((1 / 4 : ℝ) ^ K) ^ 2) *
        innerTupleMass K := by ring

/-- The exact diagonal-minus-cross bracket in the CRT main term has a
strictly positive, fully explicit lower bound. -/
theorem quarterDiagonalMass_le_sieveBracket {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K : ℕ} (hreg : NormalizationRegular A K) :
    (1 / 4 : ℝ) * (((1 / 4 : ℝ) ^ K) ^ 2) * innerTupleMass K ≤
      maynardYDiagonalSum (nearShifts K) (globalRadius K)
          (preSieveModulus K) (sieveY K) -
        incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
          (sieveDivisorSupport K) (sieveCoefficient K) := by
  have hdiag := sieveDiagonal_lower hreg.1
  have hcross := abs_sieveCrossCorrection_le_quarterDiagonal hA hreg
  have hcrossSelf :
      incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
          (sieveDivisorSupport K) (sieveCoefficient K) ≤
        |incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
          (sieveDivisorSupport K) (sieveCoefficient K)| := le_abs_self _
  nlinarith

theorem sieveBracket_pos {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K : ℕ} (hreg : NormalizationRegular A K) :
    0 < maynardYDiagonalSum (nearShifts K) (globalRadius K)
          (preSieveModulus K) (sieveY K) -
        incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
          (sieveDivisorSupport K) (sieveCoefficient K) := by
  have hlower := quarterDiagonalMass_le_sieveBracket hA hreg
  have hmass := innerTupleMass_pos hA hreg
  have hscale : 0 < (1 / 4 : ℝ) * (((1 / 4 : ℝ) ^ K) ^ 2) := by
    positivity
  exact (mul_pos hscale hmass).trans_le hlower

theorem log_innerShiftRadius_self (K : ℕ) :
    Real.log (innerShiftRadius K K) =
      ((50 * 100 ^ (100 * K - K - 1) : ℕ) : ℝ) * Real.log 2 := by
  rw [innerShiftRadius]
  push_cast
  rw [Real.log_pow]
  norm_num

theorem fourThousandOneHundredTwenty_mul_le_innerExponent
    {K : ℕ} (hK : 0 < K) :
    4120 * K ≤ 50 * 100 ^ (100 * K - K - 1) := by
  have hbase : K ≤ 100 ^ K := by
    calc
      K ≤ 2 ^ K := K.lt_two_pow_self.le
      _ ≤ 100 ^ K := Nat.pow_le_pow_left (by norm_num) K
  have hexponent : K + 2 ≤ 100 * K - K - 1 := by omega
  calc
    4120 * K ≤ 500000 * K := by gcongr <;> norm_num
    _ ≤ 500000 * 100 ^ K := Nat.mul_le_mul_left 500000 hbase
    _ = 50 * 100 ^ (K + 2) := by
      rw [pow_add]
      norm_num
      ring
    _ ≤ 50 * 100 ^ (100 * K - K - 1) :=
      Nat.mul_le_mul_left 50
        (Nat.pow_le_pow_right (by norm_num) hexponent)

/-- The all-endpoint Wirsing comparison is regular as soon as its absolute
constant is no larger than the dimension. -/
theorem normalizationRegular_of_le_dimension {A : ℝ} {K : ℕ}
    (hK : 0 < K) (hAK : A ≤ K) :
    NormalizationRegular A K := by
  refine ⟨hK, ?_⟩
  rw [normalizationError, log_tinyCutoff,
    log_innerShiftRadius_self]
  have hlogLower : (1 / 2 : ℝ) ≤ Real.log 2 := by
    exact Real.log_two_gt_d9.le.trans' (by norm_num)
  have hlogPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKone : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hAlog : A ≤ 2 * (K : ℝ) * Real.log 2 := by
    calc
      A ≤ K := hAK
      _ ≤ 2 * (K : ℝ) * Real.log 2 := by nlinarith
  have honeLog : Real.log 2 ≤ (K : ℝ) * Real.log 2 := by
    nlinarith
  have hinside :
      A + ((100 * K : ℕ) : ℝ) * Real.log 2 + Real.log 2 ≤
        103 * (K : ℝ) * Real.log 2 := by
    push_cast
    nlinarith
  have hcoefficient : (4120 : ℝ) * K ≤
      ((50 * 100 ^ (100 * K - K - 1) : ℕ) : ℝ) := by
    exact_mod_cast fourThousandOneHundredTwenty_mul_le_innerExponent hK
  calc
    4 * (10 *
        (A + ((100 * K : ℕ) : ℝ) * Real.log 2 + Real.log 2)) =
        40 * (A + ((100 * K : ℕ) : ℝ) * Real.log 2 + Real.log 2) := by
      ring
    _ ≤ 40 * (103 * (K : ℝ) * Real.log 2) := by gcongr
    _ = 4120 * (K : ℝ) * Real.log 2 := by ring
    _ ≤ ((50 * 100 ^ (100 * K - K - 1) : ℕ) : ℝ) *
        Real.log 2 := mul_le_mul_of_nonneg_right hcoefficient hlogPos.le

end Erdos248
