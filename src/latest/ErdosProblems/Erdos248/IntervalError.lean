import ErdosProblems.Erdos248.NormalizationBounds

/-!
# Erdős Problem 248: absorption of finite CRT errors

The interval-counting error is bounded by the square of the active divisor
support times a polylogarithmic coefficient envelope.  The first coordinate
radius already has binary exponent `100^(100*K-1)`, which absorbs the
primorial, cutoff loss, and coefficient envelope together.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

theorem intervalExponent_le_two_pow (K : ℕ) :
    intervalExponent K ≤ 2 ^ (700 * K) := by
  calc
    intervalExponent K = 100 ^ (100 * K) := rfl
    _ ≤ 128 ^ (100 * K) := Nat.pow_le_pow_left (by norm_num) _
    _ = 2 ^ (700 * K) := by
      rw [show (128 : ℕ) = 2 ^ 7 by norm_num, ← pow_mul]
      congr 1
      omega

theorem polylogNaturalEnvelope_le_two_pow (K : ℕ) :
    (2 * intervalExponent K) ^ (4 * K ^ 2) ≤
      2 ^ ((700 * K + 1) * (4 * K ^ 2)) := by
  have hbase : 2 * intervalExponent K ≤ 2 ^ (700 * K + 1) := by
    calc
      2 * intervalExponent K ≤ 2 * 2 ^ (700 * K) :=
        Nat.mul_le_mul_left 2 (intervalExponent_le_two_pow K)
      _ = 2 ^ (700 * K + 1) := by
        rw [pow_add]
        norm_num
        ring
  calc
    (2 * intervalExponent K) ^ (4 * K ^ 2) ≤
        (2 ^ (700 * K + 1)) ^ (4 * K ^ 2) :=
      Nat.pow_le_pow_left hbase _
    _ = 2 ^ ((700 * K + 1) * (4 * K ^ 2)) := by
      rw [← pow_mul]

theorem cube_le_two_pow_three_mul (K : ℕ) :
    K ^ 3 ≤ 2 ^ (3 * K) := by
  calc
    K ^ 3 ≤ (2 ^ K) ^ 3 := Nat.pow_le_pow_left K.lt_two_pow_self.le 3
    _ = 2 ^ (3 * K) := by
      rw [← pow_mul]
      congr 1
      omega

theorem nuisanceExponent_le_two_pow {K : ℕ} (hK : 0 < K) :
    2 * tinyCutoff K + 2 + 4 * K +
        (700 * K + 1) * (4 * K ^ 2) ≤
      2 ^ (100 * K + 20) := by
  let B : ℕ := 2 ^ (100 * K + 18)
  have hcut : 2 * tinyCutoff K ≤ B := by
    dsimp [B, tinyCutoff]
    rw [show 2 * 2 ^ (100 * K) = 2 ^ (100 * K + 1) by
      rw [pow_add]
      norm_num
      ring]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have htwo : 2 ≤ B := by
    have hone : 1 ≤ tinyCutoff K := Nat.one_le_iff_ne_zero.mpr
      (tinyCutoff_pos K).ne'
    exact (Nat.mul_le_mul_left 2 hone).trans hcut
  have hfourK : 4 * K ≤ B := by
    calc
      4 * K ≤ 4 * 2 ^ K := Nat.mul_le_mul_left 4 K.lt_two_pow_self.le
      _ = 2 ^ (K + 2) := by
        rw [pow_add]
        norm_num
        ring
      _ ≤ B := by
        dsimp [B]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpolyCoeff :
      (700 * K + 1) * (4 * K ^ 2) ≤ 4096 * K ^ 3 := by
    calc
      (700 * K + 1) * (4 * K ^ 2) ≤
          (701 * K) * (4 * K ^ 2) := by
        gcongr
        omega
      _ = 2804 * K ^ 3 := by ring
      _ ≤ 4096 * K ^ 3 := Nat.mul_le_mul_right (K ^ 3) (by norm_num)
  have hpoly : (700 * K + 1) * (4 * K ^ 2) ≤ B := by
    calc
      (700 * K + 1) * (4 * K ^ 2) ≤ 4096 * K ^ 3 := hpolyCoeff
      _ ≤ 4096 * 2 ^ (3 * K) :=
        Nat.mul_le_mul_left 4096 (cube_le_two_pow_three_mul K)
      _ = 2 ^ (3 * K + 12) := by
        rw [pow_add]
        norm_num
        ring
      _ ≤ B := by
        dsimp [B]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
  calc
    2 * tinyCutoff K + 2 + 4 * K +
        (700 * K + 1) * (4 * K ^ 2) ≤ B + B + B + B := by
      exact Nat.add_le_add
        (Nat.add_le_add (Nat.add_le_add hcut htwo) hfourK) hpoly
    _ = 4 * B := by ring
    _ = 2 ^ (100 * K + 20) := by
      dsimp [B]
      rw [pow_add]
      norm_num
      ring

theorem two_pow_nuisance_le_firstRadiusExponent {K : ℕ} (hK : 0 < K) :
    2 ^ (100 * K + 20) ≤ 100 ^ (100 * K - 1) := by
  calc
    2 ^ (100 * K + 20) ≤ 2 ^ (600 * K - 6) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 64 ^ (100 * K - 1) := by
      rw [show (64 : ℕ) = 2 ^ 6 by norm_num, ← pow_mul]
      congr 1
      omega
    _ ≤ 100 ^ (100 * K - 1) := Nat.pow_le_pow_left (by norm_num) _

theorem firstRadiusExponent_le_budget {K : ℕ} (hK : 0 < K) :
    100 ^ (100 * K - 1) ≤ radiusExponentBudget K := by
  unfold radiusExponentBudget
  have hmem : 1 ∈ nearShifts K := mem_nearShifts.mpr ⟨by omega, hK⟩
  simpa using (Finset.single_le_sum
    (s := nearShifts K) (f := fun k => 100 ^ (100 * K - k))
    (fun k hk => Nat.zero_le _) hmem)

theorem nuisanceExponent_le_radiusBudget {K : ℕ} (hK : 0 < K) :
    2 * tinyCutoff K + 2 + 4 * K +
        (700 * K + 1) * (4 * K ^ 2) ≤ radiusExponentBudget K := by
  exact (nuisanceExponent_le_two_pow hK).trans
    ((two_pow_nuisance_le_firstRadiusExponent hK).trans
      (firstRadiusExponent_le_budget hK))

theorem one_add_log_globalRadius_le_natural (K : ℕ) :
    1 + Real.log (globalRadius K) ≤ (2 * intervalExponent K : ℕ) := by
  have hM : (1 : ℝ) ≤ intervalExponent K := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (intervalExponent_pos K).ne')
  have hlogTwo : Real.log 2 ≤ 1 :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  rw [globalRadius, intervalStart]
  push_cast
  rw [Real.log_pow]
  nlinarith

theorem polylogCoefficientEnvelope_le_natural (K : ℕ) :
    (1 + Real.log (globalRadius K)) ^ (4 * K ^ 2) ≤
      ((2 * intervalExponent K) ^ (4 * K ^ 2) : ℕ) := by
  push_cast
  have hbase :
      1 + Real.log (globalRadius K) ≤ (2 : ℝ) * intervalExponent K := by
    simpa using one_add_log_globalRadius_le_natural K
  exact pow_le_pow_left₀ (by positivity) hbase _

theorem nuisanceNaturalProduct_le_radiusProduct {K : ℕ} (hK : 0 < K) :
    preSieveModulus K * 4 * 16 ^ K *
        (2 * intervalExponent K) ^ (4 * K ^ 2) ≤
      radiusProduct K := by
  have hW : preSieveModulus K ≤ 2 ^ (2 * tinyCutoff K) := by
    calc
      preSieveModulus K = primorial (tinyCutoff K) := rfl
      _ ≤ 4 ^ tinyCutoff K := primorial_le_four_pow _
      _ = 2 ^ (2 * tinyCutoff K) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hpoly := polylogNaturalEnvelope_le_two_pow K
  calc
    preSieveModulus K * 4 * 16 ^ K *
        (2 * intervalExponent K) ^ (4 * K ^ 2) ≤
        2 ^ (2 * tinyCutoff K) * 4 * 16 ^ K *
          2 ^ ((700 * K + 1) * (4 * K ^ 2)) := by
      exact Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul hW (le_refl 4)) (le_refl _)) hpoly
    _ = 2 ^ (2 * tinyCutoff K + 2 + 4 * K +
        (700 * K + 1) * (4 * K ^ 2)) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
        show (16 : ℕ) ^ K = 2 ^ (4 * K) by
          rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]]
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 1
    _ ≤ 2 ^ radiusExponentBudget K :=
      Nat.pow_le_pow_right (by norm_num) (nuisanceExponent_le_radiusBudget hK)
    _ = radiusProduct K := (radiusProduct_eq_pow K).symm

theorem one_le_innerCoordinateMajorant (K : ℕ) (h : nearShifts K) :
    1 ≤ innerCoordinateMajorant K h := by
  have hone : 1 ∈ innerCoordinateSupport K h := by
    rw [innerCoordinateSupport, Finset.mem_filter]
    exact ⟨Finset.mem_Icc.mpr
      ⟨by norm_num, Nat.one_le_iff_ne_zero.mpr
        (innerShiftRadius_pos K h).ne'⟩, by simp⟩
  calc
    (1 : ℝ) = (1 : ℝ) / Nat.totient 1 := by norm_num
    _ ≤ ∑ n ∈ innerCoordinateSupport K h,
        (1 : ℝ) / Nat.totient n := by
      exact Finset.single_le_sum
        (s := innerCoordinateSupport K h)
        (f := fun n => (1 : ℝ) / Nat.totient n)
        (fun n hn => by positivity) hone
    _ = innerCoordinateMajorant K h :=
      innerCoordinateMass_eq_majorant K h

theorem one_le_innerTupleMass (K : ℕ) :
    1 ≤ innerTupleMass K := by
  rw [innerTupleMass_eq_majorant_product]
  simpa only [Finset.prod_const_one] using
    Finset.prod_le_prod (fun h _ => zero_le_one)
      (fun h _ => one_le_innerCoordinateMajorant K h)

theorem abs_sieveIntervalError_le_envelope {K : ℕ} (hK : 0 < K) :
    |compatibleDivisorPairErrorSum (nearShifts K) (sieveDivisorSupport K)
        0 (preSieveModulus K) (intervalStart K) (sieveCoefficient K)| ≤
      (radiusProduct K : ℝ) ^ 2 *
        (1 + Real.log (globalRadius K)) ^ (4 * K ^ 2) := by
  have herr := abs_compatibleDivisorPairErrorSum_le_coefficientMass
    (D := sieveDivisorSupport K) (lambda := sieveCoefficient K)
    (R := globalRadius K) (v := 0) (N := intervalStart K)
    (preSieveModulus_pos K) (sieveDivisorSupport_isMaynard K)
  refine herr.trans (sieveCoefficientMass_le_radiusProduct hK |>.trans_eq ?_)
  rw [← pow_mul]
  congr 2
  omega

theorem scaled_abs_sieveIntervalError_le_radiusCube {K : ℕ} (hK : 0 < K) :
    |compatibleDivisorPairErrorSum (nearShifts K) (sieveDivisorSupport K)
        0 (preSieveModulus K) (intervalStart K) (sieveCoefficient K)| *
        ((preSieveModulus K : ℝ) * 4 * 16 ^ K) ≤
      (radiusProduct K : ℝ) ^ 3 := by
  have herr := abs_sieveIntervalError_le_envelope hK
  have hpoly := polylogCoefficientEnvelope_le_natural K
  have hnuis :
      (preSieveModulus K : ℝ) * 4 * 16 ^ K *
          (((2 * intervalExponent K) ^ (4 * K ^ 2) : ℕ) : ℝ) ≤
        radiusProduct K := by
    exact_mod_cast nuisanceNaturalProduct_le_radiusProduct hK
  have hfactor : 0 ≤ (preSieveModulus K : ℝ) * 4 * 16 ^ K := by positivity
  have hR : 0 ≤ (radiusProduct K : ℝ) := by positivity
  calc
    |compatibleDivisorPairErrorSum (nearShifts K) (sieveDivisorSupport K)
        0 (preSieveModulus K) (intervalStart K) (sieveCoefficient K)| *
        ((preSieveModulus K : ℝ) * 4 * 16 ^ K) ≤
        ((radiusProduct K : ℝ) ^ 2 *
          (1 + Real.log (globalRadius K)) ^ (4 * K ^ 2)) *
            ((preSieveModulus K : ℝ) * 4 * 16 ^ K) :=
      mul_le_mul_of_nonneg_right herr hfactor
    _ = (radiusProduct K : ℝ) ^ 2 *
        (((preSieveModulus K : ℝ) * 4 * 16 ^ K) *
          (1 + Real.log (globalRadius K)) ^ (4 * K ^ 2)) := by ring
    _ ≤ (radiusProduct K : ℝ) ^ 2 *
        (((preSieveModulus K : ℝ) * 4 * 16 ^ K) *
          (((2 * intervalExponent K) ^ (4 * K ^ 2) : ℕ) : ℝ)) := by
      gcongr
    _ ≤ (radiusProduct K : ℝ) ^ 2 * radiusProduct K := by
      gcongr
    _ = (radiusProduct K : ℝ) ^ 3 := by ring

theorem scaled_abs_sieveIntervalError_lt_intervalStart {K : ℕ} (hK : 0 < K) :
    |compatibleDivisorPairErrorSum (nearShifts K) (sieveDivisorSupport K)
        0 (preSieveModulus K) (intervalStart K) (sieveCoefficient K)| *
        ((preSieveModulus K : ℝ) * 4 * 16 ^ K) < intervalStart K := by
  have hscaled := scaled_abs_sieveIntervalError_le_radiusCube hK
  have hRone : 1 ≤ radiusProduct K := by
    rw [radiusProduct_eq_pow]
    exact Nat.one_le_pow (radiusExponentBudget K) 2 (by norm_num)
  have hcubepow : radiusProduct K ^ 3 ≤ radiusProduct K ^ 99 :=
    pow_le_pow_right' hRone (by norm_num)
  have hpow := radiusProduct_pow_lt_intervalStart hK
  exact hscaled.trans_lt (by exact_mod_cast hcubepow.trans_lt hpow)

end Erdos248
