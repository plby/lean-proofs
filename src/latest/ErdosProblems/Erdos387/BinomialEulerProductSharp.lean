/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.BinomialEulerProduct
import ErdosProblems.Erdos387.RoughHarmonicEstimate
import Util.MertensThird

/-!
# A sharp tail bound for the binomial Euler correction

The original endpoint-independent comparison bounded the second-order
correction by `2`.  On the source scale this is much too expensive after
raising to the power `2 * k^2`.  The product over all integers in `(z,y]`
telescopes exactly, and gives the sharper bound `z / (z - 1)`.  At the
natural lower endpoint `z >= 2*k`, its logarithmic cost is only linear in
`k`.
-/

namespace Erdos387.BinomialEulerProductSharp

open scoped BigOperators
open Erdos851
open Erdos387
open Erdos387.BinomialEulerProduct

/-- The second-order correction telescopes on every integer interval. -/
theorem integerSecondOrderCorrection_Ioc_formula
    {z y : ℕ} (hz : 2 ≤ z) (hzy : z ≤ y) :
    (∏ n ∈ Finset.Ioc z y, secondOrderCorrection n) =
      (z : ℝ) * ((y : ℝ) - 1) /
        ((y : ℝ) * ((z : ℝ) - 1)) := by
  induction y, hzy using Nat.le_induction with
  | base =>
      simp
      have hzR : (0 : ℝ) < z := by positivity
      have hzm1 : (0 : ℝ) < (z : ℝ) - 1 := by
        exact sub_pos.mpr (by exact_mod_cast (show 1 < z by omega))
      field_simp [hzR.ne', hzm1.ne']
  | succ y hzy ih =>
      rw [Finset.prod_Ioc_succ_top (by omega), ih,
        secondOrderCorrection_eq (show 2 < y + 1 by omega)]
      have hzR : (0 : ℝ) < z := by positivity
      have hzm1 : (0 : ℝ) < (z : ℝ) - 1 := by
        exact sub_pos.mpr (by exact_mod_cast (show 1 < z by omega))
      have hyR : (0 : ℝ) < y := by
        exact_mod_cast (show 0 < y by omega)
      have hym1 : (0 : ℝ) < (y : ℝ) - 1 := by
        exact sub_pos.mpr (by exact_mod_cast (show 1 < y by omega))
      have hy1R : (0 : ℝ) < ((y + 1 : ℕ) : ℝ) := by positivity
      norm_num [Nat.cast_add, Nat.cast_one]
      rw [show (y : ℝ) + 1 - 2 = (y : ℝ) - 1 by ring]
      field_simp [hzR.ne', hzm1.ne', hyR.ne', hym1.ne', hy1R.ne']

/-- The prime correction product over `(z,y]` is bounded by the exact
all-integer telescoping tail. -/
theorem secondOrderCorrection_product_le_tail
    {z y : ℕ} (hz : 2 ≤ z) :
    (∏ p ∈ Erdos851.sievePrimes z y, secondOrderCorrection p) ≤
      (z : ℝ) / ((z : ℝ) - 1) := by
  by_cases hzy : z ≤ y
  · have hsubset : Erdos851.sievePrimes z y ⊆ Finset.Ioc z y := by
      intro p hp
      exact Finset.mem_Ioc.mpr
        ⟨(Erdos851.mem_sievePrimes.mp hp).1,
          (Erdos851.mem_sievePrimes.mp hp).2.1⟩
    have hprod :
        (∏ p ∈ Erdos851.sievePrimes z y, secondOrderCorrection p) ≤
          ∏ n ∈ Finset.Ioc z y, secondOrderCorrection n := by
      apply Finset.prod_le_prod_of_subset_of_one_le hsubset
      · intro p hp
        exact (zero_le_one.trans (one_le_secondOrderCorrection (by
          have hp' := Erdos851.mem_sievePrimes.mp hp
          omega)))
      · intro n hn _hnprime
        exact one_le_secondOrderCorrection (by
          have hn' := Finset.mem_Ioc.mp hn
          omega)
    rw [integerSecondOrderCorrection_Ioc_formula hz hzy] at hprod
    have hzR : (0 : ℝ) < z := by positivity
    have hzm1 : (0 : ℝ) < (z : ℝ) - 1 := by
      exact sub_pos.mpr (by exact_mod_cast (show 1 < z by omega))
    have hyR : (0 : ℝ) < y := by
      exact_mod_cast (show 0 < y by omega)
    calc
      (∏ p ∈ Erdos851.sievePrimes z y, secondOrderCorrection p) ≤
          (z : ℝ) * ((y : ℝ) - 1) /
            ((y : ℝ) * ((z : ℝ) - 1)) := hprod
      _ ≤ (z : ℝ) / ((z : ℝ) - 1) := by
        rw [div_le_div_iff₀ (mul_pos hyR hzm1) hzm1]
        nlinarith
  · have hempty : Erdos851.sievePrimes z y = ∅ := by
      ext p
      simp only [Erdos851.mem_sievePrimes, Finset.notMem_empty, iff_false]
      omega
    rw [hempty]
    simp only [Finset.prod_empty]
    have hzm1 : (0 : ℝ) < (z : ℝ) - 1 := by
      exact sub_pos.mpr (by exact_mod_cast (show 1 < z by omega))
    rw [le_div_iff₀ hzm1]
    norm_num

/-- Sharp finite comparison with the one-shift inverse Euler product. -/
theorem binomial_inverseLocalEulerProduct_le_tail
    {k z y : ℕ} (hk : 1 ≤ k) (hz : 2 * k ≤ z) :
    inverseLocalEulerProduct (fun p ↦ binomialSieveNu k p) z y ≤
      inverseLocalEulerProduct oneShiftDensity z y ^ k *
        ((z : ℝ) / ((z : ℝ) - 1)) ^ (2 * k ^ 2) := by
  simp only [inverseLocalEulerProduct]
  calc
    (∏ p ∈ Erdos851.sievePrimes z y, (1 - binomialSieveNu k p)⁻¹) ≤
        ∏ p ∈ Erdos851.sievePrimes z y,
          ((1 - oneShiftDensity p)⁻¹ ^ k *
            secondOrderCorrection p ^ (2 * k ^ 2)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp' := Erdos851.mem_sievePrimes.mp hp
        have hklt : k < p := by omega
        rw [binomialSieveNu_prime hp'.2.2]
        exact inv_nonneg.mpr (sub_nonneg.mpr (by
          rw [div_le_one (by exact_mod_cast hp'.2.2.pos)]
          exact_mod_cast hklt.le))
      · intro p hp
        exact binomial_inverseLocalFactor_le hk
          (Erdos851.mem_sievePrimes.mp hp).2.2 (by
            have hp' := Erdos851.mem_sievePrimes.mp hp
            omega)
    _ = (∏ p ∈ Erdos851.sievePrimes z y, (1 - oneShiftDensity p)⁻¹) ^ k *
          (∏ p ∈ Erdos851.sievePrimes z y, secondOrderCorrection p) ^
            (2 * k ^ 2) := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow]
    _ ≤ (∏ p ∈ Erdos851.sievePrimes z y, (1 - oneShiftDensity p)⁻¹) ^ k *
          ((z : ℝ) / ((z : ℝ) - 1)) ^ (2 * k ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_left₀ (by
          apply Finset.prod_nonneg
          intro p hp
          exact (zero_le_one.trans (one_le_secondOrderCorrection (by
            have hp' := Erdos851.mem_sievePrimes.mp hp
            omega)))) (secondOrderCorrection_product_le_tail (by omega)) _
      · apply pow_nonneg
        apply Finset.prod_nonneg
        intro p hp
        exact inv_nonneg.mpr (oneShift_localFactor_pos
          (Erdos851.mem_sievePrimes.mp hp).2.2).le

private theorem partialEulerProduct_eq_inv_preSieveSingularSeries (D : ℕ) :
    partial_euler_product D =
      (BoundedGaps.Maynard.preSieveSingularSeries D)⁻¹ := by
  unfold partial_euler_product
    BoundedGaps.Maynard.preSieveSingularSeries
  rw [Finset.prod_inv_distrib]
  have hsets : (Finset.Icc 1 D).filter Nat.Prime = Nat.primesLE D := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.primesLE,
      Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨_hp1, hpD⟩, hp⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨hpD, hp⟩
      exact ⟨⟨hp.one_le, by omega⟩, hp⟩
  rw [hsets]
  simp [one_div]

/-- The elementary harmonic Euler product gives the explicit lower Mertens
bound needed in a product ratio. -/
theorem log_le_partialEulerProduct (D : ℕ) :
    Real.log (D : ℝ) ≤ partial_euler_product D := by
  by_cases hD0 : D = 0
  · subst D
    simp
  let V := BoundedGaps.Maynard.preSieveSingularSeries D
  have hV : 0 < V := by
    exact BoundedGaps.Maynard.preSieveSingularSeries_pos D
  have hlog : Real.log (D : ℝ) ≤ Real.log (D + 1 : ℕ) := by
    apply Real.log_le_log
    · exact_mod_cast (Nat.pos_of_ne_zero hD0)
    · exact_mod_cast (Nat.le_succ D)
  have hmain := Erdos387.RoughHarmonic.log_mul_preSieveSingularSeries_le_one D
  have hmul : Real.log (D : ℝ) * V ≤ 1 := by
    exact (mul_le_mul_of_nonneg_right hlog hV.le).trans hmain
  rw [partialEulerProduct_eq_inv_preSieveSingularSeries]
  change Real.log (D : ℝ) ≤ V⁻¹
  rw [inv_eq_one_div, le_div_iff₀ hV]
  simpa [mul_comm] using hmul

/-- The explicit lower bound from `Util.MertensThird` yields the matching
upper bound for the inverse Euler product. -/
theorem partialEulerProduct_le_three_mul_log
    {D : ℕ} (hD : 3 ≤ D) :
    partial_euler_product D ≤ 3 * Real.log (D : ℝ) := by
  let V := BoundedGaps.Maynard.preSieveSingularSeries D
  have hV : 0 < V := by
    exact BoundedGaps.Maynard.preSieveSingularSeries_pos D
  have hlog : 0 < Real.log (D : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < D by omega))
  have hm := mertens_third_theorem D hD
  have hsets :
      (Finset.range (D + 1)).filter Nat.Prime = Nat.primesLE D := by
    ext p
    simp [Nat.primesLE, Nat.mem_primesBelow]
  have hlow : (3 * Real.log (D : ℝ))⁻¹ ≤ V := by
    rw [show V = ∏ p ∈ Nat.primesLE D,
        (1 - 1 / (p : ℝ)) by rfl]
    rw [← hsets]
    simpa [one_div] using hm
  rw [partialEulerProduct_eq_inv_preSieveSingularSeries]
  change V⁻¹ ≤ 3 * Real.log (D : ℝ)
  have hden : 0 < 3 * Real.log (D : ℝ) := by positivity
  exact inv_le_of_inv_le₀ hden hlow

/-- A completely explicit dimension-one product-ratio bound. -/
theorem oneShift_inverseLocalEulerProduct_le_three
    {z y : ℕ} (hz : 3 ≤ z) (hzy : z ≤ y) :
    inverseLocalEulerProduct oneShiftDensity z y ≤
      3 * (Real.log (y : ℝ) / Real.log (z : ℝ)) := by
  have hzlog : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hPEPz : 0 < partial_euler_product z :=
    lt_of_lt_of_le (by norm_num) partial_euler_trivial_lower_bound
  have hPEPy : 0 ≤ partial_euler_product y :=
    (zero_le_one.trans partial_euler_trivial_lower_bound)
  have hlogy : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
  rw [oneShift_inverseLocalEulerProduct_eq hzy]
  calc
    partial_euler_product y / partial_euler_product z ≤
        (3 * Real.log (y : ℝ)) / Real.log (z : ℝ) := by
      exact div_le_div₀ (mul_nonneg (by norm_num) hlogy)
        (partialEulerProduct_le_three_mul_log (hz.trans hzy))
        hzlog (log_le_partialEulerProduct z)
    _ = 3 * (Real.log (y : ℝ) / Real.log (z : ℝ)) := by ring

/-- The explicit endpoint-independent dimension constant for `k/p`. -/
noncomputable def sharpBinomialDimensionConstant (k : ℕ) : ℝ :=
  ((2 * k : ℕ) : ℝ) ^ (2 * k ^ 2) /
      (((2 * k : ℕ) : ℝ) - 1) ^ (2 * k ^ 2) * 3 ^ k

theorem one_le_sharpBinomialDimensionConstant
    {k : ℕ} (hk : 1 ≤ k) :
    1 ≤ sharpBinomialDimensionConstant k := by
  have hden : (0 : ℝ) < ((2 * k : ℕ) : ℝ) - 1 := by
    exact sub_pos.mpr (by exact_mod_cast (show 1 < 2 * k by omega))
  have hbase : (1 : ℝ) ≤ ((2 * k : ℕ) : ℝ) /
      (((2 * k : ℕ) : ℝ) - 1) := by
    rw [le_div_iff₀ hden]
    norm_num
  rw [sharpBinomialDimensionConstant, ← div_pow]
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hbase)
    (one_le_pow₀ (by norm_num))

/-- The binomial density has dimension `k` with the explicit constant above. -/
theorem binomial_inverseLocalEulerProduct_le_sharpConstant
    {k z y : ℕ} (hk : 2 ≤ k) (hz : 2 * k ≤ z) (hzy : z ≤ y) :
    inverseLocalEulerProduct (fun p ↦ binomialSieveNu k p) z y ≤
      sharpBinomialDimensionConstant k *
        (Real.log (y : ℝ) / Real.log (z : ℝ)) ^ k := by
  have hz3 : 3 ≤ z := by omega
  have hone := oneShift_inverseLocalEulerProduct_le_three hz3 hzy
  have hratio0 : 0 ≤ Real.log (y : ℝ) / Real.log (z : ℝ) := by
    exact div_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega)))
      (Real.log_pos (by exact_mod_cast (show 1 < z by omega))).le
  have hone0 : 0 ≤ inverseLocalEulerProduct oneShiftDensity z y := by
    unfold inverseLocalEulerProduct
    apply Finset.prod_nonneg
    intro p hp
    exact inv_nonneg.mpr (oneShift_localFactor_pos
      (Erdos851.mem_sievePrimes.mp hp).2.2).le
  have htailden : (0 : ℝ) < ((2 * k : ℕ) : ℝ) - 1 := by
    exact sub_pos.mpr (by exact_mod_cast (show 1 < 2 * k by omega))
  have hzden : (0 : ℝ) < (z : ℝ) - 1 := by
    exact sub_pos.mpr (by exact_mod_cast (show 1 < z by omega))
  have htail : (z : ℝ) / ((z : ℝ) - 1) ≤
      ((2 * k : ℕ) : ℝ) / (((2 * k : ℕ) : ℝ) - 1) := by
    have hzR : (2 : ℝ) * k ≤ z := by exact_mod_cast hz
    rw [div_le_div_iff₀ hzden htailden]
    norm_num [Nat.cast_mul] at ⊢
    nlinarith
  have hlocal := binomial_inverseLocalEulerProduct_le_tail (y := y)
    (by omega : 1 ≤ k) hz
  calc
    inverseLocalEulerProduct (fun p ↦ binomialSieveNu k p) z y ≤
        inverseLocalEulerProduct oneShiftDensity z y ^ k *
          ((z : ℝ) / ((z : ℝ) - 1)) ^ (2 * k ^ 2) := hlocal
    _ ≤ (3 * (Real.log (y : ℝ) / Real.log (z : ℝ))) ^ k *
          (((2 * k : ℕ) : ℝ) /
            (((2 * k : ℕ) : ℝ) - 1)) ^ (2 * k ^ 2) := by
      gcongr
    _ = sharpBinomialDimensionConstant k *
          (Real.log (y : ℝ) / Real.log (z : ℝ)) ^ k := by
      rw [sharpBinomialDimensionConstant, div_pow]
      ring

/-- The logarithm of the explicit dimension constant grows only linearly. -/
theorem log_sharpBinomialDimensionConstant_le
    {k : ℕ} (hk : 1 ≤ k) :
    Real.log (sharpBinomialDimensionConstant k) ≤ 4 * k := by
  let b : ℝ := ((2 * k : ℕ) : ℝ) / (((2 * k : ℕ) : ℝ) - 1)
  have hden : (0 : ℝ) < ((2 * k : ℕ) : ℝ) - 1 := by
    exact sub_pos.mpr (by exact_mod_cast (show 1 < 2 * k by omega))
  have hbpos : 0 < b := by exact div_pos (by positivity) hden
  have hbEq : b = 1 + 1 / (((2 * k : ℕ) : ℝ) - 1) := by
    dsimp [b]
    field_simp [hden.ne']
    ring
  have hlogb : Real.log b ≤ 1 / (((2 * k : ℕ) : ℝ) - 1) := by
    calc
      Real.log b ≤ b - 1 := Real.log_le_sub_one_of_pos hbpos
      _ = 1 / (((2 * k : ℕ) : ℝ) - 1) := by rw [hbEq]; ring
  have hcorr : ((2 * k ^ 2 : ℕ) : ℝ) * Real.log b ≤ 2 * k := by
    calc
      ((2 * k ^ 2 : ℕ) : ℝ) * Real.log b ≤
          ((2 * k ^ 2 : ℕ) : ℝ) /
            (((2 * k : ℕ) : ℝ) - 1) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hlogb)
          (by positivity)
      _ ≤ 2 * k := by
        rw [div_le_iff₀ hden]
        norm_num [Nat.cast_mul, Nat.cast_pow]
        have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 * k by positivity)
          (sub_nonneg.mpr hkR)]
  have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
    convert Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num) using 1 <;>
      norm_num
  have hthree : (k : ℝ) * Real.log 3 ≤ 2 * k := by
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left hlog3 (by positivity : (0 : ℝ) ≤ k))
  rw [sharpBinomialDimensionConstant, ← div_pow]
  change Real.log (b ^ (2 * k ^ 2) * 3 ^ k) ≤ 4 * k
  rw [Real.log_mul (pow_ne_zero _ hbpos.ne') (pow_ne_zero _ (by norm_num)),
    Real.log_pow, Real.log_pow]
  norm_num [Nat.cast_mul, Nat.cast_pow] at hcorr ⊢
  linarith

end Erdos387.BinomialEulerProductSharp
