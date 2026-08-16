/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib
import UnitFractions.ForMathlib.BasicEstimates

/-!
# Local Euler products for Erdős problem 851

This file verifies the local-density and sieve-dimension estimates used for
the one- and two-shift rough-residual sieves.  The one-shift local density is
`1 / p`.  For two shifts separated by `h`, it is `1 / p` when `p ∣ h` and
`2 / p` otherwise.

The inverse two-shift Euler product is bounded by the square of the one-shift
product times a uniformly bounded second-order correction.  The latter is a
`p⁻²` Euler product; comparison with all integers makes it telescope to a
quantity below `2`.  Combining this with the weak upper and lower forms of
Mertens' third theorem in `UnitFractions.ForMathlib.BasicEstimates` gives the
dimension-one and dimension-two product-ratio bounds required by the beta
sieve.
-/

namespace Erdos851

open scoped BigOperators

/-- Primes in the half-open sieve interval `(z, y]`. -/
def sievePrimes (z y : ℕ) : Finset ℕ :=
  (Finset.Ioc z y).filter Nat.Prime

/-- The one-shift local sieve density. -/
noncomputable def oneShiftDensity (p : ℕ) : ℝ :=
  (p : ℝ)⁻¹

/-- The two-shift local sieve density for shifts separated by `h`. -/
noncomputable def pairShiftDensity (h p : ℕ) : ℝ :=
  if p ∣ h then (p : ℝ)⁻¹ else 2 * (p : ℝ)⁻¹

/-- A finite local Euler product over primes in `(z,y]`. -/
def localEulerProduct (g : ℕ → ℝ) (z y : ℕ) : ℝ :=
  ∏ p ∈ sievePrimes z y, (1 - g p)

/-- The corresponding inverse Euler product. -/
noncomputable def inverseLocalEulerProduct (g : ℕ → ℝ) (z y : ℕ) : ℝ :=
  ∏ p ∈ sievePrimes z y, (1 - g p)⁻¹

/-- The local density mass in a prime interval is at most the logarithm of
the inverse Euler product over that interval.  This is the finite analytic
input behind the elementary-symmetric depth estimate: termwise it is the
inequality `u ≤ -log (1-u)` for `0 ≤ u < 1`. -/
theorem sum_density_le_log_inverseLocalEulerProduct
    (g : ℕ → ℝ) (z y : ℕ)
    (hg1 : ∀ p ∈ sievePrimes z y, g p < 1) :
    (∑ p ∈ sievePrimes z y, g p) ≤
      Real.log (inverseLocalEulerProduct g z y) := by
  rw [inverseLocalEulerProduct]
  calc
    (∑ p ∈ sievePrimes z y, g p) ≤
        ∑ p ∈ sievePrimes z y, Real.log ((1 - g p)⁻¹) := by
      apply Finset.sum_le_sum
      intro p hp
      have hfactor : 0 < (1 - g p)⁻¹ :=
        inv_pos.mpr (sub_pos.mpr (hg1 p hp))
      have hlog := Real.one_sub_inv_le_log_of_pos hfactor
      simpa only [inv_inv, sub_sub_cancel] using hlog
    _ = Real.log (∏ p ∈ sievePrimes z y, (1 - g p)⁻¹) := by
      symm
      apply Real.log_prod
      intro p hp
      exact (inv_pos.mpr (sub_pos.mpr (hg1 p hp))).ne'

/-- The usual truncated singular factor for a difference `h`. -/
noncomputable def singularFactor (h z y : ℕ) : ℝ :=
  ∏ p ∈ sievePrimes z y,
    if p ∣ h then (p : ℝ) / ((p : ℝ) - 1) else 1

/-- The exact local correction after extracting two one-shift factors. -/
noncomputable def pairDirectCorrection (h p : ℕ) : ℝ :=
  if p ∣ h then (p : ℝ) / ((p : ℝ) - 1)
  else 1 - (((p : ℝ) - 1) ^ 2)⁻¹

theorem mem_sievePrimes {z y p : ℕ} :
    p ∈ sievePrimes z y ↔ z < p ∧ p ≤ y ∧ p.Prime := by
  simp [sievePrimes, and_assoc]

theorem oneShiftDensity_pos {p : ℕ} (hp : p.Prime) :
    0 < oneShiftDensity p := by
  simp only [oneShiftDensity]
  exact inv_pos.mpr (by exact_mod_cast hp.pos)

theorem oneShiftDensity_lt_one {p : ℕ} (hp : p.Prime) :
    oneShiftDensity p < 1 := by
  simp only [oneShiftDensity]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

theorem pairShiftDensity_pos {h p : ℕ} (hp : p.Prime) :
    0 < pairShiftDensity h p := by
  simp only [pairShiftDensity]
  split_ifs
  · exact inv_pos.mpr (by exact_mod_cast hp.pos)
  · exact mul_pos (by norm_num) (inv_pos.mpr (by exact_mod_cast hp.pos))

theorem pairShiftDensity_lt_one {h p : ℕ} (hp : p.Prime)
    (hp2 : 2 < p) : pairShiftDensity h p < 1 := by
  simp only [pairShiftDensity]
  split_ifs
  · exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  · have hpR : (2 : ℝ) < p := by exact_mod_cast hp2
    rw [← div_eq_mul_inv]
    exact (div_lt_one (by positivity)).2 hpR

theorem oneShift_localFactor_pos {p : ℕ} (hp : p.Prime) :
    0 < 1 - oneShiftDensity p :=
  sub_pos.mpr (oneShiftDensity_lt_one hp)

theorem pairShift_localFactor_pos {h p : ℕ} (hp : p.Prime)
    (hp2 : 2 < p) : 0 < 1 - pairShiftDensity h p :=
  sub_pos.mpr (pairShiftDensity_lt_one hp hp2)

theorem oneShift_localEulerProduct_pos {z y : ℕ} :
    0 < localEulerProduct oneShiftDensity z y := by
  apply Finset.prod_pos
  intro p hp
  exact oneShift_localFactor_pos (mem_sievePrimes.mp hp).2.2

theorem pairShift_localEulerProduct_pos (h : ℕ) {z y : ℕ} (hz : 2 ≤ z) :
    0 < localEulerProduct (pairShiftDensity h) z y := by
  apply Finset.prod_pos
  intro p hp
  have hp' := mem_sievePrimes.mp hp
  exact pairShift_localFactor_pos hp'.2.2 (by omega)

/-- Exact extraction of the square of the one-shift factor from one
two-shift local factor. -/
theorem pairShift_localFactor_eq {h p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    1 - pairShiftDensity h p =
      (1 - oneShiftDensity p) ^ 2 * pairDirectCorrection h p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpR1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpm1 : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr hpR1).ne'
  simp only [pairShiftDensity, oneShiftDensity, pairDirectCorrection]
  split_ifs <;> field_simp [hpR.ne', hpm1] <;> ring

/-- Exact finite-product form of the pair singular-series decomposition. -/
theorem pairShift_localEulerProduct_eq (h : ℕ) {z y : ℕ} (hz : 2 ≤ z) :
    localEulerProduct (pairShiftDensity h) z y =
      localEulerProduct oneShiftDensity z y ^ 2 *
        ∏ p ∈ sievePrimes z y, pairDirectCorrection h p := by
  simp only [localEulerProduct]
  calc
    (∏ p ∈ sievePrimes z y, (1 - pairShiftDensity h p)) =
        ∏ p ∈ sievePrimes z y,
          ((1 - oneShiftDensity p) ^ 2 * pairDirectCorrection h p) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp' := mem_sievePrimes.mp hp
      exact pairShift_localFactor_eq hp'.2.2 (by omega)
    _ = (∏ p ∈ sievePrimes z y, (1 - oneShiftDensity p) ^ 2) *
          ∏ p ∈ sievePrimes z y, pairDirectCorrection h p := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ p ∈ sievePrimes z y, (1 - oneShiftDensity p)) ^ 2 *
          ∏ p ∈ sievePrimes z y, pairDirectCorrection h p := by
      rw [Finset.prod_pow]

theorem pairDirectCorrection_nonneg {h p : ℕ} (hp2 : 2 < p) :
    0 ≤ pairDirectCorrection h p := by
  have hpR : (2 : ℝ) < p := by exact_mod_cast hp2
  simp only [pairDirectCorrection]
  split_ifs
  · exact div_nonneg (by positivity) (by linarith)
  · have hpm1 : (1 : ℝ) < (p : ℝ) - 1 := by linarith
    have hinv : (((p : ℝ) - 1) ^ 2)⁻¹ < 1 :=
      inv_lt_one_of_one_lt₀ (one_lt_pow₀ hpm1 (by norm_num))
    linarith

theorem pairDirectCorrection_le_singularLocal {h p : ℕ} (hp2 : 2 < p) :
    pairDirectCorrection h p ≤
      (if p ∣ h then (p : ℝ) / ((p : ℝ) - 1) else 1) := by
  simp only [pairDirectCorrection]
  split_ifs
  · exact le_rfl
  · exact sub_le_self _ (inv_nonneg.mpr (sq_nonneg _))

/-- The two-shift local Euler product is at most the square of the one-shift
product times the truncated singular factor. -/
theorem pairShift_localEulerProduct_le (h : ℕ) {z y : ℕ} (hz : 2 ≤ z) :
    localEulerProduct (pairShiftDensity h) z y ≤
      localEulerProduct oneShiftDensity z y ^ 2 * singularFactor h z y := by
  rw [pairShift_localEulerProduct_eq h hz, singularFactor]
  apply mul_le_mul_of_nonneg_left
  · apply Finset.prod_le_prod
    · intro p hp
      exact pairDirectCorrection_nonneg (by
        have hp' := mem_sievePrimes.mp hp
        omega)
    · intro p hp
      exact pairDirectCorrection_le_singularLocal (by
        have hp' := mem_sievePrimes.mp hp
        omega)
  · exact sq_nonneg _

/-! ## Uniform second-order correction -/

/-- The second-order loss incurred when a two-shift inverse factor is
majorized by the square of the one-shift inverse factor. -/
noncomputable def secondOrderCorrection (p : ℕ) : ℝ :=
  1 + ((p : ℝ) * ((p : ℝ) - 2))⁻¹

theorem one_le_secondOrderCorrection {p : ℕ} (hp2 : 2 < p) :
    1 ≤ secondOrderCorrection p := by
  have hpR2 : (2 : ℝ) < p := by exact_mod_cast hp2
  simp only [secondOrderCorrection]
  exact le_add_of_nonneg_right
    (inv_nonneg.mpr (mul_nonneg (by positivity) (by linarith)))

/-- For every prime above `2`, a pair inverse factor is bounded by two
one-shift inverse factors and one second-order correction. -/
theorem pairShift_inverseLocalFactor_le {h p : ℕ}
    (hp : p.Prime) (hp2 : 2 < p) :
    (1 - pairShiftDensity h p)⁻¹ ≤
      (1 - oneShiftDensity p)⁻¹ ^ 2 * secondOrderCorrection p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpR2 : (2 : ℝ) < p := by exact_mod_cast hp2
  have honePos : 0 < 1 - (p : ℝ)⁻¹ := by
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt))
  simp only [pairShiftDensity, oneShiftDensity, secondOrderCorrection]
  split_ifs with hdiv
  · have honeInv : 1 ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
      exact (one_le_inv₀ honePos).2
        (sub_le_self _ (inv_nonneg.mpr hpR.le))
    have hcorr : 1 ≤ 1 + ((p : ℝ) * ((p : ℝ) - 2))⁻¹ := by
      exact le_add_of_nonneg_right (inv_nonneg.mpr (mul_nonneg hpR.le (by linarith)))
    calc
      (1 - (p : ℝ)⁻¹)⁻¹ ≤ (1 - (p : ℝ)⁻¹)⁻¹ ^ 2 := by
        nlinarith [inv_pos.mpr honePos]
      _ ≤ (1 - (p : ℝ)⁻¹)⁻¹ ^ 2 *
          (1 + ((p : ℝ) * ((p : ℝ) - 2))⁻¹) := by
        exact le_mul_of_one_le_right (sq_nonneg _) hcorr
  · have hpairPos : 0 < 1 - 2 * (p : ℝ)⁻¹ := by
      have : 2 * (p : ℝ)⁻¹ < 1 := by
        rw [← div_eq_mul_inv]
        exact (div_lt_one hpR).2 hpR2
      linarith
    have hpm1 : 0 < (p : ℝ) - 1 := by linarith
    have hpm2 : 0 < (p : ℝ) - 2 := by linarith
    have honeEq :
        (1 - (p : ℝ)⁻¹)⁻¹ = (p : ℝ) / ((p : ℝ) - 1) := by
      field_simp [honePos.ne', hpR.ne', hpm1.ne']
    have hpairEq :
        (1 - 2 * (p : ℝ)⁻¹)⁻¹ = (p : ℝ) / ((p : ℝ) - 2) := by
      field_simp [hpairPos.ne', hpR.ne', hpm2.ne']
    have hcorrEq :
        1 + ((p : ℝ) * ((p : ℝ) - 2))⁻¹ =
          ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2)) := by
      field_simp [hpR.ne', hpm2.ne']
      ring
    apply le_of_eq
    rw [hpairEq, honeEq, hcorrEq]
    field_simp [hpR.ne', hpm1.ne', hpm2.ne']

theorem pairShift_inverseLocalEulerProduct_le (h : ℕ) {z y : ℕ}
    (hz : 2 ≤ z) :
    inverseLocalEulerProduct (pairShiftDensity h) z y ≤
      inverseLocalEulerProduct oneShiftDensity z y ^ 2 *
        ∏ p ∈ sievePrimes z y, secondOrderCorrection p := by
  simp only [inverseLocalEulerProduct]
  calc
    (∏ p ∈ sievePrimes z y, (1 - pairShiftDensity h p)⁻¹) ≤
        ∏ p ∈ sievePrimes z y,
          ((1 - oneShiftDensity p)⁻¹ ^ 2 * secondOrderCorrection p) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact (inv_nonneg.mpr (pairShift_localFactor_pos
          (mem_sievePrimes.mp hp).2.2 (by
            have hp' := mem_sievePrimes.mp hp
            omega)).le)
      · intro p hp
        exact pairShift_inverseLocalFactor_le
          (mem_sievePrimes.mp hp).2.2 (by
            have hp' := mem_sievePrimes.mp hp
            omega)
    _ = (∏ p ∈ sievePrimes z y, (1 - oneShiftDensity p)⁻¹) ^ 2 *
          ∏ p ∈ sievePrimes z y, secondOrderCorrection p := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow]

/-- The correction factor is the telescoping quotient
`(p-1)^2 / (p(p-2))`. -/
theorem secondOrderCorrection_eq {p : ℕ} (hp2 : 2 < p) :
    secondOrderCorrection p =
      ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2)) := by
  have hpR : (0 : ℝ) < p := by positivity
  have hpR2 : (2 : ℝ) < p := by exact_mod_cast hp2
  simp only [secondOrderCorrection]
  field_simp [hpR.ne', (sub_pos.mpr hpR2).ne']
  ring

/-- The all-integer correction product from `3` through `k+3` telescopes. -/
theorem integerSecondOrderCorrection_formula (k : ℕ) :
    (∏ n ∈ Finset.Icc 3 (k + 3), secondOrderCorrection n) =
      2 * ((k + 2 : ℕ) : ℝ) / (k + 3 : ℕ) := by
  induction k with
  | zero =>
      norm_num [secondOrderCorrection]
  | succ k ih =>
      rw [show k + 1 + 3 = (k + 3) + 1 by omega,
        Finset.prod_Icc_succ_top (show 3 ≤ k + 3 + 1 by omega), ih,
        secondOrderCorrection_eq (show 2 < k + 3 + 1 by omega)]
      have hk2 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
      have hk3 : (0 : ℝ) < ((k + 3 : ℕ) : ℝ) := by positivity
      have hk4 : (0 : ℝ) < ((k + 4 : ℕ) : ℝ) := by positivity
      norm_num [Nat.cast_add] at hk2 hk3 hk4 ⊢
      rw [show (k : ℝ) + 3 + 1 - 2 = (k : ℝ) + 2 by ring,
        show (k : ℝ) + 3 + 1 = (k : ℝ) + 4 by ring,
        show (k : ℝ) + 1 + 2 = (k : ℝ) + 3 by ring]
      change
        (2 * ((k : ℝ) + 2) / ((k : ℝ) + 3)) *
            (((k : ℝ) + 3) ^ 2 /
              (((k : ℝ) + 4) * ((k : ℝ) + 2))) =
          2 * ((k : ℝ) + 3) / ((k : ℝ) + 4)
      field_simp [hk2.ne', hk3.ne', hk4.ne']

theorem integerSecondOrderCorrection_le_two {y : ℕ} (hy : 3 ≤ y) :
    (∏ n ∈ Finset.Icc 3 y, secondOrderCorrection n) ≤ 2 := by
  rw [← Nat.sub_add_cancel hy, integerSecondOrderCorrection_formula]
  have hyR : (0 : ℝ) < (((y - 3) + 3 : ℕ) : ℝ) := by positivity
  rw [div_le_iff₀ hyR]
  norm_num [Nat.cast_add]

/-- The prime `p⁻²` correction is uniformly bounded independently of both
endpoints of the sieve interval. -/
theorem secondOrderCorrection_product_le_two {z y : ℕ} (hz : 2 ≤ z) :
    (∏ p ∈ sievePrimes z y, secondOrderCorrection p) ≤ 2 := by
  by_cases hy : 3 ≤ y
  · calc
      (∏ p ∈ sievePrimes z y, secondOrderCorrection p) ≤
          ∏ n ∈ Finset.Icc 3 y, secondOrderCorrection n := by
        apply Finset.prod_le_prod_of_subset_of_one_le
        · intro p hp
          have hp' := mem_sievePrimes.mp hp
          exact Finset.mem_Icc.mpr ⟨by omega, hp'.2.1⟩
        · intro p hp
          exact le_trans (by norm_num : (0 : ℝ) ≤ 1)
            (one_le_secondOrderCorrection (by
              have hp' := mem_sievePrimes.mp hp
              omega))
        · intro p hp hpnot
          exact one_le_secondOrderCorrection (by
            have hp' := Finset.mem_Icc.mp hp
            omega)
      _ ≤ 2 := integerSecondOrderCorrection_le_two hy
  · have hempty : sievePrimes z y = ∅ := by
      ext p
      simp only [mem_sievePrimes, Finset.notMem_empty, iff_false]
      omega
    simp [hempty]

/-! ## Mertens product ratios and sieve dimension -/

private theorem primeSet_decomposition {z y : ℕ} (hzy : z ≤ y) :
    ((Finset.Icc 1 z).filter Nat.Prime) ∪ sievePrimes z y =
      (Finset.Icc 1 y).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc,
    mem_sievePrimes]
  constructor
  · rintro (⟨⟨hp1, hpz⟩, hpPrime⟩ | ⟨hzp, hpy, hpPrime⟩)
    · exact ⟨⟨hp1, hpz.trans hzy⟩, hpPrime⟩
    · exact ⟨⟨by omega, hpy⟩, hpPrime⟩
  · rintro ⟨⟨hp1, hpy⟩, hpPrime⟩
    by_cases hpz : p ≤ z
    · exact Or.inl ⟨⟨hp1, hpz⟩, hpPrime⟩
    · exact Or.inr ⟨by omega, hpy, hpPrime⟩

private theorem primeSet_disjoint (z y : ℕ) :
    Disjoint ((Finset.Icc 1 z).filter Nat.Prime) (sievePrimes z y) := by
  rw [Finset.disjoint_left]
  intro p hpz hprange
  have hpz' := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpz).1).2
  have hprange' := (mem_sievePrimes.mp hprange).1
  omega

/-- The one-shift inverse product over `(z,y]` is exactly the quotient of
the two partial Mertens products. -/
theorem oneShift_inverseLocalEulerProduct_eq {z y : ℕ} (hzy : z ≤ y) :
    inverseLocalEulerProduct oneShiftDensity z y =
      partial_euler_product y / partial_euler_product z := by
  have hprod :
      partial_euler_product z *
          inverseLocalEulerProduct oneShiftDensity z y =
        partial_euler_product y := by
    simp only [partial_euler_product, inverseLocalEulerProduct, oneShiftDensity]
    rw [← Finset.prod_union (primeSet_disjoint z y),
      primeSet_decomposition hzy]
  apply (eq_div_iff (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (partial_euler_trivial_lower_bound (n := z))))).2
  simpa [mul_comm] using hprod

/-- Weak Mertens gives the dimension-one product-ratio condition, uniformly for
all natural endpoints `2 ≤ z ≤ y`. -/
theorem exists_oneShift_dimension_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z y : ℕ, 2 ≤ z → z ≤ y →
      inverseLocalEulerProduct oneShiftDensity z y ≤
        C * (Real.log (y : ℝ) / Real.log (z : ℝ)) := by
  obtain ⟨Cu, hCu, hupper⟩ := weak_mertens_third_upper_all
  obtain ⟨Cl, hCl, hlower⟩ := weak_mertens_third_lower_all
  refine ⟨Cu / Cl, div_pos hCu hCl, ?_⟩
  intro z y hz hzy
  have hzR : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hyR : (2 : ℝ) ≤ y := by exact_mod_cast hz.trans hzy
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hz))
  have hlogy : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
  have hPEPz : 0 < partial_euler_product z :=
    lt_of_lt_of_le (by norm_num) partial_euler_trivial_lower_bound
  have hupper' : partial_euler_product y ≤ Cu * Real.log (y : ℝ) := by
    simpa [Real.norm_of_nonneg hlogy,
      Real.norm_of_nonneg (zero_le_one.trans
        (partial_euler_trivial_lower_bound (n := y)))]
      using hupper (y : ℝ) hyR
  have hlower' : Cl * Real.log (z : ℝ) ≤ partial_euler_product z := by
    simpa [Real.norm_of_nonneg hlogz.le,
      Real.norm_of_nonneg (zero_le_one.trans
        (partial_euler_trivial_lower_bound (n := z)))]
      using hlower (z : ℝ) (by exact_mod_cast (show 1 ≤ z by omega))
  rw [oneShift_inverseLocalEulerProduct_eq hzy]
  calc
    partial_euler_product y / partial_euler_product z ≤
        (Cu * Real.log (y : ℝ)) / (Cl * Real.log (z : ℝ)) := by
      exact div_le_div₀ (by positivity) hupper'
        (mul_pos hCl hlogz) hlower'
    _ = (Cu / Cl) * (Real.log (y : ℝ) / Real.log (z : ℝ)) := by
      field_simp [hCl.ne', hlogz.ne']

/-- Weak Mertens plus the uniformly convergent correction gives the
dimension-two product-ratio condition for every pair of shifts. -/
theorem exists_pairShift_dimension_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ h z y : ℕ, 2 ≤ z → z ≤ y →
      inverseLocalEulerProduct (pairShiftDensity h) z y ≤
        C * (Real.log (y : ℝ) / Real.log (z : ℝ)) ^ 2 := by
  obtain ⟨C, hC, hdimensionOne⟩ := exists_oneShift_dimension_bound
  refine ⟨2 * C ^ 2, by positivity, ?_⟩
  intro h z y hz hzy
  have hone := hdimensionOne z y hz hzy
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hlogy : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
  have hratio : 0 ≤ Real.log (y : ℝ) / Real.log (z : ℝ) :=
    div_nonneg hlogy hlogz.le
  have hinv : 0 ≤ inverseLocalEulerProduct oneShiftDensity z y := by
    simp only [inverseLocalEulerProduct]
    apply Finset.prod_nonneg
    intro p hp
    exact inv_nonneg.mpr
      (oneShift_localFactor_pos (mem_sievePrimes.mp hp).2.2).le
  have htarget :
      0 ≤ C * (Real.log (y : ℝ) / Real.log (z : ℝ)) :=
    mul_nonneg hC.le hratio
  have hsquare : inverseLocalEulerProduct oneShiftDensity z y ^ 2 ≤
      (C * (Real.log (y : ℝ) / Real.log (z : ℝ))) ^ 2 :=
    (sq_le_sq₀ hinv htarget).2 hone
  calc
    inverseLocalEulerProduct (pairShiftDensity h) z y ≤
        inverseLocalEulerProduct oneShiftDensity z y ^ 2 *
          ∏ p ∈ sievePrimes z y, secondOrderCorrection p :=
      pairShift_inverseLocalEulerProduct_le h hz
    _ ≤ inverseLocalEulerProduct oneShiftDensity z y ^ 2 * 2 := by
      exact mul_le_mul_of_nonneg_left
        (secondOrderCorrection_product_le_two hz) (sq_nonneg _)
    _ ≤ (C * (Real.log (y : ℝ) / Real.log (z : ℝ))) ^ 2 * 2 := by
      exact mul_le_mul_of_nonneg_right hsquare (by norm_num)
    _ = (2 * C ^ 2) *
        (Real.log (y : ℝ) / Real.log (z : ℝ)) ^ 2 := by ring

end Erdos851
