/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.GeneralBetaInflation
import ErdosProblems.Erdos387.SieveInstantiation
import ErdosProblems.Erdos851.LocalEulerProducts

/-!
# Uniform dimension bound for the binomial sieve density

For primes larger than `2*k`, the density `k/p` has sieve dimension `k`.
The comparison with `k` copies of the one-shift Mertens product has a
second-order correction.  We dominate that correction by the already
formalized telescoping product from `Erdos851.LocalEulerProducts`, obtaining
a constant depending on `k` but independent of both interval endpoints.
-/

namespace Erdos387.BinomialEulerProduct

open scoped BigOperators
open Erdos851
open Erdos387

private theorem local_ratio_aux
    {k : ℕ} {x : ℝ} (hk : 1 ≤ k) (hx : 0 ≤ x)
    (hxhalf : (k : ℝ) * x < 1 / 2)
    (hxone : x < 1) :
    (1 - x) ^ k / (1 - (k : ℝ) * x) ≤
      (1 + x ^ 2) ^ (2 * k ^ 2) := by
  have hone : 0 < 1 - x := sub_pos.mpr hxone
  have hkden : 0 < 1 - (k : ℝ) * x := by linarith
  let a : ℝ := x / (1 - x)
  have ha : 0 ≤ a := div_nonneg hx hone.le
  have hbern : 1 + (k : ℝ) * a ≤ (1 + a) ^ k := by
    exact one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ a) k
  have hbase : 1 + a = (1 - x)⁻¹ := by
    dsimp [a]
    field_simp [hone.ne']
    ring
  have hpowpos : 0 < (1 - x) ^ k := pow_pos hone _
  have hupper : (1 - x) ^ k ≤ (1 + (k : ℝ) * a)⁻¹ := by
    have hright : 0 < 1 + (k : ℝ) * a := by positivity
    rw [hbase, inv_pow] at hbern
    have := (inv_le_inv₀ (inv_pos.mpr hpowpos) hright).2 hbern
    simpa using this
  have hdenLower : 1 / 2 < 1 - (k : ℝ) * x := by linarith
  have hratio : (1 + (k : ℝ) * a)⁻¹ /
        (1 - (k : ℝ) * x) ≤ 1 + 2 * (k : ℝ) ^ 2 * x ^ 2 := by
    have hinvForm : (1 + (k : ℝ) * a)⁻¹ =
        (1 - x) / (1 - x + (k : ℝ) * x) := by
      dsimp [a]
      have hsum : 0 < 1 - x + (k : ℝ) * x := by nlinarith
      field_simp [hone.ne', hsum.ne']
    rw [hinvForm]
    have hsum : 0 < 1 - x + (k : ℝ) * x := by
      nlinarith
    have hdenprod : 0 <
        (1 - x + (k : ℝ) * x) * (1 - (k : ℝ) * x) :=
      mul_pos hsum hkden
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hsumOne : 1 ≤ 1 - x + (k : ℝ) * x := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hkR) hx]
    have hprodHalf : 1 / 2 <
        (1 - x + (k : ℝ) * x) * (1 - (k : ℝ) * x) := by
      calc
        (1 / 2 : ℝ) < 1 * (1 - (k : ℝ) * x) := by simpa using hdenLower
        _ ≤ (1 - x + (k : ℝ) * x) * (1 - (k : ℝ) * x) := by
          exact mul_le_mul_of_nonneg_right hsumOne hkden.le
    rw [div_div, div_le_iff₀ hdenprod]
    ring_nf at hprodHalf ⊢
    nlinarith [sq_nonneg x, mul_nonneg (show (0 : ℝ) ≤ k by positivity)
      (sub_nonneg.mpr hkR), mul_nonneg (sq_nonneg ((k : ℝ) * x)) hdenprod.le]
  calc
    (1 - x) ^ k / (1 - (k : ℝ) * x) ≤
        (1 + (k : ℝ) * a)⁻¹ / (1 - (k : ℝ) * x) := by
      exact div_le_div_of_nonneg_right hupper hkden.le
    _ ≤ 1 + 2 * (k : ℝ) ^ 2 * x ^ 2 := hratio
    _ ≤ (1 + x ^ 2) ^ (2 * k ^ 2) := by
      have h := one_add_mul_le_pow (a := x ^ 2)
        (by nlinarith [sq_nonneg x] : (-2 : ℝ) ≤ x ^ 2) (2 * k ^ 2)
      norm_num [Nat.cast_mul, Nat.cast_pow] at h ⊢
      exact h

/-- A local `k/p` inverse factor is bounded by `k` one-shift inverse
factors and a power of the standard second-order correction. -/
theorem binomial_inverseLocalFactor_le
    {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hpk : 2 * k < p) :
    (1 - binomialSieveNu k p)⁻¹ ≤
      (1 - oneShiftDensity p)⁻¹ ^ k *
        secondOrderCorrection p ^ (2 * k ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : 2 < p := by omega
  have hx : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr hp0.le
  have hxone : (p : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hxhalf : (k : ℝ) * (p : ℝ)⁻¹ < 1 / 2 := by
    rw [← div_eq_mul_inv, div_lt_iff₀ hp0]
    have hpkR : (2 : ℝ) * k < p := by exact_mod_cast hpk
    linarith
  have hratio := local_ratio_aux hk hx hxhalf hxone
  have hcorr : 1 + ((p : ℝ)⁻¹) ^ 2 ≤ secondOrderCorrection p := by
    rw [secondOrderCorrection_eq hp2]
    have hpR2 : (2 : ℝ) < p := by exact_mod_cast hp2
    have hden : 0 < (p : ℝ) * ((p : ℝ) - 2) :=
      mul_pos hp0 (sub_pos.mpr hpR2)
    rw [le_div_iff₀ hden]
    field_simp [hp0.ne']
    ring_nf
    linarith
  have hcorrpow : (1 + ((p : ℝ)⁻¹) ^ 2) ^ (2 * k ^ 2) ≤
      secondOrderCorrection p ^ (2 * k ^ 2) := by
    exact pow_le_pow_left₀ (by positivity) hcorr _
  rw [binomialSieveNu_prime hp, oneShiftDensity]
  have hbin : 0 < 1 - (k : ℝ) / p := by
    rw [sub_pos, div_lt_one hp0]
    have : (k : ℝ) < p := by exact_mod_cast (by omega : k < p)
    exact this
  have hone : 0 < 1 - (p : ℝ)⁻¹ := sub_pos.mpr hxone
  have heq :
      (1 - (k : ℝ) / p)⁻¹ /
          ((1 - (p : ℝ)⁻¹)⁻¹ ^ k) =
        (1 - (p : ℝ)⁻¹) ^ k /
          (1 - (k : ℝ) * (p : ℝ)⁻¹) := by
    simp only [div_eq_mul_inv, inv_pow, inv_inv]
    ring
  have hdiv :
      (1 - (k : ℝ) / p)⁻¹ /
          ((1 - (p : ℝ)⁻¹)⁻¹ ^ k) ≤
        secondOrderCorrection p ^ (2 * k ^ 2) := by
    rw [heq]
    exact hratio.trans hcorrpow
  exact (div_le_iff₀ (pow_pos (inv_pos.mpr hone) k)).1 hdiv |>.trans_eq
    (by ring)

/-- Finite endpoint-independent comparison with the one-shift inverse
Euler product. -/
theorem binomial_inverseLocalEulerProduct_le
    {k z y : ℕ} (hk : 1 ≤ k) (hz : 2 * k ≤ z) :
    inverseLocalEulerProduct (fun p ↦ binomialSieveNu k p) z y ≤
      inverseLocalEulerProduct oneShiftDensity z y ^ k *
        2 ^ (2 * k ^ 2) := by
  change (∏ p ∈ Erdos851.sievePrimes z y,
      (1 - binomialSieveNu k p)⁻¹) ≤
    (∏ p ∈ Erdos851.sievePrimes z y,
      (1 - oneShiftDensity p)⁻¹) ^ k * 2 ^ (2 * k ^ 2)
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
          2 ^ (2 * k ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_left₀ (by
          apply Finset.prod_nonneg
          intro p hp
          exact (zero_le_one.trans (one_le_secondOrderCorrection (by
            have hp' := Erdos851.mem_sievePrimes.mp hp
            omega))))
          (secondOrderCorrection_product_le_two (by omega)) _
      · apply pow_nonneg
        apply Finset.prod_nonneg
        intro p hp
        exact inv_nonneg.mpr (oneShift_localFactor_pos
          (Erdos851.mem_sievePrimes.mp hp).2.2).le

/-- Weak Mertens supplies a dimension-`k` estimate for `k/p`, with a
constant depending only on `k`. -/
theorem exists_binomial_dimension_bound (k : ℕ) (hk : 1 ≤ k) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ z y : ℕ, 2 * k ≤ z → z ≤ y →
      inverseLocalEulerProduct (fun p ↦ binomialSieveNu k p) z y ≤
        A * (Real.log (y : ℝ) / Real.log (z : ℝ)) ^ k := by
  obtain ⟨C, hC, hdimension⟩ := exists_oneShift_dimension_bound
  let C' := max 1 C
  refine ⟨2 ^ (2 * k ^ 2) * C' ^ k, ?_, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      (one_le_pow₀ (by simp [C']))
  · intro z y hz hzy
    have hz2 : 2 ≤ z := by omega
    have hone := hdimension z y hz2 hzy
    have hone' : inverseLocalEulerProduct oneShiftDensity z y ≤
        C' * (Real.log (y : ℝ) / Real.log (z : ℝ)) := by
      have hlogz : 0 < Real.log (z : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < z by omega))
      have hlogy : 0 ≤ Real.log (y : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
      calc
        inverseLocalEulerProduct oneShiftDensity z y ≤
            C * (Real.log (y : ℝ) / Real.log (z : ℝ)) := hone
        _ ≤ C' * (Real.log (y : ℝ) / Real.log (z : ℝ)) := by
          gcongr
          exact le_max_right _ _
    have hinv0 : 0 ≤ inverseLocalEulerProduct oneShiftDensity z y := by
      simp only [inverseLocalEulerProduct]
      apply Finset.prod_nonneg
      intro p hp
      exact inv_nonneg.mpr (oneShift_localFactor_pos
        ((Erdos851.mem_sievePrimes).mp hp).2.2).le
    have htarget0 : 0 ≤ C' *
        (Real.log (y : ℝ) / Real.log (z : ℝ)) := by
      positivity
    have hpow := pow_le_pow_left₀ hinv0 hone' k
    have hlocal := binomial_inverseLocalEulerProduct_le (y := y) hk hz
    calc
      inverseLocalEulerProduct (fun p ↦ binomialSieveNu k p) z y ≤
          inverseLocalEulerProduct oneShiftDensity z y ^ k * 2 ^ (2 * k ^ 2) := hlocal
      _ ≤ (C' * (Real.log (y : ℝ) / Real.log (z : ℝ))) ^ k *
          2 ^ (2 * k ^ 2) := by gcongr
      _ = (2 ^ (2 * k ^ 2) * C' ^ k) *
          (Real.log (y : ℝ) / Real.log (z : ℝ)) ^ k := by ring

end Erdos387.BinomialEulerProduct
