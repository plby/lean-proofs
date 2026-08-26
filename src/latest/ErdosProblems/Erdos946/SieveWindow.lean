/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.ConditionedSieve
import ErdosProblems.Erdos946.DimensionSixteenBeta

/-! # The fixed numerical sieve window used for Erdős 946 -/

open scoped BigOperators

namespace Erdos946.SieveWindow

open Erdos946.AffineSieve Erdos851 Erdos851.FiniteCombinatorialSieve Erdos387
open Erdos851.BetaSieveFundamental

noncomputable section

def sieveError : ℝ := 10 * (2 * (3 : ℝ) ^ 17) * (9 / 10 : ℝ) ^ 300

theorem sieveError_nonneg : 0 ≤ sieveError := by
  unfold sieveError
  positivity

theorem sieveError_lt : sieveError < 1 / 1000 := by
  have hb : (9 / 10 : ℝ) ^ (50 : ℕ) < 1 / 190 := by norm_num
  unfold sieveError
  rw [show (300 : ℕ) = 50 * 6 by norm_num, pow_mul]
  have hp : ((9 / 10 : ℝ) ^ (50 : ℕ)) ^ (6 : ℕ) <
      (1 / 190 : ℝ) ^ (6 : ℕ) := by gcongr
  norm_num at hp ⊢

theorem log_two_mul_three_pow_seventeen_le :
    Real.log (2 * (3 : ℝ) ^ 17) ≤ 9 * (500 - 200 : ℕ) / 99 := by
  have he : (27 / 10 : ℝ) < Real.exp 1 :=
    (by norm_num : (27 / 10 : ℝ) < 2.7182818283).trans Real.exp_one_gt_d9
  have hlog2 : Real.log (2 : ℝ) < 1 := by
    rw [← Real.exp_lt_exp, Real.exp_log (by norm_num)]
    exact (by norm_num : (2 : ℝ) < 27 / 10).trans he
  have hsmall : (6 / 5 : ℝ) ≤ Real.exp (1 / 5) := by
    nlinarith [Real.add_one_le_exp (1 / 5 : ℝ)]
  have hexp : (3 : ℝ) < Real.exp (6 / 5) := by
    rw [show (6 / 5 : ℝ) = 1 + 1 / 5 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos (1 / 5 : ℝ)]
  have hlog3 : Real.log (3 : ℝ) < 6 / 5 := by
    rw [← Real.exp_lt_exp, Real.exp_log (by norm_num)]
    exact hexp
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (by positivity : (3 : ℝ) ^ 17 ≠ 0), Real.log_pow]
  norm_num at *
  linarith

theorem log_thousand_lt_seven : Real.log (1000 : ℝ) < 7 := by
  have he : (27 / 10 : ℝ) < Real.exp 1 :=
    (by norm_num : (27 / 10 : ℝ) < 2.7182818283).trans Real.exp_one_gt_d9
  have hpow : (1000 : ℝ) < (27 / 10 : ℝ) ^ (7 : ℕ) := by norm_num
  have hexp : (1000 : ℝ) < Real.exp 7 := by
    rw [show Real.exp 7 = (Real.exp 1) ^ (7 : ℕ) by
      rw [← Real.exp_nat_mul]; norm_num]
    have hp : (27 / 10 : ℝ) ^ (7 : ℕ) < (Real.exp 1) ^ (7 : ℕ) := by gcongr
    exact hpow.trans hp
  rw [← Real.exp_lt_exp, Real.exp_log (by norm_num)]
  exact hexp

def sieveV (z y : ℕ) : ℝ :=
  localEulerProduct (fun p ↦ binomialSieveNu 16 p) z y

theorem sieveV_pos {z y : ℕ} (hz : 16 ≤ z) : 0 < sieveV z y := by
  unfold sieveV localEulerProduct
  apply Finset.prod_pos
  intro p hp
  have h := mem_sievePrimes.mp hp
  dsimp only
  rw [binomialSieveNu_prime h.2.2]
  apply sub_pos.mpr
  apply (div_lt_one (by exact_mod_cast h.2.2.pos)).2
  exact_mod_cast hz.trans_lt h.1

theorem sieveV_le_one {z y : ℕ} (hz : 16 ≤ z) : sieveV z y ≤ 1 := by
  unfold sieveV localEulerProduct
  apply Finset.prod_le_one
  · intro p hp
    have h := mem_sievePrimes.mp hp
    dsimp only
    rw [binomialSieveNu_prime h.2.2]
    have hpR : (16 : ℝ) < p := by exact_mod_cast hz.trans_lt h.1
    have hp0 : (0 : ℝ) < p := by positivity
    exact sub_nonneg.mpr ((div_le_one hp0).2 hpR.le)
  · intro p hp
    dsimp only
    rw [binomialSieveNu_prime (mem_sievePrimes.mp hp).2.2]
    exact sub_le_self _ (by positivity)

theorem sieveV_inv_bound {z y : ℕ} (hz : 272 ≤ z) (hzy : z ≤ y) :
    (sieveV z y)⁻¹ ≤ (3 : ℝ) ^ 17 *
      (Real.log (y : ℝ) / Real.log (z : ℝ)) ^ 17 := by
  have heq : (sieveV z y)⁻¹ =
      inverseLocalEulerProduct (fun p ↦ binomialSieveNu 16 p) z y := by
    simp [sieveV, localEulerProduct, inverseLocalEulerProduct, Finset.prod_inv_distrib]
  rw [heq]
  exact DimensionSixteenSharp.binomial16_dimension_seventeen hz hzy

theorem finiteEulerProduct_ascending (z y : ℕ) :
    FiniteCombinatorialSieve.finiteEulerProduct (fun p ↦ binomialSieveNu 16 p)
      (ascendingSievePrimes z y) =
      sieveV z y := by
  unfold FiniteCombinatorialSieve.finiteEulerProduct ascendingSievePrimes sieveV localEulerProduct
  simpa using (List.prod_toFinset (fun p ↦ 1 - binomialSieveNu 16 p)
    (Finset.sort_nodup (Erdos851.sievePrimes z y) (fun a b : ℕ ↦ a ≤ b))).symm

theorem fixed_mainTerms_bounds {z y : ℕ} (hz : 272 ≤ z) (hzy : z ≤ y) :
    (1 - sieveError) * sieveV z y ≤
      lowerMainTerm (rosserStoppingPredicate 200 (y ^ 500))
        (fun p ↦ binomialSieveNu 16 p) (ascendingSievePrimes z y) ∧
    upperMainTerm (rosserStoppingPredicate 200 (y ^ 500))
        (fun p ↦ binomialSieveNu 16 p) (ascendingSievePrimes z y) ≤
      (1 + sieveError) * sieveV z y := by
  have h := DimensionSixteenBeta.finiteMainTerms_bounds_twoHundred_sixteen
    (C := (3 : ℝ) ^ 17) (z₀ := 272) (by norm_num)
    (fun z y hz hzy ↦ DimensionSixteenSharp.binomial16_dimension_seventeen hz hzy)
    (z := z) (y := y) (S := 500) hz (by omega) hzy (by norm_num)
    log_two_mul_three_pow_seventeen_le
  have hreverse : (descendingSievePrimes z y).reverse = ascendingSievePrimes z y := by
    simp [descendingSievePrimes, ascendingSievePrimes]
  dsimp only at h
  rw [hreverse, finiteEulerProduct_ascending] at h
  simpa only [sieveError, show (500 - 200 : ℕ) = 300 by norm_num] using h

theorem affine_cardinality_bounds {a b : Fin 16 → ℕ} {X z y : ℕ}
    (hz : 272 ≤ z) (hzy : z ≤ y)
    (hlocal : ∀ p : ℕ, p.Prime → z < p → p ≤ y → localNu a b p = 16)
    (hcop : ∀ p : ℕ, p.Prime →
      p ∣ Erdos387.sievePrimeProduct z (y + 1) → ∀ i, (a i).Coprime p) :
    (X : ℝ) * ((1 - sieveError) * sieveV z y) - ((y ^ 500 : ℕ) : ℝ) ^ 2 ≤
      ((siftedCandidates a b X z (y + 1)).card : ℝ) ∧
    ((siftedCandidates a b X z (y + 1)).card : ℝ) ≤
      (X : ℝ) * ((1 + sieveError) * sieveV z y) + ((y ^ 500 : ℕ) : ℝ) ^ 2 := by
  let P := ascendingSievePrimes z y
  let stop := rosserStoppingPredicate 200 (y ^ 500)
  have hnu : ∀ p ∈ P, affineNu a b p = binomialSieveNu 16 p := by
    intro p hp
    have hp' := mem_sievePrimes.mp (mem_ascendingSievePrimes.mp hp)
    rw [affineNu_prime hp'.2.2, hlocal p hp'.2.2 hp'.1 hp'.2.1,
      binomialSieveNu_prime hp'.2.2]
  have hb := AffineSieve.boundingSieve_cardinality_between_mainTerms
    (a := a) (b := b) (X := X) (z := z) (y := y) (beta := 200) (S := 500)
    (by simpa using (show 16 ≤ z by omega)) (by omega) hzy
    (by norm_num) (by norm_num) hcop
  dsimp only at hb
  rw [lowerMainTerm_congr_on stop (fun p ↦ affineNu a b p)
      (fun p ↦ binomialSieveNu 16 p) P hnu,
    upperMainTerm_congr_on stop (fun p ↦ affineNu a b p)
      (fun p ↦ binomialSieveNu 16 p) P hnu] at hb
  have hm := fixed_mainTerms_bounds hz hzy
  constructor
  · exact (sub_le_sub_right (mul_le_mul_of_nonneg_left hm.1 (Nat.cast_nonneg X)) _).trans hb.1
  · exact hb.2.trans (add_le_add
      (mul_le_mul_of_nonneg_left hm.2 (Nat.cast_nonneg X)) le_rfl)

theorem affine_conditioned_cardinality_bound {a b : Fin 16 → ℕ} {X z y p : ℕ}
    (hz : 272 ≤ z) (hzy : z ≤ y) (hp : p.Prime) (hyp : y < p)
    (hlocalp : localNu a b p = 16)
    (hlocal : ∀ q : ℕ, q.Prime → z < q → q ≤ y → localNu a b q = 16)
    (hcop : ∀ q : ℕ, q.Prime →
      q ∣ Erdos387.sievePrimeProduct z (y + 1) → ∀ i, (a i).Coprime q) :
    ((conditionedCandidates a b X z (y + 1) p).card : ℝ) ≤
      16 * (((X : ℝ) / p) * ((1 + sieveError) * sieveV z y) +
        ((y ^ 500 : ℕ) : ℝ) ^ 2) := by
  let P := ascendingSievePrimes z y
  let stop := rosserStoppingPredicate 200 (y ^ 500)
  have hnu : ∀ q ∈ P, affineNu a b q = binomialSieveNu 16 q := by
    intro q hq
    have hq' := mem_sievePrimes.mp (mem_ascendingSievePrimes.mp hq)
    rw [affineNu_prime hq'.2.2, hlocal q hq'.2.2 hq'.1 hq'.2.1,
      binomialSieveNu_prime hq'.2.2]
  have hb := conditionedCandidates_card_le_upperMainTerm
    (a := a) (b := b) (X := X) (z := z) (y := y) (p := p) (beta := 200) (S := 500)
    (by simpa using (show 16 ≤ z by omega)) (by omega) hzy
    (by norm_num) hp hyp hlocalp hcop
  dsimp only at hb
  rw [upperMainTerm_congr_on stop (fun q ↦ affineNu a b q)
    (fun q ↦ binomialSieveNu 16 q) P hnu] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left (fixed_mainTerms_bounds hz hzy).2
      (div_nonneg (Nat.cast_nonneg X) (Nat.cast_nonneg p))) le_rfl)
    (by norm_num))

end

end Erdos946.SieveWindow
