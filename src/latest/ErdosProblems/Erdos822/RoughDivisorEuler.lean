/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos387.BrunSieve
import ErdosProblems.Erdos822.LargePrimeFactorMass
import ErdosProblems.Erdos822.CommonDivisorSplit
import ErdosProblems.Erdos822.SlowCutoffAsymptotic
import ErdosProblems.Erdos822.HarmonicElementary

/-!
# Euler products for squarefree rough-divisor sums

The quadratic residue-class argument contributes `4 ^ ω(h)` for a
squarefree common divisor `h`.  Summing this weight divided by `h` over all
divisors is an exact finite Euler product.  The product is then bounded by
the exponential of the reciprocal mass of the ambient prime factors.
-/

namespace Erdos822

open scoped BigOperators
open scoped ArithmeticFunction.Omega

/-- Exact squarefree divisor expansion of the quadratic root weight. -/
theorem sum_divisors_four_pow_primeFactorsCard_div_eq_prod
    {R : ℕ} (hR : Squarefree R) :
    (∑ h ∈ R.divisors,
        (4 : ℝ) ^ h.primeFactors.card / h) =
      ∏ p ∈ R.primeFactors, (1 + (4 : ℝ) / p) := by
  rw [Erdos387.divisors_eq_image_prod_primeFactorSubsets hR,
    Finset.sum_image (Erdos387.prod_primeFactorSubsets_injOn R),
    Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro T hT
  obtain ⟨_, hcard⟩ := Erdos387.prod_primeFactorSubset_squarefree_card hT
  have hpfcard : (∏ p ∈ T, p).primeFactors.card = T.card := by
    simpa [Erdos387.cardDistinctFactors_eq_primeFactors_card] using hcard
  rw [hpfcard]
  push_cast
  rw [Finset.prod_div_distrib]
  simp

/-- The unnormalized quadratic root weight sums to `5 ^ ω(R)` on a
squarefree ambient modulus. -/
theorem sum_divisors_four_pow_primeFactorsCard_eq_five_pow
    {R : ℕ} (hR : Squarefree R) :
    (∑ h ∈ R.divisors, (4 : ℕ) ^ h.primeFactors.card) =
      5 ^ R.primeFactors.card := by
  rw [Erdos387.divisors_eq_image_prod_primeFactorSubsets hR,
    Finset.sum_image (Erdos387.prod_primeFactorSubsets_injOn R)]
  calc
    (∑ T ∈ R.primeFactors.powerset,
        (4 : ℕ) ^ (∏ p ∈ T, p).primeFactors.card) =
        ∑ T ∈ R.primeFactors.powerset, ∏ _p ∈ T, (4 : ℕ) := by
      apply Finset.sum_congr rfl
      intro T hT
      obtain ⟨_, hcard⟩ :=
        Erdos387.prod_primeFactorSubset_squarefree_card hT
      have hpfcard : (∏ p ∈ T, p).primeFactors.card = T.card := by
        simpa [Erdos387.cardDistinctFactors_eq_primeFactors_card] using hcard
      simp [hpfcard]
    _ = ∏ _p ∈ R.primeFactors, (1 + (4 : ℕ)) := by
      exact (Finset.prod_one_add (R := ℕ) R.primeFactors).symm
    _ = 5 ^ R.primeFactors.card := by simp

/-- With one extra divisor factor, the same subset expansion has local
factor `1 + 4p`. -/
theorem sum_divisors_mul_four_pow_primeFactorsCard_eq_prod
    {R : ℕ} (hR : Squarefree R) :
    (∑ h ∈ R.divisors,
        h * (4 : ℕ) ^ h.primeFactors.card) =
      ∏ p ∈ R.primeFactors, (1 + 4 * p) := by
  rw [Erdos387.divisors_eq_image_prod_primeFactorSubsets hR,
    Finset.sum_image (Erdos387.prod_primeFactorSubsets_injOn R),
    Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro T hT
  obtain ⟨_, hcard⟩ := Erdos387.prod_primeFactorSubset_squarefree_card hT
  have hpfcard : (∏ p ∈ T, p).primeFactors.card = T.card := by
    simpa [Erdos387.cardDistinctFactors_eq_primeFactors_card] using hcard
  rw [hpfcard, Finset.prod_mul_distrib]
  simp [Nat.mul_comm]

/-- Truncating the squarefree divisor expansion can only decrease its
unnormalized quadratic weight. -/
theorem sum_filtered_divisors_four_pow_primeFactorsCard_le
    {R T : ℕ} (hR : Squarefree R) :
    (∑ h ∈ R.divisors.filter (fun h ↦ h ≤ T),
        (4 : ℕ) ^ h.primeFactors.card) ≤
      5 ^ R.primeFactors.card := by
  calc
    (∑ h ∈ R.divisors.filter (fun h ↦ h ≤ T),
        (4 : ℕ) ^ h.primeFactors.card) ≤
        ∑ h ∈ R.divisors, (4 : ℕ) ^ h.primeFactors.card := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ ↦ Nat.zero_le _)
    _ = 5 ^ R.primeFactors.card :=
      sum_divisors_four_pow_primeFactorsCard_eq_five_pow hR

/-- With one divisor factor, truncation at `T` costs at most the factor
`T`; this is the second endpoint estimate used in the divisor-range split. -/
theorem sum_filtered_divisors_mul_four_pow_primeFactorsCard_le
    {R T : ℕ} (hR : Squarefree R) :
    (∑ h ∈ R.divisors.filter (fun h ↦ h ≤ T),
        h * (4 : ℕ) ^ h.primeFactors.card) ≤
      T * 5 ^ R.primeFactors.card := by
  calc
    (∑ h ∈ R.divisors.filter (fun h ↦ h ≤ T),
        h * (4 : ℕ) ^ h.primeFactors.card) ≤
        ∑ h ∈ R.divisors.filter (fun h ↦ h ≤ T),
          T * (4 : ℕ) ^ h.primeFactors.card := by
      apply Finset.sum_le_sum
      intro h hh
      exact Nat.mul_le_mul_right _ (Finset.mem_filter.mp hh).2
    _ = T * (∑ h ∈ R.divisors.filter (fun h ↦ h ≤ T),
        (4 : ℕ) ^ h.primeFactors.card) := by
      rw [Finset.mul_sum]
    _ ≤ T * 5 ^ R.primeFactors.card := by
      exact Nat.mul_le_mul_left T
        (sum_filtered_divisors_four_pow_primeFactorsCard_le hR)

/-- A finite Euler product with local factors `1 + 4/p` is bounded by the
exponential of four times the reciprocal prime-factor mass. -/
theorem prod_one_add_four_div_le_exp_primeFactorMass (R : ℕ) :
    (∏ p ∈ R.primeFactors, (1 + (4 : ℝ) / p)) ≤
      Real.exp (4 * ∑ p ∈ R.primeFactors, (1 : ℝ) / p) := by
  calc
    (∏ p ∈ R.primeFactors, (1 + (4 : ℝ) / p)) ≤
        ∏ p ∈ R.primeFactors, Real.exp ((4 : ℝ) / p) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        simpa [add_comm] using Real.add_one_le_exp ((4 : ℝ) / p)
    _ = Real.exp (∑ p ∈ R.primeFactors, (4 : ℝ) / p) := by
      symm
      exact Real.exp_sum _ _
    _ = Real.exp (4 * ∑ p ∈ R.primeFactors, (1 : ℝ) / p) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

/-- Summation-ready exponential bound for all squarefree divisors. -/
theorem sum_divisors_four_pow_primeFactorsCard_div_le_exp
    {R : ℕ} (hR : Squarefree R) :
    (∑ h ∈ R.divisors,
        (4 : ℝ) ^ h.primeFactors.card / h) ≤
      Real.exp (4 * ∑ p ∈ R.primeFactors, (1 : ℝ) / p) := by
  rw [sum_divisors_four_pow_primeFactorsCard_div_eq_prod hR]
  exact prod_one_add_four_div_le_exp_primeFactorMass R

/-- The prime factors of a rough part are exactly the prime factors above
the cutoff, so their reciprocal mass inherits the elementary logarithmic
bound. -/
theorem sum_inv_primeFactors_roughPart_le_log_div
    {n y : ℕ} (hn : 0 < n) (hy : 1 ≤ y) :
    ∑ p ∈ (roughPart n y).primeFactors, (1 : ℝ) / p ≤
      (Nat.log 2 n : ℝ) / y := by
  have hsets : (roughPart n y).primeFactors = primeFactorsAbove n y := by
    ext p
    rw [mem_primeFactors_roughPart_iff, mem_primeFactorsAbove_iff]
  rw [hsets]
  exact sum_inv_primeFactorsAbove_le_log_div hn hy

/-- If all prime factors of `R` are at least `y`, while `R` is at most a
fixed constant times `y ^ K`, then `R` has at most `K` distinct prime
factors as soon as `y` exceeds that constant. -/
theorem primeFactors_card_le_of_rough_bound
    {R y C K : ℕ} (hR : 0 < R) (hyC : C < y)
    (hRle : R ≤ C * y ^ K)
    (hrough : ∀ p ∈ R.primeFactors, y ≤ p) :
    R.primeFactors.card ≤ K := by
  by_contra hnot
  have hK : K + 1 ≤ R.primeFactors.card := by omega
  have hypowprod : y ^ R.primeFactors.card ≤
      ∏ p ∈ R.primeFactors, p := by
    exact Finset.pow_card_le_prod R.primeFactors id y hrough
  have hprodR : (∏ p ∈ R.primeFactors, p) ≤ R :=
    Nat.le_of_dvd hR R.prod_primeFactors_dvd
  have hypos : 0 < y := by omega
  have hlow : y ^ (K + 1) ≤ R := by
    exact (Nat.pow_le_pow_right hypos hK).trans (hypowprod.trans hprodR)
  have hstrict : C * y ^ K < y ^ (K + 1) := by
    rw [pow_succ, Nat.mul_comm (y ^ K) y]
    exact (Nat.mul_lt_mul_right (pow_pos hypos K)).mpr hyC
  omega

/-- At the slow cutoff `y = N^(1/(4S))`, every divisor bounded by
`2 * N ^ 28` has only boundedly many prime factors above `y`.  The explicit
bound `112S` is deliberately crude but uniform in `N` and the divisor. -/
theorem eventually_primeFactors_card_roughPart_le
    {S : ℕ} (hS : 0 < S) :
    ∀ᶠ N : ℕ in Filter.atTop,
      let y := Nat.nthRoot (4 * S) N
      ∀ h : ℕ, 0 < h → h ≤ 2 * N ^ 28 →
        (roughPart h y).primeFactors.card ≤ 112 * S := by
  let k := 4 * S
  let K := 28 * k
  let C := 2 ^ (K + 1)
  have hk : k ≠ 0 := by simp [k, hS.ne']
  filter_upwards [eventually_nthRoot_ge k (C + 1) hk,
      eventually_nthRoot_ge k 1 hk] with N hyC hy1
  dsimp only
  intro h hhpos hhle
  let y := Nat.nthRoot k N
  let R := roughPart h y
  have hyC' : C < y := by
    dsimp [y]
    omega
  have hy1' : 1 ≤ y := by simpa [y] using hy1
  have hNroot : N ≤ 2 ^ k * y ^ k := by
    exact le_two_pow_mul_nthRoot_pow hk hy1'
  have hNpow : N ^ 28 ≤ (2 ^ k * y ^ k) ^ 28 :=
    Nat.pow_le_pow_left hNroot 28
  have hRleH : R ≤ h := by
    exact Nat.le_of_dvd hhpos (roughPart_dvd h y)
  have hscale : 2 * N ^ 28 ≤ C * y ^ K := by
    calc
      2 * N ^ 28 ≤ 2 * (2 ^ k * y ^ k) ^ 28 :=
        Nat.mul_le_mul_left 2 hNpow
      _ = C * y ^ K := by
        simp only [C, K, mul_pow, ← pow_mul, pow_succ]
        ring
  have hrough : ∀ p ∈ R.primeFactors, y ≤ p := by
    intro p hp
    exact (mem_primeFactors_roughPart_iff.mp hp).2.le
  have hcard : R.primeFactors.card ≤ K :=
    primeFactors_card_le_of_rough_bound
      (Nat.pos_of_ne_zero (roughPart_ne_zero h y)) hyC'
      (hRleH.trans (hhle.trans hscale)) hrough
  simpa [R, y, K, k, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcard

/-- Consequently the unnormalized squarefree divisor weight of such a
rough part is at most a fixed power of five, uniformly in `N`. -/
theorem eventually_five_pow_primeFactorsCard_roughPart_le
    {S : ℕ} (hS : 0 < S) :
    ∀ᶠ N : ℕ in Filter.atTop,
      let y := Nat.nthRoot (4 * S) N
      ∀ h : ℕ, 0 < h → h ≤ 2 * N ^ 28 →
        5 ^ (roughPart h y).primeFactors.card ≤ 5 ^ (112 * S) := by
  filter_upwards [eventually_primeFactors_card_roughPart_le hS] with N hN
  dsimp only at hN ⊢
  intro h hhpos hhle
  exact Nat.pow_le_pow_right (by norm_num) (hN h hhpos hhle)

/-- Since the preceding bound is independent of `N`, it is eventually at
most `N` itself.  This is the endpoint estimate used after truncating the
rough-divisor Euler sum. -/
theorem eventually_five_pow_primeFactorsCard_roughPart_le_self
    {S : ℕ} (hS : 0 < S) :
    ∀ᶠ N : ℕ in Filter.atTop,
      let y := Nat.nthRoot (4 * S) N
      ∀ h : ℕ, 0 < h → h ≤ 2 * N ^ 28 →
        5 ^ (roughPart h y).primeFactors.card ≤ N := by
  filter_upwards [eventually_five_pow_primeFactorsCard_roughPart_le hS,
      Filter.eventually_ge_atTop (5 ^ (112 * S))] with N hfive hN
  dsimp only at hfive ⊢
  intro h hhpos hhle
  exact (hfive h hhpos hhle).trans hN

/-- On the corrected B4 family, the complete quadratic rough-divisor sum
is controlled by the elementary logarithmic prime-factor tail. -/
theorem sum_roughDivisors_four_pow_div_le_exp_log_div
    {N y h m m' : ℕ}
    (hm : m ∈ squarefreeLargeGcdFreeOddCofactors N y)
    (hh : h ∣ shiftedCoefficientGcd m m')
    (hhpos : 0 < h) (hy : 1 ≤ y) :
    (∑ d ∈ (roughPart h y).divisors,
        (4 : ℝ) ^ d.primeFactors.card / d) ≤
      Real.exp (4 * ((Nat.log 2 h : ℝ) / y)) := by
  have hsq : Squarefree (roughPart h y) :=
    roughPart_squarefree_of_squarefreeLargeGcdFree hm hh
  have hEuler := sum_divisors_four_pow_primeFactorsCard_div_le_exp hsq
  have hmass := sum_inv_primeFactors_roughPart_le_log_div hhpos hy
  exact hEuler.trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hmass (by norm_num)))

/-- At the common slow cutoff, the full quadratic rough-divisor Euler sum
is eventually bounded by one absolute constant, uniformly in the two
cofactors and the chosen common divisor. -/
theorem eventually_sum_roughDivisors_four_pow_div_le_exp_twoForty
    {S : ℕ} (hS : 0 < S) :
    ∀ᶠ N : ℕ in Filter.atTop,
      let y := Nat.nthRoot (4 * S) N
      ∀ m ∈ squarefreeLargeGcdFreeOddCofactors N y,
        ∀ m' h : ℕ, h ∣ shiftedCoefficientGcd m m' → 0 < h →
          (∑ d ∈ (roughPart h y).divisors,
              (4 : ℝ) ^ d.primeFactors.card / d) ≤
            Real.exp 240 := by
  filter_upwards [eventually_slowCutoff_log_cube_div_le_one hS,
      eventually_nthRoot_ge (4 * S) 1 (by omega),
      Filter.eventually_ge_atTop 2] with N hslow hy hN
  dsimp only at hslow hy ⊢
  intro m hm m' h hh hhpos
  let y := Nat.nthRoot (4 * S) N
  have hy1 : 1 ≤ y := by simpa [y] using hy
  have hmRaw : m ∈ oddRawCofactors N :=
    squarefreeLargeGcdFreeOddCofactors_subset_oddRaw N y hm
  have hmle : m ≤ N ^ 28 := oddRawCofactors_le_pow_twenty_eight hmRaw
  have hgcdle : shiftedCoefficientGcd m m' ≤ shiftedTotient m := by
    unfold shiftedCoefficientGcd
    exact Nat.gcd_le_left _ (by
      have hmpos := oddRawCofactors_pos hmRaw
      exact hmpos.trans_le (Nat.le_add_right m (Nat.totient m)))
  have hhle : h ≤ 2 * N ^ 28 := by
    exact (Nat.le_of_dvd (by
      have hmpos := oddRawCofactors_pos hmRaw
      exact hmpos.trans_le (Nat.le_add_right m (Nat.totient m)))
        (hh.trans (Nat.gcd_dvd_left _ _))).trans
      ((shiftedTotient_le_two_mul m).trans
        (Nat.mul_le_mul_left 2 hmle))
  have hNcast : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNcast
  have hlogh : Real.log (h : ℝ) ≤
      Real.log ((2 * N ^ 28 : ℕ) : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (show (0 : ℝ) < h by exact_mod_cast hhpos)
      (show (0 : ℝ) < (2 * N ^ 28 : ℕ) by positivity)
      (by exact_mod_cast hhle)
  have hlogbound : Real.log (h : ℝ) ≤
      30 * (1 + Real.log (N : ℝ)) := by
    calc
      Real.log (h : ℝ) ≤
          Real.log ((2 * N ^ 28 : ℕ) : ℝ) := hlogh
      _ = Real.log (2 : ℝ) + 28 * Real.log (N : ℝ) := by
        push_cast
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        norm_num
      _ ≤ 30 * (1 + Real.log (N : ℝ)) := by
        nlinarith [Real.log_two_lt_d9]
  have hnatlog : (Nat.log 2 h : ℝ) ≤
      60 * (1 + Real.log (N : ℝ)) := by
    exact (natLog_two_le_two_realLog hhpos).trans (by nlinarith)
  have hlinearCube :
      1 + Real.log (N : ℝ) ≤
        (1 + Real.log (N : ℝ)) ^ 3 := by
    nlinarith [sq_nonneg (Real.log (N : ℝ)), hlogN]
  have hratio : ((Nat.log 2 h : ℝ) / y) ≤ 60 := by
    calc
      (Nat.log 2 h : ℝ) / y ≤
          (60 * (1 + Real.log (N : ℝ))) / y := by
        gcongr
      _ ≤ (60 * (1 + Real.log (N : ℝ)) ^ 3) / y := by
        gcongr
      _ = 60 * ((1 + Real.log (N : ℝ)) ^ 3 / y) := by ring
      _ ≤ 60 := by nlinarith
  have hEuler := sum_roughDivisors_four_pow_div_le_exp_log_div
    hm hh hhpos hy1
  exact hEuler.trans (Real.exp_le_exp.mpr (by nlinarith))

end Erdos822
