/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.BrunSieve
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Quantitative finite Euler products for Brun's sieve

The qualitative proof uses an odd Brun truncation whose depth is allowed to
grow (while `k` remains fixed).  This file isolates the elementary finite
probability estimate behind that argument: truncating the subset expansion of
an Euler product has an error bounded by the positive tail, and a powers-of-two
moment bounds that tail.
-/

namespace Erdos387

open Finset

open scoped BigOperators
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega

/-- The monomial attached to a subset of local sieve primes. -/
def subsetMonomial {ι : Type*} (x : ι → ℝ) (T : Finset ι) : ℝ :=
  ∏ p ∈ T, x p

/-- The finite Euler product associated to local densities `x p`. -/
def finiteEulerProduct {ι : Type*} (P : Finset ι) (x : ι → ℝ) : ℝ :=
  ∏ p ∈ P, (1 - x p)

/-- Inclusion--exclusion truncated after subsets of cardinality `L`. -/
def brunSubsetSum {ι : Type*} (P : Finset ι) (x : ι → ℝ) (L : ℕ) : ℝ :=
  ∑ T ∈ P.powerset,
    if T.card ≤ L then (-1 : ℝ) ^ T.card * subsetMonomial x T else 0

/-- The unsigned omitted tail of the subset expansion. -/
def brunSubsetTail {ι : Type*} (P : Finset ι) (x : ι → ℝ) (L : ℕ) : ℝ :=
  ∑ T ∈ P.powerset,
    if L < T.card then subsetMonomial x T else 0

/-- Once the truncation level reaches the number of available primes, the
finite subset tail vanishes identically. -/
theorem brunSubsetTail_eq_zero_of_card_le
    {ι : Type*} [DecidableEq ι] (P : Finset ι) (x : ι → ℝ) {L : ℕ}
    (hPL : P.card ≤ L) : brunSubsetTail P x L = 0 := by
  unfold brunSubsetTail
  apply Finset.sum_eq_zero
  intro T hT
  rw [if_neg]
  exact Nat.not_lt.mpr ((Finset.card_le_card
    (Finset.mem_powerset.mp hT)).trans hPL)

/-- Exact subset expansion of a finite Euler product. -/
theorem finiteEulerProduct_eq_sum_powerset {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (x : ι → ℝ) :
    finiteEulerProduct P x =
      ∑ T ∈ P.powerset,
        (-1 : ℝ) ^ T.card * subsetMonomial x T := by
  unfold finiteEulerProduct subsetMonomial
  simpa using (Finset.prod_sub (fun _ : ι => (1 : ℝ)) x P)

/-- A subset monomial is nonnegative when all local densities are. -/
theorem subsetMonomial_nonneg {ι : Type*} {x : ι → ℝ} {T : Finset ι}
    (hx : ∀ p ∈ T, 0 ≤ x p) : 0 ≤ subsetMonomial x T := by
  unfold subsetMonomial
  exact Finset.prod_nonneg hx

/-- The error of either parity of Brun truncation is bounded by the unsigned
tail. -/
theorem abs_brunSubsetSum_sub_finiteEulerProduct_le
    {ι : Type*} [DecidableEq ι] (P : Finset ι) (x : ι → ℝ) (L : ℕ)
    (hx : ∀ p ∈ P, 0 ≤ x p) :
    |brunSubsetSum P x L - finiteEulerProduct P x| ≤
      brunSubsetTail P x L := by
  rw [finiteEulerProduct_eq_sum_powerset]
  unfold brunSubsetSum brunSubsetTail
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ T ∈ P.powerset,
        ((if T.card ≤ L then
            (-1 : ℝ) ^ T.card * subsetMonomial x T else 0) -
          (-1 : ℝ) ^ T.card * subsetMonomial x T)|
        ≤ ∑ T ∈ P.powerset,
            |(if T.card ≤ L then
                (-1 : ℝ) ^ T.card * subsetMonomial x T else 0) -
              (-1 : ℝ) ^ T.card * subsetMonomial x T| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ T ∈ P.powerset,
          if L < T.card then subsetMonomial x T else 0 := by
      apply Finset.sum_congr rfl
      intro T hT
      have hmono : 0 ≤ subsetMonomial x T :=
        subsetMonomial_nonneg (fun p hp =>
          hx p (Finset.mem_powerset.mp hT hp))
      by_cases hcard : T.card ≤ L
      · rw [if_pos hcard, if_neg (Nat.not_lt.mpr hcard)]
        simp
      · have hlt : L < T.card := Nat.lt_of_not_ge hcard
        rw [if_neg hcard, if_pos hlt]
        rw [zero_sub, abs_neg, abs_mul, abs_neg_one_pow, one_mul,
          abs_of_nonneg hmono]

/-- Two-sided form of the preceding absolute-error estimate. -/
theorem brunSubsetSum_between_euler_sub_add_tail
    {ι : Type*} [DecidableEq ι] (P : Finset ι) (x : ι → ℝ) (L : ℕ)
    (hx : ∀ p ∈ P, 0 ≤ x p) :
    finiteEulerProduct P x - brunSubsetTail P x L ≤
        brunSubsetSum P x L ∧
      brunSubsetSum P x L ≤
        finiteEulerProduct P x + brunSubsetTail P x L := by
  have h := abs_brunSubsetSum_sub_finiteEulerProduct_le P x L hx
  have hsides := (abs_le.mp h)
  constructor <;> linarith

/-- If the omitted positive tail is at most half of the Euler product, the
odd and even Brun main terms both lie in a fixed positive window. -/
theorem brunSubsetSum_half_threeHalves
    {ι : Type*} [DecidableEq ι] (P : Finset ι) (x : ι → ℝ) (L : ℕ)
    (hx : ∀ p ∈ P, 0 ≤ x p)
    (htail : 2 * brunSubsetTail P x L ≤ finiteEulerProduct P x) :
    finiteEulerProduct P x / 2 ≤ brunSubsetSum P x L ∧
      brunSubsetSum P x L ≤ 3 * finiteEulerProduct P x / 2 := by
  obtain ⟨hlo, hhi⟩ :=
    brunSubsetSum_between_euler_sub_add_tail P x L hx
  constructor <;> linarith

/-- Expanding `∏ (1 + 2 x_p)` gives the powers-of-two moment of the subset
monomials. -/
theorem prod_one_add_two_mul_eq_sum_powerset
    {ι : Type*} [DecidableEq ι] (P : Finset ι) (x : ι → ℝ) :
    (∏ p ∈ P, (1 + 2 * x p)) =
      ∑ T ∈ P.powerset, (2 : ℝ) ^ T.card * subsetMonomial x T := by
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro T hT
  unfold subsetMonomial
  rw [Finset.prod_mul_distrib]
  simp

/-- Exponential-moment-free tail estimate.  Multiplication by
`2^(L+1)` is enough for all omitted subsets because each has at least `L+1`
members. -/
theorem pow_two_mul_brunSubsetTail_le
    {ι : Type*} [DecidableEq ι] (P : Finset ι) (x : ι → ℝ) (L : ℕ)
    (hx : ∀ p ∈ P, 0 ≤ x p) :
    (2 : ℝ) ^ (L + 1) * brunSubsetTail P x L ≤
      ∏ p ∈ P, (1 + 2 * x p) := by
  rw [prod_one_add_two_mul_eq_sum_powerset]
  unfold brunSubsetTail
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro T hT
  have hmono : 0 ≤ subsetMonomial x T :=
    subsetMonomial_nonneg (fun p hp =>
      hx p (Finset.mem_powerset.mp hT hp))
  by_cases hcard : L < T.card
  · rw [if_pos hcard]
    have hpow : (2 : ℝ) ^ (L + 1) ≤ (2 : ℝ) ^ T.card :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact mul_le_mul_of_nonneg_right hpow hmono
  · rw [if_neg hcard]
    simp only [mul_zero]
    positivity

/-- A convenient finite criterion for the usual ``half the Euler product''
tail bound.  The powers-of-two moment controls the omitted subsets, so it is
enough to compare that moment with the Euler product after multiplication by
`2^(L+1)`.  This formulation avoids divisions and is well suited to later
explicit estimates. -/
theorem two_mul_brunSubsetTail_le_of_moment
    {ι : Type*} [DecidableEq ι] (P : Finset ι) (x : ι → ℝ) (L : ℕ)
    (hx : ∀ p ∈ P, 0 ≤ x p)
    (hmoment :
      2 * (∏ p ∈ P, (1 + 2 * x p)) ≤
        (2 : ℝ) ^ (L + 1) * finiteEulerProduct P x) :
    2 * brunSubsetTail P x L ≤ finiteEulerProduct P x := by
  have htail := pow_two_mul_brunSubsetTail_le P x L hx
  have hpow : 0 < (2 : ℝ) ^ (L + 1) := by positivity
  rw [← mul_le_mul_iff_of_pos_left hpow]
  calc
    (2 : ℝ) ^ (L + 1) * (2 * brunSubsetTail P x L) =
        2 * ((2 : ℝ) ^ (L + 1) * brunSubsetTail P x L) := by ring
    _ ≤ 2 * (∏ p ∈ P, (1 + 2 * x p)) := by gcongr
    _ ≤ (2 : ℝ) ^ (L + 1) * finiteEulerProduct P x := hmoment

/-- Abstract bounding-sieve specialization of
`two_mul_brunSubsetTail_le_of_moment`. -/
theorem boundingSieve_brunTail_le_half_of_moment
    (s : BoundingSieve) (L : ℕ)
    (hmoment :
      2 * (∏ p ∈ s.prodPrimes.primeFactors, (1 + 2 * s.nu p)) ≤
        (2 : ℝ) ^ (L + 1) *
          finiteEulerProduct s.prodPrimes.primeFactors (fun p => s.nu p)) :
    2 * brunSubsetTail s.prodPrimes.primeFactors (fun p => s.nu p) L ≤
      finiteEulerProduct s.prodPrimes.primeFactors (fun p => s.nu p) := by
  apply two_mul_brunSubsetTail_le_of_moment
  intro p hp
  exact (s.nu_pos_of_prime p
    (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp)).le
  simpa only using hmoment

/-- Harmonic-product factor with a harmless value at the zero index. -/
noncomputable def harmonicProductFactor (a p : ℕ) : ℝ :=
  if p = 0 then 1 else 1 + (a : ℝ) / p

theorem harmonicProductFactor_one_le (a p : ℕ) :
    1 ≤ harmonicProductFactor a p := by
  unfold harmonicProductFactor
  split_ifs
  · rfl
  · exact le_add_of_nonneg_right (by positivity)

/-- Elementary polynomial bound for the full harmonic product.  This is a
finite Bernoulli-inequality substitute for the much sharper Mertens estimate:
`∏_{1 ≤ p ≤ z} (1 + a/p) ≤ (z+1)^a`. -/
theorem prod_range_harmonicProductFactor_le_pow (a z : ℕ) :
    (∏ p ∈ Finset.range (z + 1), harmonicProductFactor a p) ≤
      ((z + 1 : ℕ) : ℝ) ^ a := by
  induction z with
  | zero => simp [harmonicProductFactor]
  | succ z ih =>
      rw [show z + 1 + 1 = (z + 1) + 1 by omega,
        Finset.prod_range_succ]
      have hden : (0 : ℝ) < z + 1 := by positivity
      have hbern :
          1 + (a : ℝ) / (z + 1) ≤
            (1 + 1 / (z + 1 : ℝ)) ^ a := by
        simpa [div_eq_mul_inv] using
          (one_add_mul_le_pow
            (a := (1 / (z + 1 : ℝ)))
              (by have := one_div_pos.mpr hden; linarith : (-2 : ℝ) ≤ 1 / (z + 1)) a)
      have hfac :
          (z + 1 : ℝ) * (1 + 1 / (z + 1 : ℝ)) = z + 2 := by
        field_simp
        <;> ring
      calc
        (∏ p ∈ Finset.range (z + 1), harmonicProductFactor a p) *
              harmonicProductFactor a (z + 1) ≤
            (z + 1 : ℝ) ^ a * (1 + (a : ℝ) / (z + 1)) := by
          rw [harmonicProductFactor, if_neg (by omega : z + 1 ≠ 0)]
          simp only [Nat.cast_add, Nat.cast_one]
          have hfactor : 0 ≤ 1 + (a : ℝ) / (z + 1) := by
            exact add_nonneg (by norm_num) (div_nonneg (by positivity) hden.le)
          exact mul_le_mul_of_nonneg_right (by simpa using ih) hfactor
        _ ≤ (z + 1 : ℝ) ^ a *
              (1 + 1 / (z + 1 : ℝ)) ^ a := by gcongr
        _ = ((z + 1 : ℝ) * (1 + 1 / (z + 1 : ℝ))) ^ a := by
          rw [mul_pow]
        _ = (z + 2 : ℝ) ^ a := by rw [hfac]
        _ = (((z + 1 + 1 : ℕ) : ℝ)) ^ a := by push_cast; ring

/-- Any finite subproduct with indices in `[1,z]` satisfies the same
polynomial harmonic-product bound. -/
theorem prod_one_add_nat_div_le_pow
    (P : Finset ℕ) (a z : ℕ)
    (hpos : ∀ p ∈ P, 0 < p) (hle : ∀ p ∈ P, p ≤ z) :
    (∏ p ∈ P, (1 + (a : ℝ) / p)) ≤ ((z + 1 : ℕ) : ℝ) ^ a := by
  have hsub : P ⊆ Finset.range (z + 1) := by
    intro p hp
    rw [Finset.mem_range]
    have hpz := hle p hp
    omega
  calc
    (∏ p ∈ P, (1 + (a : ℝ) / p)) =
        ∏ p ∈ P, harmonicProductFactor a p := by
      apply Finset.prod_congr rfl
      intro p hp
      simp [harmonicProductFactor, (hpos p hp).ne']
    _ ≤ ∏ p ∈ Finset.range (z + 1), harmonicProductFactor a p := by
      apply Finset.prod_le_prod_of_subset_of_one_le hsub
      · intro p hp
        exact (by positivity : (0 : ℝ) ≤ 1).trans
          (harmonicProductFactor_one_le a p)
      · intro p hp _
        exact harmonicProductFactor_one_le a p
    _ ≤ ((z + 1 : ℕ) : ℝ) ^ a :=
      prod_range_harmonicProductFactor_le_pow a z

/-- The abstract sieve main sum for a Brun weight is literally the truncated
subset expansion of its local Euler product. -/
theorem boundingSieve_mainSum_brunLowerWeight_eq_brunSubsetSum
    (s : BoundingSieve) (L : ℕ) :
    s.mainSum (brunLowerWeight L) =
      brunSubsetSum s.prodPrimes.primeFactors (fun p => s.nu p) L := by
  rw [BoundingSieve.mainSum,
    divisors_eq_image_prod_primeFactorSubsets s.prodPrimes_squarefree,
    Finset.sum_image (prod_primeFactorSubsets_injOn s.prodPrimes)]
  unfold brunSubsetSum brunLowerWeight subsetMonomial
  apply Finset.sum_congr rfl
  intro T hT
  obtain ⟨hSq, hcard⟩ := prod_primeFactorSubset_squarefree_card hT
  have hprime : ∀ p ∈ T, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors
      (Finset.mem_powerset.mp hT hp)
  have hpf : (∏ p ∈ T, p).primeFactors = T :=
    Nat.primeFactors_prod hprime
  have hdvd : (∏ p ∈ T, p) ∣ s.prodPrimes := by
    calc
      ∏ p ∈ T, p ∣ ∏ p ∈ s.prodPrimes.primeFactors, p :=
        Finset.prod_dvd_prod_of_subset _ _ _
          (Finset.mem_powerset.mp hT)
      _ = s.prodPrimes :=
        Nat.prod_primeFactors_of_squarefree s.prodPrimes_squarefree
  have hnu := s.prod_primeFactors_nu hdvd
  have hOmega : Ω (∏ p ∈ T, p) = T.card := by
    calc
      Ω (∏ p ∈ T, p) = ω (∏ p ∈ T, p) :=
        ((ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree
          hSq.ne_zero).mpr hSq).symm
      _ = T.card := hcard
  rw [hcard, ArithmeticFunction.moebius_apply_of_squarefree hSq,
    hOmega, ← hnu, hpf]
  by_cases hTL : T.card ≤ L <;> simp [hTL]

/-- The same identity for the even Brun upper weight. -/
theorem boundingSieve_mainSum_brunUpperWeight_eq_brunSubsetSum
    (s : BoundingSieve) (L : ℕ) :
    s.mainSum (brunUpperWeight L) =
      brunSubsetSum s.prodPrimes.primeFactors (fun p => s.nu p) L := by
  have h := boundingSieve_mainSum_brunLowerWeight_eq_brunSubsetSum s L
  have hw : brunUpperWeight L = brunLowerWeight L := by
    funext d
    rfl
  rw [hw]
  exact h

/-- Consequently the main sum of a Brun weight differs from the local Euler
product by at most the positive subset tail. -/
theorem boundingSieve_abs_mainSum_brunLowerWeight_sub_euler_le
    (s : BoundingSieve) (L : ℕ) :
    |s.mainSum (brunLowerWeight L) -
        finiteEulerProduct s.prodPrimes.primeFactors (fun p => s.nu p)| ≤
      brunSubsetTail s.prodPrimes.primeFactors (fun p => s.nu p) L := by
  rw [boundingSieve_mainSum_brunLowerWeight_eq_brunSubsetSum]
  apply abs_brunSubsetSum_sub_finiteEulerProduct_le
  intro p hp
  exact (s.nu_pos_of_prime p
    (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp)).le

/-- Upper and lower Brun weights have the same quantitative main-term
approximation. -/
theorem boundingSieve_abs_mainSum_brunUpperWeight_sub_euler_le
    (s : BoundingSieve) (L : ℕ) :
    |s.mainSum (brunUpperWeight L) -
        finiteEulerProduct s.prodPrimes.primeFactors (fun p => s.nu p)| ≤
      brunSubsetTail s.prodPrimes.primeFactors (fun p => s.nu p) L := by
  rw [boundingSieve_mainSum_brunUpperWeight_eq_brunSubsetSum]
  apply abs_brunSubsetSum_sub_finiteEulerProduct_le
  intro p hp
  exact (s.nu_pos_of_prime p
    (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp)).le

/-- Ready-to-use fixed-window control of both abstract Brun main sums. -/
theorem boundingSieve_brunMainSums_half_threeHalves
    (s : BoundingSieve) (L : ℕ)
    (htail : 2 * brunSubsetTail s.prodPrimes.primeFactors
        (fun p => s.nu p) L ≤
      finiteEulerProduct s.prodPrimes.primeFactors (fun p => s.nu p)) :
    finiteEulerProduct s.prodPrimes.primeFactors (fun p => s.nu p) / 2 ≤
        s.mainSum (brunLowerWeight L) ∧
      s.mainSum (brunUpperWeight L) ≤
        3 * finiteEulerProduct s.prodPrimes.primeFactors
          (fun p => s.nu p) / 2 := by
  have hx : ∀ p ∈ s.prodPrimes.primeFactors, 0 ≤ s.nu p := by
    intro p hp
    exact (s.nu_pos_of_prime p
      (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)).le
  have hwindow := brunSubsetSum_half_threeHalves
    s.prodPrimes.primeFactors (fun p => s.nu p) L hx htail
  rw [← boundingSieve_mainSum_brunLowerWeight_eq_brunSubsetSum] at hwindow
  refine ⟨hwindow.1, ?_⟩
  rw [boundingSieve_mainSum_brunUpperWeight_eq_brunSubsetSum,
    ← boundingSieve_mainSum_brunLowerWeight_eq_brunSubsetSum]
  exact hwindow.2

/-- Full finite inclusion--exclusion: a Brun main sum at any level at least
the number of sieve primes equals its Euler product exactly. -/
theorem boundingSieve_mainSum_brunLowerWeight_eq_euler_of_card_le
    (s : BoundingSieve) {L : ℕ} (hcard : s.prodPrimes.primeFactors.card ≤ L) :
    s.mainSum (brunLowerWeight L) =
      finiteEulerProduct s.prodPrimes.primeFactors (fun p => s.nu p) := by
  rw [boundingSieve_mainSum_brunLowerWeight_eq_brunSubsetSum]
  have h := abs_brunSubsetSum_sub_finiteEulerProduct_le
    s.prodPrimes.primeFactors (fun p => s.nu p) L (fun p hp =>
      (s.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)).le)
  rw [brunSubsetTail_eq_zero_of_card_le _ _ hcard, abs_nonpos_iff] at h
  exact sub_eq_zero.mp h

theorem boundingSieve_mainSum_brunUpperWeight_eq_euler_of_card_le
    (s : BoundingSieve) {L : ℕ} (hcard : s.prodPrimes.primeFactors.card ≤ L) :
    s.mainSum (brunUpperWeight L) =
      finiteEulerProduct s.prodPrimes.primeFactors (fun p => s.nu p) := by
  rw [boundingSieve_mainSum_brunUpperWeight_eq_brunSubsetSum]
  rw [← boundingSieve_mainSum_brunLowerWeight_eq_brunSubsetSum]
  exact boundingSieve_mainSum_brunLowerWeight_eq_euler_of_card_le s hcard

/-- Every local factor in a bounding sieve is strictly positive, hence so is
its finite Euler product. -/
theorem boundingSieve_finiteEulerProduct_pos (s : BoundingSieve) :
    0 < finiteEulerProduct s.prodPrimes.primeFactors (fun p => s.nu p) := by
  unfold finiteEulerProduct
  apply Finset.prod_pos
  intro p hp
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  have hpDvd := Nat.dvd_of_mem_primeFactors hp
  exact sub_pos.mpr (s.nu_lt_one_of_prime p hpPrime hpDvd)

end Erdos387
