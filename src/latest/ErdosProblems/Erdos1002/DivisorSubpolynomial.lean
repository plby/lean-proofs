import ErdosProblems.Erdos1002.DivisorSquareAverage
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Subpolynomial bounds for the divisor function

The window estimate only needs a bound on `sigma_{-1}(n)` which is
`o(log n)`; the sharper classical `O(log log n)` estimate is unnecessary.
This file develops the elementary divisor bound needed for that purpose.
All constants are explicit finite products of convergent geometric-series
moments.
-/

open Filter
open scoped ArithmeticFunction.sigma BigOperators Topology

namespace Erdos1002

noncomputable section

/-- The convergent local constant which absorbs one fixed small prime. -/
def divisorLocalPowerConstant (k p : ℕ) : ℝ :=
  ∑' a : ℕ, ((a + 1 : ℕ) : ℝ) ^ k * (1 / (p : ℝ)) ^ a

private theorem summable_divisorLocalPowerTerm
    (k p : ℕ) (hp : 2 ≤ p) :
    Summable fun a : ℕ ↦
      ((a + 1 : ℕ) : ℝ) ^ k * (1 / (p : ℝ)) ^ a := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hrnorm : ‖(1 / (p : ℝ))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (div_lt_one (by positivity)).2 (by linarith)
  have hs : Summable fun n : ℕ ↦
      (n : ℝ) ^ k * (1 / (p : ℝ)) ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one k hrnorm
  have hshift : Summable fun a : ℕ ↦
      ((a + 1 : ℕ) : ℝ) ^ k * (1 / (p : ℝ)) ^ (a + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using!
      ((summable_nat_add_iff (f := fun n : ℕ ↦
        (n : ℝ) ^ k * (1 / (p : ℝ)) ^ n) 1).2 hs)
  have hmul := Summable.mul_left (p : ℝ) hshift
  convert! hmul using 1
  funext a
  rw [pow_succ]
  field_simp

theorem one_le_divisorLocalPowerConstant
    (k p : ℕ) (hp : 2 ≤ p) :
    1 ≤ divisorLocalPowerConstant k p := by
  have hs := summable_divisorLocalPowerTerm k p hp
  have hterm := hs.le_tsum 0 (fun a ha ↦ by positivity)
  simpa [divisorLocalPowerConstant] using! hterm

theorem divisor_power_le_local_mul_prime_power
    (k p a : ℕ) (hp : 2 ≤ p) :
    (((a + 1 : ℕ) : ℝ) ^ k) ≤
      divisorLocalPowerConstant k p * (p : ℝ) ^ a := by
  have hs := summable_divisorLocalPowerTerm k p hp
  have hterm := hs.le_tsum a (fun b hb ↦ by positivity)
  have hpPow : 0 < (p : ℝ) ^ a := by positivity
  have hrewrite :
      ((a + 1 : ℕ) : ℝ) ^ k * (1 / (p : ℝ)) ^ a =
        ((a + 1 : ℕ) : ℝ) ^ k / (p : ℝ) ^ a := by
    rw [one_div, inv_pow, div_eq_mul_inv]
  change
    ((a + 1 : ℕ) : ℝ) ^ k * (1 / (p : ℝ)) ^ a ≤
      divisorLocalPowerConstant k p at hterm
  rw [hrewrite] at hterm
  exact (div_le_iff₀ hpPow).mp hterm

private theorem nat_succ_le_two_pow (a : ℕ) :
    a + 1 ≤ 2 ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [pow_succ]
      omega

/-- For a prime beyond `2^k`, no local constant is needed. -/
theorem divisor_power_le_prime_power_of_two_pow_le
    (k p a : ℕ) (hp : 2 ^ k ≤ p) :
    ((a + 1 : ℕ) ^ k) ≤ p ^ a := by
  calc
    (a + 1) ^ k ≤ (2 ^ a) ^ k :=
      Nat.pow_le_pow_left (nat_succ_le_two_pow a) k
    _ = 2 ^ (a * k) := (pow_mul 2 a k).symm
    _ = 2 ^ (k * a) := by rw [Nat.mul_comm]
    _ = (2 ^ k) ^ a := pow_mul 2 k a
    _ ≤ p ^ a := Nat.pow_le_pow_left hp a

/-- A finite constant which simultaneously absorbs every prime below
`2^k`. -/
def divisorPowerConstant (k : ℕ) : ℝ :=
  ∏ p ∈ Finset.Icc 2 (2 ^ k), max 1 (divisorLocalPowerConstant k p)

theorem one_le_divisorPowerConstant (k : ℕ) :
    1 ≤ divisorPowerConstant k := by
  unfold divisorPowerConstant
  exact Finset.one_le_prod fun p _ ↦ le_max_left _ _

/-- The factor attached to one prime: only primes below `2^k` carry a
constant. -/
def divisorPrimeMultiplier (k p : ℕ) : ℝ :=
  if p < 2 ^ k then max 1 (divisorLocalPowerConstant k p) else 1

theorem one_le_divisorPrimeMultiplier (k p : ℕ) :
    1 ≤ divisorPrimeMultiplier k p := by
  unfold divisorPrimeMultiplier
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem divisor_factor_power_le_multiplier
    (k p a : ℕ) (hp : p.Prime) :
    (((a + 1 : ℕ) : ℝ) ^ k) ≤
      divisorPrimeMultiplier k p * (p : ℝ) ^ a := by
  have hp2 : 2 ≤ p := hp.two_le
  by_cases hsmall : p < 2 ^ k
  · rw [divisorPrimeMultiplier, if_pos hsmall]
    exact (divisor_power_le_local_mul_prime_power k p a hp2).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  · have hlarge : 2 ^ k ≤ p := le_of_not_gt hsmall
    rw [divisorPrimeMultiplier, if_neg hsmall, one_mul]
    exact_mod_cast divisor_power_le_prime_power_of_two_pow_le k p a hlarge

/-- The product of prime multipliers occurring in one factorization is
bounded by the fixed finite constant `divisorPowerConstant k`. -/
theorem prod_divisorPrimeMultiplier_le
    (k n : ℕ) :
    (∏ p ∈ n.primeFactors, divisorPrimeMultiplier k p) ≤
      divisorPowerConstant k := by
  let s := n.primeFactors.filter fun p ↦ p < 2 ^ k
  have hs : s ⊆ Finset.Icc 2 (2 ^ k) := by
    intro p hp
    simp only [s, Finset.mem_filter] at hp
    exact Finset.mem_Icc.mpr
      ⟨(Nat.prime_of_mem_primeFactors hp.1).two_le, hp.2.le⟩
  have hremove :
      (∏ p ∈ n.primeFactors, divisorPrimeMultiplier k p) =
        ∏ p ∈ s, max 1 (divisorLocalPowerConstant k p) := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro p hp
    by_cases hsmall : p < 2 ^ k
    · simp [divisorPrimeMultiplier, hsmall]
    · simp [divisorPrimeMultiplier, hsmall]
  rw [hremove]
  unfold divisorPowerConstant
  calc
    (∏ p ∈ s, max 1 (divisorLocalPowerConstant k p)) ≤
        (∏ p ∈ s, max 1 (divisorLocalPowerConstant k p)) *
          ∏ p ∈ Finset.Icc 2 (2 ^ k) \ s,
            max 1 (divisorLocalPowerConstant k p) := by
      apply le_mul_of_one_le_right (by positivity)
      exact Finset.one_le_prod fun p _ ↦ le_max_left _ _
    _ = ∏ p ∈ Finset.Icc 2 (2 ^ k),
          max 1 (divisorLocalPowerConstant k p) := by
      rw [mul_comm, Finset.prod_sdiff hs]

/-- Fixed-power divisor bound: for every `k`, the `k`-th power of the
number of divisors is bounded by a constant times `n`. -/
theorem card_divisors_pow_le
    (k n : ℕ) (hn : n ≠ 0) :
    ((n.divisors.card : ℝ) ^ k) ≤
      divisorPowerConstant k * (n : ℝ) := by
  rw [Nat.card_divisors hn]
  push_cast
  rw [← Finset.prod_pow]
  have hfac :
      (∏ p ∈ n.primeFactors,
          ((n.factorization p : ℝ) + 1) ^ k) ≤
        ∏ p ∈ n.primeFactors,
          (divisorPrimeMultiplier k p *
            (p : ℝ) ^ n.factorization p) := by
    apply Finset.prod_le_prod
    · intro p _hp
      positivity
    · intro p hp
      have hpPrime := Nat.prime_of_mem_primeFactors hp
      simpa only [Nat.cast_add, Nat.cast_one] using!
        divisor_factor_power_le_multiplier
          k p (n.factorization p) hpPrime
  calc
    (∏ p ∈ n.primeFactors,
        ((n.factorization p : ℝ) + 1) ^ k) ≤
        ∏ p ∈ n.primeFactors,
          (divisorPrimeMultiplier k p *
            (p : ℝ) ^ n.factorization p) := hfac
    _ = (∏ p ∈ n.primeFactors, divisorPrimeMultiplier k p) *
          ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ p ∈ n.primeFactors, divisorPrimeMultiplier k p) *
          (n : ℝ) := by
      congr 1
      exact_mod_cast (by
        simpa only [Nat.prod_factorization_eq_prod_primeFactors] using!
          Nat.factorization_prod_pow_eq_self hn)
    _ ≤ divisorPowerConstant k * (n : ℝ) :=
      mul_le_mul_of_nonneg_right
        (prod_divisorPrimeMultiplier_le k n) (Nat.cast_nonneg n)

/-- The divisor-counting function is eventually bounded by every positive
real power.  This is the standard subpolynomial divisor bound, derived here
from `card_divisors_pow_le` with all constants internal to the proof. -/
theorem eventually_card_divisors_le_rpow
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (n.divisors.card : ℝ) ≤ (n : ℝ) ^ ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  have hkpos : 0 < k := by
    have hone : (0 : ℝ) < 1 / ε := one_div_pos.mpr hε
    exact_mod_cast (lt_trans hone hk)
  have hk0 : k ≠ 0 := Nat.ne_of_gt hkpos
  have hεk : 1 < ε * (k : ℝ) := by
    have := mul_lt_mul_of_pos_left hk hε
    simpa [hε.ne'] using! this
  let d : ℝ := ε * (k : ℝ) - 1
  have hd : 0 < d := by dsimp [d]; linarith
  let C : ℝ := divisorPowerConstant k
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact zero_le_one.trans (one_le_divisorPowerConstant k)
  have hrpow : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ d) atTop atTop :=
    (tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop
  have hCe : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) ^ d :=
    hrpow.eventually (eventually_ge_atTop C)
  filter_upwards [hCe, eventually_atTop.2 ⟨1, fun n hn ↦ hn⟩] with n hCn hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcardPow : ((n.divisors.card : ℝ) ^ k) ≤ C * (n : ℝ) := by
    simpa only [C] using! card_divisors_pow_le k n hn0
  have hCnMul : C * (n : ℝ) ≤ (n : ℝ) ^ (ε * (k : ℝ)) := by
    calc
      C * (n : ℝ) ≤ (n : ℝ) ^ d * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hCn hnR.le
      _ = (n : ℝ) ^ (d + 1) := by
        calc
          (n : ℝ) ^ d * (n : ℝ) =
              (n : ℝ) ^ d * (n : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ = (n : ℝ) ^ (d + 1) := (Real.rpow_add hnR d 1).symm
      _ = (n : ℝ) ^ (ε * (k : ℝ)) := by
        congr 1
        dsimp [d]
        ring
  have hpow :
      ((n.divisors.card : ℝ) ^ k) ≤ ((n : ℝ) ^ ε) ^ k := by
    calc
      ((n.divisors.card : ℝ) ^ k) ≤ C * (n : ℝ) := hcardPow
      _ ≤ (n : ℝ) ^ (ε * (k : ℝ)) := hCnMul
      _ = ((n : ℝ) ^ ε) ^ k := by
        rw [Real.rpow_mul hnR.le, Real.rpow_natCast]
  exact (pow_le_pow_iff_left₀ (by positivity)
    (Real.rpow_nonneg hnR.le ε) hk0).mp hpow

/-! ## Reciprocal divisor sums -/

/-- The arithmetic function usually denoted `sigma_{-1}`. -/
def reciprocalDivisorSum (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, 1 / (d : ℝ)

theorem reciprocalDivisorSum_nonneg (n : ℕ) :
    0 ≤ reciprocalDivisorSum n := by
  unfold reciprocalDivisorSum
  positivity

private theorem real_harmonic_Icc_eq (R : ℕ) :
    (∑ d ∈ Finset.Icc 1 R, 1 / (d : ℝ)) = (harmonic R : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  simp only [one_div]

/-- Splitting divisors at an arbitrary positive threshold.  The small
divisors contribute a harmonic sum and every large divisor contributes at
most `1/R`. -/
theorem reciprocalDivisorSum_le_harmonic_add_card_div
    {n R : ℕ} (hn : n ≠ 0) (hR : 0 < R) :
    reciprocalDivisorSum n ≤
      (harmonic R : ℝ) + (n.divisors.card : ℝ) / R := by
  let s := n.divisors.filter fun d ↦ d ≤ R
  let t := n.divisors.filter fun d ↦ ¬d ≤ R
  have hsplit :
      reciprocalDivisorSum n =
        (∑ d ∈ s, 1 / (d : ℝ)) + ∑ d ∈ t, 1 / (d : ℝ) := by
    unfold reciprocalDivisorSum s t
    exact (Finset.sum_filter_add_sum_filter_not n.divisors
      (fun d ↦ d ≤ R) (fun d ↦ 1 / (d : ℝ))).symm
  have hsSubset : s ⊆ Finset.Icc 1 R := by
    intro d hd
    simp only [s, Finset.mem_filter] at hd
    have hdDvd : d ∣ n := (Nat.mem_divisors.mp hd.1).1
    have hdPos : 0 < d :=
      Nat.pos_of_dvd_of_pos hdDvd (Nat.pos_of_ne_zero hn)
    exact Finset.mem_Icc.mpr ⟨hdPos, hd.2⟩
  have hsBound :
      (∑ d ∈ s, 1 / (d : ℝ)) ≤ (harmonic R : ℝ) := by
    rw [← real_harmonic_Icc_eq R]
    apply Finset.sum_le_sum_of_subset_of_nonneg hsSubset
    intro d _hd _hds
    positivity
  have htPoint : ∀ d ∈ t, 1 / (d : ℝ) ≤ 1 / (R : ℝ) := by
    intro d hd
    simp only [t, Finset.mem_filter, not_le] at hd
    have hRR : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
    have hdR : (R : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.2.le
    exact one_div_le_one_div_of_le hRR hdR
  have htBound :
      (∑ d ∈ t, 1 / (d : ℝ)) ≤
        (n.divisors.card : ℝ) / R := by
    calc
      (∑ d ∈ t, 1 / (d : ℝ)) ≤
          ∑ _d ∈ t, 1 / (R : ℝ) := by
        exact Finset.sum_le_sum fun d hd ↦ htPoint d hd
      _ = (t.card : ℝ) / R := by
        simp [div_eq_mul_inv]
      _ ≤ (n.divisors.card : ℝ) / R := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
        · positivity
  rw [hsplit]
  exact add_le_add hsBound htBound

/-- Quantitative form of sublogarithmic growth.  For every fixed positive
`δ`, the reciprocal divisor sum is eventually bounded by

`1 + log 2 + δ log n + n^(-δ/2)`.

The ceiling cutoff avoids any hidden floor error. -/
theorem eventually_reciprocalDivisorSum_le_log_add_rpow
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      reciprocalDivisorSum n ≤
        1 + Real.log 2 + δ * Real.log (n : ℝ) +
          (n : ℝ) ^ (-(δ / 2)) := by
  have hcard := eventually_card_divisors_le_rpow (δ / 2) (by positivity)
  filter_upwards [hcard, eventually_atTop.2 ⟨1, fun n hn ↦ hn⟩] with n hcard hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  let x : ℝ := (n : ℝ) ^ δ
  let R : ℕ := ⌈x⌉₊
  have hxPos : 0 < x := by dsimp [x]; exact Real.rpow_pos_of_pos hnR _
  have hxOne : 1 ≤ x := by
    dsimp [x]
    exact Real.one_le_rpow hnOne hδ.le
  have hR : 0 < R := by
    dsimp [R]
    exact Nat.ceil_pos.mpr hxPos
  have hRReal : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hxR : x ≤ (R : ℝ) := by
    dsimp [R]
    exact Nat.le_ceil x
  have hRtwo : (R : ℝ) ≤ 2 * x := by
    have hceil : (R : ℝ) < x + 1 := by
      dsimp [R]
      exact Nat.ceil_lt_add_one hxPos.le
    linarith
  have hlogR : Real.log (R : ℝ) ≤
      Real.log 2 + δ * Real.log (n : ℝ) := by
    calc
      Real.log (R : ℝ) ≤ Real.log (2 * x) :=
        Real.log_le_log hRReal hRtwo
      _ = Real.log 2 + Real.log x := by
        rw [Real.log_mul (by norm_num) hxPos.ne']
      _ = Real.log 2 + δ * Real.log (n : ℝ) := by
        rw [show Real.log x = δ * Real.log (n : ℝ) by
          dsimp [x]
          exact Real.log_rpow hnR δ]
  have hharmonic : (harmonic R : ℝ) ≤
      1 + Real.log 2 + δ * Real.log (n : ℝ) := by
    exact (harmonic_le_one_add_log R).trans (by linarith)
  have htail : (n.divisors.card : ℝ) / R ≤
      (n : ℝ) ^ (-(δ / 2)) := by
    have hdiv : (n.divisors.card : ℝ) / (R : ℝ) ≤
        (n : ℝ) ^ (δ / 2) / x := by
      exact div_le_div₀ (by positivity) hcard hxPos hxR
    calc
      (n.divisors.card : ℝ) / (R : ℝ) ≤
          (n : ℝ) ^ (δ / 2) / x := hdiv
      _ = (n : ℝ) ^ (δ / 2 - δ) := by
        dsimp [x]
        exact (Real.rpow_sub hnR (δ / 2) δ).symm
      _ = (n : ℝ) ^ (-(δ / 2)) := by
        congr 1
        ring
  exact (reciprocalDivisorSum_le_harmonic_add_card_div hn0 hR).trans
    (add_le_add hharmonic htail)

/-- The reciprocal divisor sum is `o(log n)`.  This weaker consequence of
the elementary subpolynomial divisor bound is sufficient in the manuscript's
window estimate; no prime-number theorem or Mertens estimate is used. -/
theorem tendsto_reciprocalDivisorSum_div_log :
    Tendsto
      (fun n : ℕ ↦ reciprocalDivisorSum n / Real.log (n : ℝ))
      atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hbound := eventually_reciprocalDivisorSum_le_log_add_rpow δ hδ
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto
      (fun n : ℕ ↦ (1 + Real.log 2) / Real.log (n : ℝ))
      atTop (nhds 0) :=
    hlog.const_div_atTop (1 + Real.log 2)
  have hrpow : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ (-(δ / 2))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by positivity : 0 < δ / 2)).comp
      tendsto_natCast_atTop_atTop
  have htailRatio : Tendsto
      (fun n : ℕ ↦
        (n : ℝ) ^ (-(δ / 2)) / Real.log (n : ℝ))
      atTop (nhds 0) :=
    hrpow.div_atTop hlog
  let M : ℕ → ℝ := fun n ↦
    (1 + Real.log 2) / Real.log (n : ℝ) + δ +
      (n : ℝ) ^ (-(δ / 2)) / Real.log (n : ℝ)
  have hM : Tendsto M atTop (nhds δ) := by
    simpa only [M, zero_add, add_zero] using!
      (hconst.add tendsto_const_nhds).add htailRatio
  have hMclose : ∀ᶠ n : ℕ in atTop, dist (M n) δ < ε / 4 :=
    (Metric.tendsto_nhds.mp hM) (ε / 4) (by positivity)
  filter_upwards [hbound, hMclose,
    eventually_atTop.2 ⟨3, fun n hn ↦ hn⟩] with n hnBound hnClose hn3
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 3) hn3)
  have hlogPos : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hratioNonneg :
      0 ≤ reciprocalDivisorSum n / Real.log (n : ℝ) :=
    div_nonneg (reciprocalDivisorSum_nonneg n) hlogPos.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hratioNonneg]
  have hratioM :
      reciprocalDivisorSum n / Real.log (n : ℝ) ≤ M n := by
    calc
      reciprocalDivisorSum n / Real.log (n : ℝ) ≤
          (1 + Real.log 2 + δ * Real.log (n : ℝ) +
            (n : ℝ) ^ (-(δ / 2))) / Real.log (n : ℝ) :=
        div_le_div_of_nonneg_right hnBound hlogPos.le
      _ = M n := by
        dsimp [M]
        field_simp
  have hMupper : M n < δ + ε / 4 := by
    rw [Real.dist_eq] at hnClose
    linarith [le_abs_self (M n - δ)]
  calc
    reciprocalDivisorSum n / Real.log (n : ℝ) ≤ M n := hratioM
    _ < δ + ε / 4 := hMupper
    _ < ε := by dsimp [δ]; linarith

end

end Erdos1002
