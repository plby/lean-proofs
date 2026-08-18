import ErdosProblems.Erdos285.Dispersion
import UnitFractions.ForMathlib.BasicEstimates

/-!
# Divisor-function estimates for Erdős Problem 1161

This file packages the three elementary maximal-order estimates used in the
anticoncentration argument for permutation orders.  We use real-valued
inequalities so that the statements can be inserted directly into the
normalized cycle-index estimates.
-/

namespace Erdos1161

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

/-- The number `τ(n)` of positive divisors of `n`. -/
def divisorCount (n : ℕ) : ℕ := n.divisors.card

/-- The sum `σ(n)` of the positive divisors of `n`. -/
def divisorSum (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

/-- The number `ω(n)` of distinct prime divisors of `n`. -/
def distinctPrimeFactorCount (n : ℕ) : ℕ := n.primeFactors.card

@[simp] lemma divisorCount_eq_sigma_zero (n : ℕ) :
    divisorCount n = ArithmeticFunction.sigma 0 n := by
  simp [divisorCount, ArithmeticFunction.sigma_zero_apply]

@[simp] lemma divisorSum_eq_sum_divisors (n : ℕ) :
    divisorSum n = ∑ d ∈ n.divisors, d := by
  exact ArithmeticFunction.sigma_one_apply n

/-- Quantified `τ(n) = n^{o(1)}`: every fixed positive power eventually
dominates the divisor count. -/
theorem eventually_divisorCount_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (divisorCount n : ℝ) ≤ (n : ℝ) ^ ε := by
  simpa [divisorCount, ArithmeticFunction.sigma_zero_apply] using
    weak_divisor_bound ε hε

/-- Threshold form of `eventually_divisorCount_le_rpow`. -/
theorem exists_divisorCount_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (divisorCount n : ℝ) ≤ (n : ℝ) ^ ε := by
  simpa only [eventually_atTop] using eventually_divisorCount_le_rpow ε hε

/-- The concrete exponent used in the local cycle-index estimate. -/
theorem eventually_divisorCount_le_twelfth_power :
    ∀ᶠ n : ℕ in atTop,
      (divisorCount n : ℝ) ≤ (n : ℝ) ^ (1 / 12 : ℝ) := by
  exact eventually_divisorCount_le_rpow (1 / 12) (by norm_num)

private theorem divisorExponent_tendsto :
    Tendsto (fun n : ℕ ↦
      2 * Real.log 2 / Real.log (Real.log n)) atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop
    (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

private theorem eventual_divisor_exponent_le (d : ℕ) (hd : 0 < d) :
    ∃ M : ℕ, ∀ n ≥ M,
      2 * Real.log 2 / Real.log (Real.log n) ≤
        1 / (8 * (d : ℝ) ^ 2) := by
  have hev : ∀ᶠ n : ℕ in atTop,
      2 * Real.log 2 / Real.log (Real.log n) <
        1 / (8 * (d : ℝ) ^ 2) :=
    divisorExponent_tendsto.eventually
      (Iio_mem_nhds (show (0 : ℝ) < 1 / (8 * (d : ℝ) ^ 2) by positivity))
  obtain ⟨M, hM⟩ := eventually_atTop.1 hev
  exact ⟨M, fun n hn ↦ (hM n hn).le⟩

private theorem divisorCount_power_le_eighth_of_exponent
    (d n N : ℕ) (hd : 0 < d) (hn : 1 ≤ n) (hN : 1 ≤ N)
    (hnN : n ≤ N ^ d) (e : ℝ)
    (he : e ≤ 1 / (8 * (d : ℝ) ^ 2))
    (hdiv : (divisorCount n : ℝ) ≤ (n : ℝ) ^ e) :
    (divisorCount n : ℝ) ^ d ≤ (N : ℝ) ^ (1 / 8 : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    (divisorCount n : ℝ) ^ d ≤ ((n : ℝ) ^ e) ^ d :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hdiv d
    _ = (n : ℝ) ^ (e * d) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    _ ≤ (n : ℝ) ^ (1 / (8 * (d : ℝ))) := by
      refine Real.rpow_le_rpow_of_exponent_le hnR ?_
      calc
        e * (d : ℝ) ≤ (1 / (8 * (d : ℝ) ^ 2)) * d := by gcongr
        _ = 1 / (8 * d) := by
          have hdR : (0 : ℝ) < d := by exact_mod_cast hd
          field_simp
    _ ≤ ((N ^ d : ℕ) : ℝ) ^ (1 / (8 * (d : ℝ))) := by
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnN) (by positivity)
    _ = (((N : ℝ) ^ d) ^ (1 / (8 * (d : ℝ))) : ℝ) := by
      rw [Nat.cast_pow]
    _ = (N : ℝ) ^ ((d : ℝ) * (1 / (8 * (d : ℝ)))) := by
      rw [Real.rpow_mul (by positivity), Real.rpow_natCast]
    _ = (N : ℝ) ^ (1 / 8 : ℝ) := by
      congr 1
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      field_simp

/-- Uniform subpower estimate on a polynomial box.  This form handles small
values of the argument by absorbing their finite maximum into the threshold
for `N`. -/
theorem exists_uniform_divisorCount_power_le_eighth (d : ℕ) (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n : ℕ, 1 ≤ n → n ≤ N ^ d →
      (divisorCount n : ℝ) ^ d ≤ (N : ℝ) ^ (1 / 8 : ℝ) := by
  let e : ℝ := 1 / (8 * (d : ℝ) ^ 2)
  have he : 0 < e := by
    dsimp [e]
    positivity
  obtain ⟨M, hM⟩ := exists_divisorCount_le_rpow e he
  have htend : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (1 / 8 : ℝ)) atTop atTop := by
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨M₃, hM₃⟩ := eventually_atTop.1
    ((tendsto_atTop.1 htend) ((M : ℝ) ^ d))
  refine ⟨max 1 M₃, ?_⟩
  intro N hN n hn hnN
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  by_cases hnM : M ≤ n
  · apply divisorCount_power_le_eighth_of_exponent d n N hd hn hN1 hnN
      e le_rfl
    exact hM n hnM
  · have hnlt : n < M := Nat.lt_of_not_ge hnM
    have hcard : divisorCount n < M :=
      lt_of_le_of_lt (Nat.card_divisors_le_self n) hnlt
    have hpow : (divisorCount n : ℝ) ^ d ≤ (M : ℝ) ^ d := by
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hcard.le) d
    exact hpow.trans (hM₃ N (le_trans (le_max_right 1 M₃) hN))

/-- Uniform maximal-order estimate for the number of distinct prime factors
in the range needed for Beker's argument. -/
theorem eventually_distinctPrimeFactorCount_lt_four_log_div_loglog :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m → m < n ^ 2 →
      (distinctPrimeFactorCount m : ℝ) <
        4 * Real.log n / Real.log (Real.log n) := by
  simpa [distinctPrimeFactorCount] using
    Erdos285.Dispersion.eventually_primeFactors_card_lt_four_log_div_loglog

/-- Direct eventual form of the standard maximal-order bound for `ω`. -/
theorem eventually_distinctPrimeFactorCount_lt_four_log_div_loglog_self :
    ∀ᶠ n : ℕ in atTop,
      (distinctPrimeFactorCount n : ℝ) <
        4 * Real.log n / Real.log (Real.log n) := by
  filter_upwards
    [eventually_distinctPrimeFactorCount_lt_four_log_div_loglog,
      eventually_ge_atTop (2 : ℕ)] with n hn hn2
  exact hn n (by omega) (by nlinarith)

private lemma primePower_divisorSum_ratio_le (p a : ℕ) (hp : p.Prime) :
    ((∑ i ∈ Finset.range (a + 1), (p : ℝ) ^ i) / (p : ℝ) ^ a) ≤
      (1 - 1 / (p : ℝ))⁻¹ := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpOne : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  have hpSub : 0 < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hp.one_lt)
  rw [geom_sum_eq hpOne]
  field_simp [hpR.ne', hpSub.ne']
  simpa [pow_succ, mul_comm] using
    (sub_le_self ((p : ℝ) ^ (a + 1)) (show (0 : ℝ) ≤ 1 by norm_num))

/-- The abundancy index is bounded by the finite Euler product over the
distinct prime divisors. -/
theorem divisorSum_ratio_le_eulerProduct (n : ℕ) (hn : n ≠ 0) :
    (divisorSum n : ℝ) / (n : ℝ) ≤
      ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ))⁻¹ := by
  have hnprod : (n : ℝ) =
      ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hn
  rw [divisorSum,
    ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn,
    hnprod]
  push_cast
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    simpa using primePower_divisorSum_ratio_le p (n.factorization p)
      (Nat.prime_of_mem_primeFactors hp)

private lemma eulerFactor_le_one_add (p : ℕ) (hp : p.Prime) :
    (1 - 1 / (p : ℝ))⁻¹ ≤ 1 + 2 / (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpSub : 0 < (p : ℝ) - 1 := by linarith
  field_simp [hpR.ne', hpSub.ne']
  nlinarith

private lemma two_pow_primeFactors_card_le (n : ℕ) (hn : 0 < n) :
    2 ^ n.primeFactors.card ≤ n := by
  calc
    2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
      apply Finset.pow_card_le_prod
      intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)

/-- Prime factors larger than `log n` contribute only an absolute constant
to the Euler product. -/
private lemma largePrimeEulerProduct_le_exp_four (n : ℕ) (hn : 0 < n)
    (hlogn : 0 < Real.log n) :
    (∏ p ∈ n.primeFactors.filter (fun p : ℕ ↦ Real.log n < (p : ℝ)),
      (1 - 1 / (p : ℝ))⁻¹) ≤ Real.exp 4 := by
  let H : Finset ℕ :=
    n.primeFactors.filter (fun p : ℕ ↦ Real.log n < (p : ℝ))
  have hcardlog : (H.card : ℝ) * Real.log 2 ≤ Real.log n := by
    have hpow := two_pow_primeFactors_card_le n hn
    have hcast : ((2 ^ n.primeFactors.card : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hpow
    have hlog := Real.log_le_log
      (show (0 : ℝ) < ((2 ^ n.primeFactors.card : ℕ) : ℝ) by positivity) hcast
    have hcastpow : ((2 ^ n.primeFactors.card : ℕ) : ℝ) =
        (2 : ℝ) ^ n.primeFactors.card := by norm_num
    rw [hcastpow, Real.log_pow] at hlog
    have hHcard : H.card ≤ n.primeFactors.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hlogtwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hHcard) hlogtwo).trans hlog
  have hsum : (∑ p ∈ H, 2 / (p : ℝ)) ≤ 4 := by
    calc
      (∑ p ∈ H, 2 / (p : ℝ)) ≤ H.card • (2 / Real.log n : ℝ) := by
        apply Finset.sum_le_card_nsmul
        intro p hp
        have hpgt : Real.log n < (p : ℝ) := (Finset.mem_filter.mp hp).2
        exact div_le_div_of_nonneg_left (by norm_num) hlogn hpgt.le
      _ = (H.card : ℝ) * (2 / Real.log n) := by simp [nsmul_eq_mul]
      _ ≤ 4 := by
        rw [show (H.card : ℝ) * (2 / Real.log n) =
          ((H.card : ℝ) * 2) / Real.log n by ring]
        rw [div_le_iff₀ hlogn]
        have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hscaled := mul_le_mul_of_nonneg_left hcardlog
          (show (0 : ℝ) ≤ 2 / Real.log 2 by positivity)
        field_simp [hlogtwo.ne'] at hscaled
        nlinarith [Real.log_two_gt_d9]
  change (∏ p ∈ H, (1 - 1 / (p : ℝ))⁻¹) ≤ Real.exp 4
  calc
    (∏ p ∈ H, (1 - 1 / (p : ℝ))⁻¹) ≤
        ∏ p ∈ H, (1 + 2 / (p : ℝ)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hpPrime := Nat.prime_of_mem_primeFactors (Finset.filter_subset _ _ hp)
        exact (inv_pos.mpr (sub_pos.mpr (by
          have hpR : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
          rw [div_lt_iff₀ (lt_trans zero_lt_one hpR)]
          simpa using hpR))).le
      · intro p hp
        exact eulerFactor_le_one_add p
          (Nat.prime_of_mem_primeFactors (Finset.filter_subset _ _ hp))
    _ ≤ Real.exp (∑ p ∈ H, 2 / (p : ℝ)) := by
      exact Real.prod_one_add_le_exp_sum H (fun p ↦ by positivity)
    _ ≤ Real.exp 4 := Real.exp_le_exp.mpr hsum

/-- The Euler factors at primes at most `log n` form a subproduct of the
usual partial Euler product. -/
private lemma smallPrimeEulerProduct_le_partial (n : ℕ) :
    (∏ p ∈ n.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ Real.log n),
      (1 - 1 / (p : ℝ))⁻¹) ≤ partial_euler_product ⌊Real.log n⌋₊ := by
  let L : Finset ℕ :=
    n.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ Real.log n)
  let P : Finset ℕ := (Finset.Icc 1 ⌊Real.log n⌋₊).filter Nat.Prime
  have hLP : L ⊆ P := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩,
      Nat.prime_of_mem_primeFactors hp'.1⟩
    · exact Nat.pos_of_mem_primeFactors hp'.1
    · exact Nat.le_floor hp'.2
  change (∏ p ∈ L, (1 - 1 / (p : ℝ))⁻¹) ≤ _
  rw [partial_euler_product]
  simp only [one_div]
  change (∏ p ∈ L, (1 - (p : ℝ)⁻¹)⁻¹) ≤
    ∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹
  apply Finset.prod_le_prod_of_subset_of_one_le hLP
  · intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors (Finset.filter_subset _ _ hp)
    have hpgt : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
    exact (inv_pos.mpr (sub_pos.mpr (by
      rw [inv_lt_one₀ (lt_trans zero_lt_one hpgt)]
      exact hpgt))).le
  · intro p hpP hpL
    have hpPrime : p.Prime := (Finset.mem_filter.mp hpP).2
    have hpgt : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
    have hdenpos : 0 < 1 - (p : ℝ)⁻¹ := sub_pos.mpr (by
      rw [inv_lt_one₀ (lt_trans zero_lt_one hpgt)]
      exact hpgt)
    exact (one_le_inv₀ hdenpos).mpr
      (sub_le_self 1 (inv_nonneg.mpr (by positivity)))

/-- Explicit pointwise abundancy bound.  The only hypothesis is that `n` is
large enough for `log n` to lie in the range of the partial Mertens bound. -/
theorem divisorSum_ratio_le_loglog_of_mertens (c : ℝ) (hc : 0 < c)
    (hM : ∀ x : ℝ, 2 ≤ x →
      ‖partial_euler_product ⌊x⌋₊‖ ≤ c * ‖Real.log x‖)
    (n : ℕ) (hnlog : 2 ≤ Real.log n) :
    (divisorSum n : ℝ) / (n : ℝ) ≤
      (c * Real.exp 4) * Real.log (Real.log n) := by
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    norm_num at hnlog
  have hlogn : 0 < Real.log n := lt_of_lt_of_le (by norm_num) hnlog
  have hloglogn : 0 ≤ Real.log (Real.log n) :=
    Real.log_nonneg (le_trans (by norm_num) hnlog)
  let low : Finset ℕ :=
    n.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ Real.log n)
  let high : Finset ℕ :=
    n.primeFactors.filter (fun p : ℕ ↦ Real.log n < (p : ℝ))
  have hlow : (∏ p ∈ low, (1 - 1 / (p : ℝ))⁻¹) ≤
      c * Real.log (Real.log n) := by
    have hsmall := smallPrimeEulerProduct_le_partial n
    change (∏ p ∈ low, (1 - 1 / (p : ℝ))⁻¹) ≤
      partial_euler_product ⌊Real.log n⌋₊ at hsmall
    have hm := hM (Real.log n) hnlog
    rw [norm_of_nonneg (le_trans zero_le_one partial_euler_trivial_lower_bound),
      norm_of_nonneg hloglogn] at hm
    exact hsmall.trans hm
  have hhigh : (∏ p ∈ high, (1 - 1 / (p : ℝ))⁻¹) ≤ Real.exp 4 := by
    exact largePrimeEulerProduct_le_exp_four n hn hlogn
  have hfilter :
      n.primeFactors.filter (fun p : ℕ ↦ ¬ (p : ℝ) ≤ Real.log n) = high := by
    ext p
    simp [high, not_le]
  have hsplit :
      (∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ))⁻¹) =
        (∏ p ∈ low, (1 - 1 / (p : ℝ))⁻¹) *
        ∏ p ∈ high, (1 - 1 / (p : ℝ))⁻¹ := by
    calc
      (∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ))⁻¹) =
          (∏ p ∈ n.primeFactors.filter
              (fun p : ℕ ↦ (p : ℝ) ≤ Real.log n),
              (1 - 1 / (p : ℝ))⁻¹) *
            ∏ p ∈ n.primeFactors.filter
              (fun p : ℕ ↦ ¬ (p : ℝ) ≤ Real.log n),
              (1 - 1 / (p : ℝ))⁻¹ := by
            exact (Finset.prod_filter_mul_prod_filter_not n.primeFactors
              (fun p : ℕ ↦ (p : ℝ) ≤ Real.log n)
              (fun p : ℕ ↦ (1 - 1 / (p : ℝ))⁻¹)).symm
      _ = (∏ p ∈ low, (1 - 1 / (p : ℝ))⁻¹) *
            ∏ p ∈ high, (1 - 1 / (p : ℝ))⁻¹ := by
          rw [hfilter]
  refine (divisorSum_ratio_le_eulerProduct n hn.ne').trans ?_
  rw [hsplit]
  calc
    (∏ p ∈ low, (1 - 1 / (p : ℝ))⁻¹) *
          ∏ p ∈ high, (1 - 1 / (p : ℝ))⁻¹ ≤
        (c * Real.log (Real.log n)) * Real.exp 4 := by
      apply mul_le_mul hlow hhigh
      · exact Finset.prod_nonneg fun p hp ↦ by
          have hpPrime := Nat.prime_of_mem_primeFactors (Finset.filter_subset _ _ hp)
          have hpgt : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
          exact (inv_pos.mpr (sub_pos.mpr (by
            rw [div_lt_iff₀ (lt_trans zero_lt_one hpgt)]
            simpa using hpgt))).le
      · exact mul_nonneg hc.le hloglogn
    _ = (c * Real.exp 4) * Real.log (Real.log n) := by ring

/-- The standard uniform bound `σ(n)/n ≪ log log n`, in a fully quantified
form suitable for eventual estimates. -/
theorem eventually_divisorSum_ratio_le_const_mul_loglog :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (divisorSum n : ℝ) / (n : ℝ) ≤ C * Real.log (Real.log n) := by
  obtain ⟨c, hc, hM⟩ := weak_mertens_third_upper_all
  refine ⟨c * Real.exp 4, mul_pos hc (Real.exp_pos 4), ?_⟩
  filter_upwards
    [tendsto_log_coe_at_top.eventually (eventually_ge_atTop (2 : ℝ))] with n hn
  exact divisorSum_ratio_le_loglog_of_mertens c hc hM n hn

/-- Threshold version of the abundancy bound. -/
theorem exists_divisorSum_ratio_le_const_mul_loglog :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (divisorSum n : ℝ) / (n : ℝ) ≤ C * Real.log (Real.log n) := by
  obtain ⟨C, hC, h⟩ := eventually_divisorSum_ratio_le_const_mul_loglog
  rw [eventually_atTop] at h
  exact ⟨C, hC, h⟩

end

end Erdos1161
