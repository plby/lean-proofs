import ErdosProblems.Erdos469
import PrimeNumberTheoremAnd.Consequences
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Coarse prime estimates for Erdős Problem 888

This file packages the elementary analytic number theory used by the dyadic
argument.  The estimates deliberately use the regularized logarithm
`lambda x = log (e * x)`: on positive inputs this is `1 + log x`, so it stays
positive down to `x = 1` while remaining equivalent to `log x` at infinity.
-/

open Filter Finset Real Set MeasureTheory Asymptotics
open scoped BigOperators Topology Chebyshev

namespace Erdos888

noncomputable section

/-- The regularized logarithm used throughout the dyadic estimates. -/
def lambda (x : ℝ) : ℝ :=
  Real.log (Real.exp 1 * x)

lemma lambda_eq_one_add_log {x : ℝ} (hx : x ≠ 0) :
    lambda x = 1 + Real.log x := by
  rw [lambda, Real.log_mul (Real.exp_ne_zero 1) hx, Real.log_exp]

lemma lambda_pos {x : ℝ} (hx : 1 ≤ x) : 0 < lambda x := by
  rw [lambda_eq_one_add_log (by linarith)]
  have := Real.log_nonneg hx
  linarith

lemma lambda_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    lambda x ≤ lambda y := by
  rw [lambda_eq_one_add_log hx.ne']
  rw [lambda_eq_one_add_log (hx.trans_le hxy).ne']
  simpa [add_comm] using add_le_add_left (Real.log_le_log hx hxy) 1

/-- The finite set of primes at most `n`. -/
def primesUpTo (n : ℕ) : Finset ℕ :=
  Nat.primesLE n

@[simp] lemma mem_primesUpTo {p n : ℕ} :
    p ∈ primesUpTo n ↔ p.Prime ∧ p ≤ n := by
  rw [primesUpTo, Nat.mem_primesLE]
  tauto

@[simp] lemma card_primesUpTo (n : ℕ) :
    (primesUpTo n).card = Nat.primeCounting n := by
  exact Nat.primesLE_card_eq_primeCounting n

/-- Primes in the dyadic interval `(X, 2X]`. -/
def dyadicPrimes (X : ℕ) : Finset ℕ :=
  (primesUpTo (2 * X)).filter fun p ↦ X < p

@[simp] lemma mem_dyadicPrimes {p X : ℕ} :
    p ∈ dyadicPrimes X ↔ p.Prime ∧ X < p ∧ p ≤ 2 * X := by
  simp only [dyadicPrimes, mem_filter, mem_primesUpTo]
  tauto

/-- On natural inputs, replacing `log` by `lambda` changes the standard
prime-counting scale by at most an absolute constant. -/
lemma nat_div_log_isBigO_nat_div_lambda :
    (fun n : ℕ ↦ (n : ℝ) / Real.log (n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) / lambda (n : ℝ)) := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hlogOne : 1 ≤ Real.log (n : ℝ) := by
    rw [Real.le_log_iff_exp_le hnpos]
    exact Real.exp_one_lt_three.le.trans hnR
  have hlambda : 0 < lambda (n : ℝ) := lambda_pos (by linarith)
  have hlambda_le : lambda (n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    rw [lambda_eq_one_add_log hnpos.ne']
    linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity) hlog.le),
    abs_of_nonneg (div_nonneg (by positivity) hlambda.le)]
  have hinv : (1 : ℝ) / Real.log (n : ℝ) ≤ 2 / lambda (n : ℝ) := by
    rw [div_le_div_iff₀ hlog hlambda]
    simpa using hlambda_le
  calc
    (n : ℝ) / Real.log (n : ℝ) = (n : ℝ) * (1 / Real.log (n : ℝ)) := by
      ring
    _ ≤ (n : ℝ) * (2 / lambda (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 2 * ((n : ℝ) / lambda (n : ℝ)) := by ring

/-- The prime-counting function has the uniform coarse scale needed in all
dyadic blocks. -/
theorem primeCounting_isBigO_scale :
    (fun n : ℕ ↦ (Nat.primeCounting n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) / lambda (n : ℝ)) := by
  have hpi := pi_alt'.isBigO.comp_tendsto tendsto_natCast_atTop_atTop
  have hpiNat :
      (fun n : ℕ ↦ (Nat.primeCounting n : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) / Real.log (n : ℝ)) := by
    simpa only [Function.comp_def, Nat.floor_natCast] using hpi
  exact hpiNat.trans nat_div_log_isBigO_nat_div_lambda

private lemma primeCounting_le_self_aux (n : ℕ) : Nat.primeCounting n ≤ n := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  calc
    n.primesLE.card ≤ (Finset.Icc 1 n).card := by
      apply Finset.card_le_card
      intro p hp
      have hp' := Nat.mem_primesLE.mp hp
      exact Finset.mem_Icc.mpr ⟨hp'.2.one_le, hp'.1⟩
    _ = n := by simp

/-- A single positive constant controls the prime-counting estimate at every
natural input, including the finite prefix hidden by `IsBigO`. -/
theorem exists_forall_primeCounting_le_scale :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (Nat.primeCounting n : ℝ) ≤ C * ((n : ℝ) / lambda (n : ℝ)) := by
  obtain ⟨C, hC⟩ := primeCounting_isBigO_scale.bound
  obtain ⟨N, hN⟩ := eventually_atTop.1 hC
  let N₀ : ℕ := max N 1
  let C₀ : ℝ := max 1 (max |C| (lambda (N₀ : ℝ)))
  refine ⟨C₀, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun n ↦ ?_⟩
  obtain rfl | hnpos := n.eq_zero_or_pos
  · simp [lambda]
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have hlamn : 0 < lambda (n : ℝ) := lambda_pos hnOne
  have hscale : 0 ≤ (n : ℝ) / lambda (n : ℝ) := by positivity
  by_cases hnN : N₀ ≤ n
  · have hb := hN n ((le_max_left N 1).trans hnN)
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ (Nat.primeCounting n : ℝ)),
      Real.norm_of_nonneg hscale] at hb
    calc
      (Nat.primeCounting n : ℝ) ≤ C * ((n : ℝ) / lambda (n : ℝ)) := hb
      _ ≤ |C| * ((n : ℝ) / lambda (n : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hscale
      _ ≤ C₀ * ((n : ℝ) / lambda (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ hscale
        exact (le_max_left |C| (lambda (N₀ : ℝ))).trans (le_max_right 1 _)
  · have hnN₀ : n ≤ N₀ := by omega
    have hN₀One : (1 : ℝ) ≤ N₀ := by
      exact_mod_cast (show 1 ≤ N₀ by simp [N₀])
    have hlamN₀ : lambda (n : ℝ) ≤ lambda (N₀ : ℝ) := by
      apply lambda_mono (by positivity)
      exact_mod_cast hnN₀
    have hpi : (Nat.primeCounting n : ℝ) ≤ n := by
      exact_mod_cast primeCounting_le_self_aux n
    calc
      (Nat.primeCounting n : ℝ) ≤ n := hpi
      _ = lambda (n : ℝ) * ((n : ℝ) / lambda (n : ℝ)) := by
        field_simp
      _ ≤ lambda (N₀ : ℝ) * ((n : ℝ) / lambda (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hlamN₀ hscale
      _ ≤ C₀ * ((n : ℝ) / lambda (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ hscale
        exact (le_max_right |C| (lambda (N₀ : ℝ))).trans (le_max_right 1 _)

/-- The number of primes in `(X,2X]` is `O(X / lambda X)`. -/
theorem dyadicPrimeCount_isBigO_scale :
    (fun X : ℕ ↦ ((dyadicPrimes X).card : ℝ)) =O[atTop]
      (fun X : ℕ ↦ (X : ℝ) / lambda (X : ℝ)) := by
  obtain ⟨C, hC⟩ := primeCounting_isBigO_scale.bound
  refine IsBigO.of_bound (2 * |C|) ?_
  have hCnonneg : 0 ≤ |C| := abs_nonneg C
  have htendsto : Tendsto (fun X : ℕ ↦ 2 * X) atTop atTop := by
    refine tendsto_atTop.2 fun b ↦ ?_
    filter_upwards [eventually_ge_atTop b] with X hX
    omega
  have hCtwo := htendsto.eventually hC
  filter_upwards [hCtwo, eventually_ge_atTop 3] with X hbound hX
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hXR
  have h2Xpos : (0 : ℝ) < (2 * X : ℕ) := by positivity
  have hlamX : 0 < lambda (X : ℝ) := lambda_pos hXR
  have hlam2X : 0 < lambda ((2 * X : ℕ) : ℝ) :=
    lambda_pos (by exact_mod_cast (show 1 ≤ 2 * X by omega))
  have hlamMono : lambda (X : ℝ) ≤ lambda ((2 * X : ℕ) : ℝ) := by
    apply lambda_mono hXpos
    exact_mod_cast (show X ≤ 2 * X by omega)
  have hcard : ((dyadicPrimes X).card : ℝ) ≤ Nat.primeCounting (2 * X) := by
    have hcardNat : (dyadicPrimes X).card ≤ (primesUpTo (2 * X)).card := by
      exact Finset.card_filter_le _ _
    rw [card_primesUpTo] at hcardNat
    exact_mod_cast hcardNat
  have hscale : ((2 * X : ℕ) : ℝ) / lambda ((2 * X : ℕ) : ℝ) ≤
      2 * ((X : ℝ) / lambda (X : ℝ)) := by
    calc
      ((2 * X : ℕ) : ℝ) / lambda ((2 * X : ℕ) : ℝ) ≤
          ((2 * X : ℕ) : ℝ) / lambda (X : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hlamX hlamMono
      _ = 2 * ((X : ℝ) / lambda (X : ℝ)) := by
        norm_num
        ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ ((dyadicPrimes X).card : ℝ)),
    abs_of_nonneg (div_nonneg (by positivity) hlamX.le)]
  calc
    ((dyadicPrimes X).card : ℝ) ≤ Nat.primeCounting (2 * X) := hcard
    _ ≤ |(Nat.primeCounting (2 * X) : ℝ)| := le_abs_self _
    _ ≤ C * |(((2 * X : ℕ) : ℝ) / lambda ((2 * X : ℕ) : ℝ))| := hbound
    _ ≤ |C| * (((2 * X : ℕ) : ℝ) / lambda ((2 * X : ℕ) : ℝ)) := by
      rw [abs_of_nonneg (div_nonneg (by positivity) hlam2X.le)]
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (2 * ((X : ℝ) / lambda (X : ℝ))) :=
      mul_le_mul_of_nonneg_left hscale hCnonneg
    _ = (2 * |C|) * ((X : ℝ) / lambda (X : ℝ)) := by ring

/-- The dyadic prime-count estimate with one constant valid at every natural
scale (rather than only eventually). -/
theorem exists_forall_dyadicPrimeCount_le_scale :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
      ((dyadicPrimes X).card : ℝ) ≤ C * ((X : ℝ) / lambda (X : ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := exists_forall_primeCounting_le_scale
  refine ⟨2 * C, mul_pos (by norm_num) hCpos, fun X ↦ ?_⟩
  obtain rfl | hXpos := X.eq_zero_or_pos
  · simp [dyadicPrimes, primesUpTo, lambda]
  have hXOne : (1 : ℝ) ≤ X := by exact_mod_cast hXpos
  have hlamX : 0 < lambda (X : ℝ) := lambda_pos hXOne
  have hlam2X : 0 < lambda ((2 * X : ℕ) : ℝ) :=
    lambda_pos (by exact_mod_cast (show 1 ≤ 2 * X by omega))
  have hlamMono : lambda (X : ℝ) ≤ lambda ((2 * X : ℕ) : ℝ) := by
    apply lambda_mono (by positivity)
    exact_mod_cast (show X ≤ 2 * X by omega)
  have hcard : ((dyadicPrimes X).card : ℝ) ≤ Nat.primeCounting (2 * X) := by
    have hcardNat : (dyadicPrimes X).card ≤ (primesUpTo (2 * X)).card := by
      exact Finset.card_filter_le _ _
    rw [card_primesUpTo] at hcardNat
    exact_mod_cast hcardNat
  calc
    ((dyadicPrimes X).card : ℝ) ≤ Nat.primeCounting (2 * X) := hcard
    _ ≤ C * (((2 * X : ℕ) : ℝ) / lambda ((2 * X : ℕ) : ℝ)) := hC _
    _ ≤ C * (((2 * X : ℕ) : ℝ) / lambda (X : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hCpos.le
      exact div_le_div_of_nonneg_left (by positivity) hlamX hlamMono
    _ = (2 * C) * ((X : ℝ) / lambda (X : ℝ)) := by
      norm_num
      ring

/-- The real primorial through `n`. -/
def primePrimorial (n : ℕ) : ℝ :=
  ∏ p ∈ primesUpTo n, (p : ℝ)

lemma primePrimorial_eq_exp_theta (n : ℕ) :
    primePrimorial n = Real.exp (Chebyshev.theta (n : ℝ)) := by
  rw [primePrimorial, Chebyshev.theta_eq_sum_primesLE_log, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Real.exp_log]
  exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos

/-- A coarse Chebyshev/primorial estimate: the product of the primes through
`n` is eventually bounded by `exp (C n)` for one positive absolute `C`. -/
theorem eventually_primePrimorial_le_exp :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      primePrimorial n ≤ Real.exp (C * n) := by
  have htheta := chebyshev_asymptotic.isBigO.comp_tendsto tendsto_natCast_atTop_atTop
  obtain ⟨C, hC⟩ := htheta.bound
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left 1 C), ?_⟩
  filter_upwards [hC] with n hn
  have hthetaNonneg : 0 ≤ Chebyshev.theta (n : ℝ) := Chebyshev.theta_nonneg _
  have hnNonneg : (0 : ℝ) ≤ n := by positivity
  have hthetaBound : Chebyshev.theta (n : ℝ) ≤ max 1 C * n := by
    have habs : ‖Chebyshev.theta (n : ℝ)‖ ≤ C * ‖(n : ℝ)‖ := by
      simpa only [Function.comp_apply, id_eq] using hn
    calc
      Chebyshev.theta (n : ℝ) ≤ ‖Chebyshev.theta (n : ℝ)‖ := Real.le_norm_self _
      _ ≤ C * ‖(n : ℝ)‖ := habs
      _ = C * n := by rw [Real.norm_of_nonneg hnNonneg]
      _ ≤ max 1 C * n := mul_le_mul_of_nonneg_right (le_max_right 1 C) hnNonneg
  rw [primePrimorial_eq_exp_theta]
  exact Real.exp_le_exp.mpr hthetaBound

/-- The Euler product `∏_{p≤n}(1+1/p)`. -/
def primeEulerProduct (n : ℕ) : ℝ :=
  ∏ p ∈ primesUpTo n, (1 + (p : ℝ)⁻¹)

lemma primesUpTo_eq_primesThrough (n : ℕ) :
    primesUpTo n = Erdos469.primesThrough n := by
  ext p
  simp only [mem_primesUpTo, Erdos469.mem_primesThrough]

/-- The coarse Mertens upper estimate required by the divisor expansion. -/
theorem primeEulerProduct_le {n : ℕ} (hn : 2 ≤ n) :
    primeEulerProduct n ≤
      Real.exp Erdos469.reciprocalPrimeMertensConstant * Real.log (n : ℝ) := by
  have hmertens := Erdos469.abs_primeReciprocalSum_sub_logLog_le hn
  have hsum :
      (∑ p ∈ primesUpTo n, (p : ℝ)⁻¹) ≤
        Real.log (Real.log (n : ℝ)) + Erdos469.reciprocalPrimeMertensConstant := by
    rw [primesUpTo_eq_primesThrough]
    rw [← Erdos469.primeReciprocalSum]
    linarith [le_abs_self
      (Erdos469.primeReciprocalSum n - Real.log (Real.log (n : ℝ)))]
  have hlog : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  calc
    primeEulerProduct n ≤
        Real.exp (∑ p ∈ primesUpTo n, (p : ℝ)⁻¹) := by
      exact Real.prod_one_add_le_exp_sum _ fun p ↦ inv_nonneg.mpr (by positivity)
    _ ≤ Real.exp (Real.log (Real.log (n : ℝ)) +
        Erdos469.reciprocalPrimeMertensConstant) := Real.exp_le_exp.mpr hsum
    _ = Real.exp Erdos469.reciprocalPrimeMertensConstant * Real.log (n : ℝ) := by
      rw [Real.exp_add, Real.exp_log hlog]
      ring

/-- Mertens' product estimate in the `IsBigO` form used by asymptotic
assembly. -/
theorem primeEulerProduct_isBigO_log :
    primeEulerProduct =O[atTop] (fun n : ℕ ↦ Real.log (n : ℝ)) := by
  refine IsBigO.of_bound (Real.exp Erdos469.reciprocalPrimeMertensConstant) ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hprod : 0 ≤ primeEulerProduct n := by
    unfold primeEulerProduct
    positivity
  have hlog : 0 ≤ Real.log (n : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n by omega)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hprod, abs_of_nonneg hlog] using
    primeEulerProduct_le hn

/-- The weighted prime sum appearing in the Rankin bound. -/
def primeThreeQuarterSum (n : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo n, (p : ℝ) ^ (-(3 / 4 : ℝ))

private noncomputable def primeLogThreeQuarterSum (n : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo n,
    Real.log (p : ℝ) * (p : ℝ) ^ (-(3 / 4 : ℝ))

private lemma sum_range_succ_rpow_neg_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) ^ (-a)) ≤
      1 + ((N : ℝ) ^ (1 - a) - 1) / (1 - a) := by
  let f : ℝ → ℝ := fun x ↦ x ^ (-a)
  have hf : AntitoneOn f (Icc ((1 : ℕ) : ℝ) (N : ℝ)) := by
    exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (neg_nonpos.mpr ha0)).mono
      (by
        intro x hx
        norm_num at hx ⊢
        exact zero_lt_one.trans_le hx.1)
  have htail := AntitoneOn.sum_le_integral_Ico (f := f) hN hf
  have hsum :
      (∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) ^ (-a)) =
        1 + ∑ j ∈ Finset.Ico 1 N, ((j + 1 : ℕ) : ℝ) ^ (-a) := by
    obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    rw [Finset.sum_range_succ', Finset.sum_Ico_eq_sum_range]
    rw [add_comm]
    norm_num
    congr 1
    funext j
    congr 1
    ring
  rw [hsum]
  gcongr
  calc
    (∑ j ∈ Finset.Ico 1 N, ((j + 1 : ℕ) : ℝ) ^ (-a))
        ≤ ∫ x in (1 : ℝ)..(N : ℝ), x ^ (-a) := by simpa [f] using htail
    _ = ((N : ℝ) ^ (1 - a) - 1) / (1 - a) := by
      rw [integral_rpow]
      · norm_num
        ring_nf
      · left
        linarith

private lemma sum_Icc_rpow_neg_three_quarters_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ j ∈ Finset.Icc 1 N, (j : ℝ) ^ (-(3 / 4 : ℝ))) ≤
      4 * (N : ℝ) ^ (1 / 4 : ℝ) := by
  calc
    (∑ j ∈ Finset.Icc 1 N, (j : ℝ) ^ (-(3 / 4 : ℝ))) =
        ∑ j ∈ Finset.range N,
          ((j + 1 : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) := by
      rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      congr 2
      ring
    _ ≤ 1 + ((N : ℝ) ^ (1 - (3 / 4 : ℝ)) - 1) /
          (1 - (3 / 4 : ℝ)) :=
      sum_range_succ_rpow_neg_le (3 / 4 : ℝ) (by norm_num)
        (by norm_num) N hN
    _ ≤ 4 * (N : ℝ) ^ (1 / 4 : ℝ) := by
      have hp : 0 ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
        Real.rpow_nonneg (by positivity) _
      norm_num at hp ⊢
      linarith

private noncomputable def primeLogIndicator (m : ℕ) : ℝ :=
  if m.Prime then Real.log (m : ℝ) else 0

private lemma sum_primeLogIndicator_eq_theta (x : ℝ) :
    (∑ m ∈ Finset.Icc 0 ⌊x⌋₊, primeLogIndicator m) = Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_Icc]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  simp [primeLogIndicator]

private lemma primeLogThreeQuarterSum_eq (n : ℕ) :
    primeLogThreeQuarterSum n =
      (n : ℝ) ^ (-(3 / 4 : ℝ)) * Chebyshev.theta n +
        (3 / 4 : ℝ) *
          ∫ t in Set.Ioc 2 (n : ℝ),
            t ^ (-(7 / 4 : ℝ)) * Chebyshev.theta t := by
  let f : ℝ → ℝ := fun x ↦ x ^ (-(3 / 4 : ℝ))
  have hf_diff : ∀ t ∈ Set.Icc (2 : ℝ) n, DifferentiableAt ℝ f t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (Real.hasDerivAt_rpow_const (Or.inl ht0)).differentiableAt
  have hderiv : ∀ t ∈ Set.Icc (2 : ℝ) n,
      deriv f t = -(3 / 4 : ℝ) * t ^ (-(7 / 4 : ℝ)) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    rw [(Real.hasDerivAt_rpow_const (x := t) (p := -(3 / 4 : ℝ))
      (Or.inl ht0)).deriv]
    norm_num [f]
  have hcont : ContinuousOn (fun t : ℝ ↦
      -(3 / 4 : ℝ) * t ^ (-(7 / 4 : ℝ))) (Set.Icc 2 n) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact continuousWithinAt_const.mul
      (Real.continuousAt_rpow_const t (-(7 / 4 : ℝ))
        (Or.inl ht0)).continuousWithinAt
  have hf_int : IntegrableOn (deriv f) (Set.Icc (2 : ℝ) n) := by
    refine (hcont.integrableOn_Icc).congr_fun ?_ measurableSet_Icc
    intro t ht
    exact (hderiv t ht).symm
  have hab := sum_mul_eq_sub_integral_mul₁ primeLogIndicator (by simp [primeLogIndicator])
    (by simp [primeLogIndicator]) (n : ℝ) hf_diff hf_int
  rw [Nat.floor_natCast] at hab
  have hprimeSet : primesUpTo n = (Finset.Icc 0 n).filter Nat.Prime := by
    ext p
    simp only [mem_primesUpTo, Finset.mem_filter, Finset.mem_Icc,
      Nat.zero_le, true_and]
    tauto
  rw [show primeLogThreeQuarterSum n =
      ∑ k ∈ Finset.Icc 0 n, f k * primeLogIndicator k by
    unfold primeLogThreeQuarterSum
    rw [hprimeSet, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hp : k.Prime <;> simp [primeLogIndicator, f, hp, mul_comm]]
  rw [hab]
  have hsum_n : (∑ k ∈ Finset.Icc 0 n, primeLogIndicator k) =
      Chebyshev.theta n := by
    simpa using sum_primeLogIndicator_eq_theta (n : ℝ)
  rw [hsum_n]
  have hint :
      (∫ t in Set.Ioc 2 (n : ℝ),
          deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogIndicator k) =
        ∫ t in Set.Ioc 2 (n : ℝ),
          (-(3 / 4 : ℝ) * t ^ (-(7 / 4 : ℝ))) * Chebyshev.theta t := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    change deriv f t * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogIndicator k) =
      (-(3 / 4 : ℝ) * t ^ (-(7 / 4 : ℝ))) * Chebyshev.theta t
    rw [sum_primeLogIndicator_eq_theta, hderiv t]
    exact ⟨ht.1.le, ht.2⟩
  rw [hint]
  have hfun : (fun t : ℝ ↦
      (-(3 / 4 : ℝ) * t ^ (-(7 / 4 : ℝ))) * Chebyshev.theta t) =
      fun t ↦ -(3 / 4 : ℝ) *
        (t ^ (-(7 / 4 : ℝ)) * Chebyshev.theta t) := by
    funext t
    ring
  rw [hfun, MeasureTheory.integral_const_mul]
  dsimp [f]
  ring

private lemma primeLogThreeQuarterSum_le (n : ℕ) (hn : 2 ≤ n) :
    primeLogThreeQuarterSum n ≤
      4 * Real.log 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hpow : (n : ℝ) ^ (-(3 / 4 : ℝ)) * (n : ℝ) =
      (n : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      (n : ℝ) ^ (-(3 / 4 : ℝ)) * (n : ℝ) =
          (n : ℝ) ^ (-(3 / 4 : ℝ)) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ (-(3 / 4 : ℝ) + 1) :=
        (Real.rpow_add hnpos _ _).symm
      _ = (n : ℝ) ^ (1 / 4 : ℝ) := by norm_num
  have hfirst :
      (n : ℝ) ^ (-(3 / 4 : ℝ)) * Chebyshev.theta n ≤
        Real.log 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      (n : ℝ) ^ (-(3 / 4 : ℝ)) * Chebyshev.theta n ≤
          (n : ℝ) ^ (-(3 / 4 : ℝ)) * (Real.log 4 * (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x hnpos.le)
          (Real.rpow_nonneg hnpos.le _)
      _ = Real.log 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by rw [← hpow]; ring
  have hg_int : IntegrableOn (fun t : ℝ ↦ t ^ (-(7 / 4 : ℝ)))
      (Set.Icc 2 (n : ℝ)) := by
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (Real.continuousAt_rpow_const t (-(7 / 4 : ℝ))
      (Or.inl ht0)).continuousWithinAt
  have hleft_int : IntegrableOn (fun t : ℝ ↦
      t ^ (-(7 / 4 : ℝ)) * Chebyshev.theta t) (Set.Ioc 2 (n : ℝ)) := by
    have hraw := integrableOn_mul_sum_Icc (m := 0) primeLogIndicator zero_le_two hg_int
    have hcongr : IntegrableOn (fun t : ℝ ↦
        t ^ (-(7 / 4 : ℝ)) * Chebyshev.theta t) (Set.Icc 2 (n : ℝ)) := by
      refine hraw.congr_fun ?_ measurableSet_Icc
      intro t ht
      change t ^ (-(7 / 4 : ℝ)) *
        (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogIndicator k) =
          t ^ (-(7 / 4 : ℝ)) * Chebyshev.theta t
      rw [sum_primeLogIndicator_eq_theta]
    exact hcongr.mono_set Set.Ioc_subset_Icc_self
  have hright_int : IntegrableOn (fun t : ℝ ↦
      Real.log 4 * t ^ (-(3 / 4 : ℝ))) (Set.Ioc 2 (n : ℝ)) := by
    have hc : ContinuousOn (fun t : ℝ ↦
        Real.log 4 * t ^ (-(3 / 4 : ℝ))) (Set.Icc 2 (n : ℝ)) := by
      intro t ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      exact continuousWithinAt_const.mul
        (Real.continuousAt_rpow_const t (-(3 / 4 : ℝ))
          (Or.inl ht0)).continuousWithinAt
    exact hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hintegral :
      (∫ t in Set.Ioc 2 (n : ℝ),
          t ^ (-(7 / 4 : ℝ)) * Chebyshev.theta t) ≤
        ∫ t in Set.Ioc 2 (n : ℝ),
          Real.log 4 * t ^ (-(3 / 4 : ℝ)) := by
    apply MeasureTheory.setIntegral_mono_on hleft_int hright_int measurableSet_Ioc
    intro t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    calc
      t ^ (-(7 / 4 : ℝ)) * Chebyshev.theta t ≤
          t ^ (-(7 / 4 : ℝ)) * (Real.log 4 * t) := by
        exact mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x ht0)
          (Real.rpow_nonneg ht0 _)
      _ = Real.log 4 * t ^ (-(3 / 4 : ℝ)) := by
        have htpos : 0 < t := by linarith [ht.1]
        have hp : t ^ (-(7 / 4 : ℝ)) * t = t ^ (-(3 / 4 : ℝ)) := by
          calc
            t ^ (-(7 / 4 : ℝ)) * t = t ^ (-(7 / 4 : ℝ)) * t ^ (1 : ℝ) := by
              rw [Real.rpow_one]
            _ = t ^ (-(7 / 4 : ℝ) + 1) := (Real.rpow_add htpos _ _).symm
            _ = t ^ (-(3 / 4 : ℝ)) := by norm_num
        rw [← hp]
        ring
  have hrhs :
      (∫ t in Set.Ioc 2 (n : ℝ),
          Real.log 4 * t ^ (-(3 / 4 : ℝ))) =
        Real.log 4 *
          (((n : ℝ) ^ (1 / 4 : ℝ) - (2 : ℝ) ^ (1 / 4 : ℝ)) /
            (1 / 4 : ℝ)) := by
    rw [← intervalIntegral.integral_of_le hnR,
      intervalIntegral.integral_const_mul, integral_rpow]
    · norm_num
    · exact Or.inl (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have htwo : 0 ≤ (2 : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by norm_num) _
  rw [primeLogThreeQuarterSum_eq]
  calc
    (n : ℝ) ^ (-(3 / 4 : ℝ)) * Chebyshev.theta ↑n +
          3 / 4 * ∫ t in Set.Ioc 2 ↑n, t ^ (-(7 / 4 : ℝ)) * Chebyshev.theta t ≤
        Real.log 4 * (n : ℝ) ^ (1 / 4 : ℝ) +
          3 / 4 * ∫ t in Set.Ioc 2 ↑n,
            Real.log 4 * t ^ (-(3 / 4 : ℝ)) := by
      gcongr
    _ = Real.log 4 * (n : ℝ) ^ (1 / 4 : ℝ) +
          3 / 4 * (Real.log 4 *
            (((n : ℝ) ^ (1 / 4 : ℝ) - (2 : ℝ) ^ (1 / 4 : ℝ)) /
              (1 / 4 : ℝ))) := by rw [hrhs]
    _ ≤ 4 * Real.log 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by
      nlinarith [mul_nonneg hlog4 htwo]

private lemma primeThreeQuarterSum_le_aux (n : ℕ) (hn : 4 ≤ n) :
    primeThreeQuarterSum n ≤
      4 * (n : ℝ) ^ (1 / 8 : ℝ) +
        8 * Real.log 4 * (n : ℝ) ^ (1 / 4 : ℝ) / Real.log n := by
  let s := primesUpTo n
  let w : ℕ → ℝ := fun p ↦ (p : ℝ) ^ (-(3 / 4 : ℝ))
  let low : Finset ℕ := s.filter (fun p : ℕ ↦ (p : ℝ) ≤ Real.sqrt n)
  let high : Finset ℕ := s.filter (fun p : ℕ ↦ ¬(p : ℝ) ≤ Real.sqrt n)
  have hnpos : (0 : ℝ) < n := by positivity
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 4) hn))
  have hsqrt : (1 : ℝ) ≤ Real.sqrt n :=
    (Real.one_le_sqrt).2 (by exact_mod_cast (show 1 ≤ n by omega))
  have hfloor : 1 ≤ ⌊Real.sqrt n⌋₊ := Nat.le_floor (by simpa using hsqrt)
  have hlow : (∑ p ∈ low, w p) ≤ 4 * (n : ℝ) ^ (1 / 8 : ℝ) := by
    have hsub : low ⊆ Finset.Icc 1 ⌊Real.sqrt n⌋₊ := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpr : p.Prime := Nat.prime_of_mem_primesLE hp'.1
      exact Finset.mem_Icc.mpr ⟨hpr.one_le, Nat.le_floor hp'.2⟩
    calc
      (∑ p ∈ low, w p) ≤
          ∑ p ∈ Finset.Icc 1 ⌊Real.sqrt n⌋₊,
            (p : ℝ) ^ (-(3 / 4 : ℝ)) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun p _ _ ↦ Real.rpow_nonneg (by positivity) _)
      _ ≤ 4 * (⌊Real.sqrt n⌋₊ : ℝ) ^ (1 / 4 : ℝ) :=
        sum_Icc_rpow_neg_three_quarters_le _ hfloor
      _ ≤ 4 * (Real.sqrt n) ^ (1 / 4 : ℝ) := by
        gcongr
        exact Nat.floor_le (Real.sqrt_nonneg n)
      _ = 4 * (n : ℝ) ^ (1 / 8 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hnpos)]
        norm_num
  have hhigh_point (p : ℕ) (hp : p ∈ high) :
      w p ≤ (2 / Real.log n) * (Real.log p * w p) := by
    have hp' := Finset.mem_filter.mp hp
    have hpr : p.Prime := Nat.prime_of_mem_primesLE hp'.1
    have hpsqrt : Real.sqrt n < (p : ℝ) := lt_of_not_ge hp'.2
    have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
    have hlogp : Real.log (Real.sqrt n) ≤ Real.log p :=
      Real.log_le_log hsqrtpos hpsqrt.le
    have hhalf : Real.log (n : ℝ) / 2 ≤ Real.log p := by
      simpa [Real.log_sqrt hnpos.le] using hlogp
    have hw : 0 ≤ w p := Real.rpow_nonneg (by positivity) _
    have hfac : 1 ≤ (2 / Real.log n) * Real.log p := by
      rw [show (2 / Real.log n) * Real.log p =
        (2 * Real.log p) / Real.log n by ring, le_div_iff₀ hlogn]
      linarith
    calc
      w p = 1 * w p := by ring
      _ ≤ ((2 / Real.log n) * Real.log p) * w p :=
        mul_le_mul_of_nonneg_right hfac hw
      _ = (2 / Real.log n) * (Real.log p * w p) := by ring
  have hhigh : (∑ p ∈ high, w p) ≤
      8 * Real.log 4 * (n : ℝ) ^ (1 / 4 : ℝ) / Real.log n := by
    calc
      (∑ p ∈ high, w p) ≤
          ∑ p ∈ high, (2 / Real.log n) * (Real.log p * w p) := by
        exact Finset.sum_le_sum fun p hp ↦ hhigh_point p hp
      _ = (2 / Real.log n) *
          ∑ p ∈ high, (Real.log p * w p) := by rw [Finset.mul_sum]
      _ ≤ (2 / Real.log n) * primeLogThreeQuarterSum n := by
        apply mul_le_mul_of_nonneg_left
        · apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro p hp _
            exact mul_nonneg (Real.log_natCast_nonneg p)
              (Real.rpow_nonneg (by positivity) _)
        · exact div_nonneg (by norm_num) hlogn.le
      _ ≤ (2 / Real.log n) *
          (4 * Real.log 4 * (n : ℝ) ^ (1 / 4 : ℝ)) := by
        gcongr
        exact primeLogThreeQuarterSum_le n (by omega)
      _ = 8 * Real.log 4 * (n : ℝ) ^ (1 / 4 : ℝ) / Real.log n := by
        field_simp
        ring
  have hsplit : primeThreeQuarterSum n =
      (∑ p ∈ low, w p) + ∑ p ∈ high, w p := by
    unfold primeThreeQuarterSum low high s
    exact (Finset.sum_filter_add_sum_filter_not (primesUpTo n)
      (fun p ↦ (p : ℝ) ≤ Real.sqrt n)
      (fun p ↦ (p : ℝ) ^ (-(3 / 4 : ℝ)))).symm
  rw [hsplit]
  exact add_le_add hlow hhigh

private lemma primeThreeQuarterSum_nonneg (n : ℕ) :
    0 ≤ primeThreeQuarterSum n := by
  unfold primeThreeQuarterSum
  exact Finset.sum_nonneg fun p _ ↦ Real.rpow_nonneg (by positivity) _

theorem primeThreeQuarterSum_isBigO_scale :
    primeThreeQuarterSum =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (1 / 4 : ℝ) / lambda n) := by
  let C : ℝ := 36 + 16 * Real.log 4
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < n by omega))
  have hlogone : 1 ≤ Real.log (n : ℝ) := by
    rw [Real.le_log_iff_exp_le hnpos]
    have hfour : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hexp : Real.exp 1 < 3 := Real.exp_one_lt_three
    linarith
  have hlam : lambda (n : ℝ) = 1 + Real.log (n : ℝ) := by
    unfold lambda
    rw [Real.log_mul (Real.exp_ne_zero 1) hnpos.ne', Real.log_exp]
  have hlampos : 0 < lambda (n : ℝ) := by rw [hlam]; linarith
  have hp8pos : 0 < (n : ℝ) ^ (1 / 8 : ℝ) :=
    Real.rpow_pos_of_pos hnpos _
  have hp4pos : 0 < (n : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos hnpos _
  have hp8one : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 8 : ℝ) := by
    have := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hnone
      (by norm_num : (0 : ℝ) ≤ 1 / 8)
    simpa using this
  have hlogpow : Real.log (n : ℝ) ≤
      8 * (n : ℝ) ^ (1 / 8 : ℝ) := by
    have h := Real.log_natCast_le_rpow_div n
      (by norm_num : (0 : ℝ) < 1 / 8)
    norm_num at h ⊢
    linarith
  have hlampow : lambda (n : ℝ) ≤
      9 * (n : ℝ) ^ (1 / 8 : ℝ) := by
    rw [hlam]
    linarith
  have hlamlog : lambda (n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    rw [hlam]
    linarith
  have hp88 : (n : ℝ) ^ (1 / 8 : ℝ) * (n : ℝ) ^ (1 / 8 : ℝ) =
      (n : ℝ) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hnpos]
    norm_num
  have hlow : 4 * (n : ℝ) ^ (1 / 8 : ℝ) ≤
      36 * ((n : ℝ) ^ (1 / 4 : ℝ) / lambda n) := by
    rw [show 36 * ((n : ℝ) ^ (1 / 4 : ℝ) / lambda n) =
      (36 * (n : ℝ) ^ (1 / 4 : ℝ)) / lambda n by ring]
    rw [le_div_iff₀ hlampos]
    calc
      4 * (n : ℝ) ^ (1 / 8 : ℝ) * lambda n ≤
          4 * (n : ℝ) ^ (1 / 8 : ℝ) *
            (9 * (n : ℝ) ^ (1 / 8 : ℝ)) := by
        gcongr
      _ = 36 * (n : ℝ) ^ (1 / 4 : ℝ) := by rw [← hp88]; ring
  have hinv : (1 : ℝ) / Real.log n ≤ 2 / lambda n := by
    rw [div_le_div_iff₀ hlogn hlampos]
    simpa using hlamlog
  have hhigh : 8 * Real.log 4 * (n : ℝ) ^ (1 / 4 : ℝ) / Real.log n ≤
      (16 * Real.log 4) * ((n : ℝ) ^ (1 / 4 : ℝ) / lambda n) := by
    have hcoef : 0 ≤ 8 * Real.log 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by positivity
    calc
      8 * Real.log 4 * (n : ℝ) ^ (1 / 4 : ℝ) / Real.log n =
          (8 * Real.log 4 * (n : ℝ) ^ (1 / 4 : ℝ)) *
            (1 / Real.log n) := by ring
      _ ≤ (8 * Real.log 4 * (n : ℝ) ^ (1 / 4 : ℝ)) *
            (2 / lambda n) := mul_le_mul_of_nonneg_left hinv hcoef
      _ = (16 * Real.log 4) *
            ((n : ℝ) ^ (1 / 4 : ℝ) / lambda n) := by ring
  have hscale : 0 ≤ (n : ℝ) ^ (1 / 4 : ℝ) / lambda n :=
    (div_pos hp4pos hlampos).le
  rw [Real.norm_of_nonneg (primeThreeQuarterSum_nonneg n),
    Real.norm_of_nonneg hscale]
  calc
    primeThreeQuarterSum n ≤
        4 * (n : ℝ) ^ (1 / 8 : ℝ) +
          8 * Real.log 4 * (n : ℝ) ^ (1 / 4 : ℝ) / Real.log n :=
      primeThreeQuarterSum_le_aux n hn
    _ ≤ 36 * ((n : ℝ) ^ (1 / 4 : ℝ) / lambda n) +
        (16 * Real.log 4) * ((n : ℝ) ^ (1 / 4 : ℝ) / lambda n) :=
      add_le_add hlow hhigh
    _ = C * ((n : ℝ) ^ (1 / 4 : ℝ) / lambda n) := by
      unfold C
      ring

end

end Erdos888
