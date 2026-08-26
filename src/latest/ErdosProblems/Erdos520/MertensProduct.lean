import ErdosProblems.Erdos520.ExactEnergyMartingale
import ErdosProblems.Erdos520.ThinScheduleChebyshev
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory
open scoped BigOperators
open ArithmeticFunction

namespace Erdos
namespace Problem520

/-!
# Deterministic bounds for the exact Euler normalizer

The exact energy martingale is normalized by

`Z(y) = ∏_{p ≤ y} (1 + 1 / p)`.

This file records the unconditional comparison obtainable directly from the
Chebyshev theorem currently available in Mathlib.  It also isolates the one
coefficient-sharp estimate which is needed to improve the polylogarithmic
bound below to the Mertens-sized bound `Z(y) = O(log y)`.
-/

/-- The exact normalizer is bounded by the exponential of the reciprocal-prime
prefix sum. -/
theorem primeEnergyNormalizer_le_exp_primeReciprocalPrefix (y : ℕ) :
    primeEnergyNormalizer y ≤ Real.exp (primeReciprocalPrefix y) := by
  unfold primeEnergyNormalizer primeReciprocalPrefix
  exact Real.prod_one_add_le_exp_sum _ fun p => by positivity

/-- A useful endpoint form of the preceding exponential bound. -/
theorem primeEnergyNormalizer_le_mul_exp_freshReciprocalSum
    {a y : ℕ} (hay : a ≤ y) :
    primeEnergyNormalizer y ≤
      primeEnergyNormalizer a * Real.exp (freshReciprocalSum a y) := by
  rw [primeEnergyNormalizer_factor hay]
  apply mul_le_mul_of_nonneg_left _ (primeEnergyNormalizer_pos a).le
  unfold freshPrimeEnergyNormalizer
  simpa only [one_div, one_mul] using!
    eulerProduct_le_exp_freshReciprocalSum (t := (1 : ℝ)) zero_le_one a y

/-- Chebyshev's prime-counting upper bound gives an unconditional
polylogarithmic estimate for the exact normalizer.  The exponent `C` here is
an absolute positive constant (Mathlib supplies one slightly larger than
`log 4`). -/
theorem exists_primeEnergyNormalizer_polylog_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ N : ℕ, 2 ≤ N ∧
      ∀ y : ℕ, N ≤ y →
        primeEnergyNormalizer y ≤ D * (Real.log (y : ℝ)) ^ C := by
  obtain ⟨C, hC, N, hN, hP⟩ := exists_primeCountingUpperBound
  let D : ℝ := primeEnergyNormalizer N *
    Real.exp (|C * logLogNat N| + 2 * C / Real.log (N : ℝ))
  have hD : 0 < D := mul_pos (primeEnergyNormalizer_pos N) (Real.exp_pos _)
  refine ⟨C, D, hC, hD, N, hN, ?_⟩
  intro y hNy
  have hlogN : 0 < Real.log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogY : 0 < Real.log (y : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < y by omega)
  have hrecip :
      freshReciprocalSum N y ≤
        C * (logLogNat y - logLogNat N) +
          2 * C / Real.log (N : ℝ) :=
    freshReciprocalSum_le_of_primeCountingUpperBound
      hC.le hP (le_refl N) hN hNy
  have hrecip' :
      freshReciprocalSum N y ≤
        C * logLogNat y +
          (|C * logLogNat N| + 2 * C / Real.log (N : ℝ)) := by
    have hneg : -(C * logLogNat N) ≤ |C * logLogNat N| := neg_le_abs _
    linarith
  calc
    primeEnergyNormalizer y ≤
        primeEnergyNormalizer N * Real.exp (freshReciprocalSum N y) :=
      primeEnergyNormalizer_le_mul_exp_freshReciprocalSum hNy
    _ ≤ primeEnergyNormalizer N *
        Real.exp
          (C * logLogNat y +
            (|C * logLogNat N| + 2 * C / Real.log (N : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hrecip')
        (primeEnergyNormalizer_pos N).le
    _ = D * (Real.log (y : ℝ)) ^ C := by
      rw [Real.exp_add]
      unfold D logLogNat
      rw [Real.rpow_def_of_pos hlogY]
      ring_nf

/-! ## A coefficient-one reciprocal-prime upper bound -/

/-- Expanding `log n` by the von Mangoldt divisor identity and reversing the
two finite sums.  This elementary identity is the source of the sharp
coefficient `1` in the bound below. -/
theorem logSum_eq_mangoldtDivisorSum (y : ℕ) :
    (∑ n ∈ Finset.Ioc 0 y, Real.log (n : ℝ)) =
      ∑ d ∈ Finset.Ioc 0 y, Λ d * (y / d : ℕ) := by
  simp_rw [← vonMangoldt_sum]
  calc
    (∑ n ∈ Finset.Ioc 0 y, ∑ d ∈ n.divisors, Λ d) =
        ∑ n ∈ Finset.Ioc 0 y,
          ∑ d ∈ Finset.Ioc 0 y, if d ∣ n then Λ d else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      calc
        (∑ d ∈ n.divisors, Λ d) =
            ∑ d ∈ n.divisors, if d ∣ n then Λ d else 0 := by
          apply Finset.sum_congr rfl
          intro d hd
          simp [Nat.dvd_of_mem_divisors hd]
        _ = ∑ d ∈ Finset.Ioc 0 y, if d ∣ n then Λ d else 0 := by
          apply Finset.sum_subset
          · intro d hd
            have hdvd := Nat.dvd_of_mem_divisors hd
            have hdpos := Nat.pos_of_mem_divisors hd
            have hdn := Nat.le_of_dvd (Finset.mem_Ioc.mp hn).1 hdvd
            exact Finset.mem_Ioc.mpr
              ⟨hdpos, hdn.trans (Finset.mem_Ioc.mp hn).2⟩
          · intro d _hdI hdnot
            have hndiv : ¬ d ∣ n := by
              intro hdvd
              apply hdnot
              exact Nat.mem_divisors.mpr
                ⟨hdvd, (Finset.mem_Ioc.mp hn).1.ne'⟩
            simp [hndiv]
    _ = ∑ d ∈ Finset.Ioc 0 y,
          ∑ n ∈ Finset.Ioc 0 y, if d ∣ n then Λ d else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Ioc 0 y, Λ d * (y / d : ℕ) := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Nat.Ioc_filter_dvd_card_eq_div]
      simp [mul_comm]

/-- The partial sum `∑_{d≤y} Λ(d)/d`. -/
noncomputable def mangoldtReciprocalPrefix (y : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ioc 0 y, Λ d / (d : ℝ)

/-- An elementary coefficient-one bound for the Mangoldt reciprocal sum.
Only the divisor identity above and Mathlib's Chebyshev bound `ψ(y) = O(y)`
enter the proof. -/
theorem mangoldtReciprocalPrefix_le_log_add_const {y : ℕ} (hy : 1 ≤ y) :
    mangoldtReciprocalPrefix y ≤
      Real.log (y : ℝ) + (Real.log 4 + 4) := by
  have hypos : 0 < y := by omega
  have hterm (d : ℕ) (hd : d ∈ Finset.Ioc 0 y) :
      (y : ℝ) * (Λ d / (d : ℝ)) ≤ Λ d * ((y / d : ℕ) + 1) := by
    have hdpos : 0 < d := (Finset.mem_Ioc.mp hd).1
    have hquot : (y : ℝ) / (d : ℝ) ≤ (y / d : ℕ) + 1 := by
      rw [div_le_iff₀ (by exact_mod_cast hdpos)]
      norm_cast
      have hmod := Nat.mod_lt y hdpos
      have hdecomp := Nat.div_add_mod y d
      calc
        y = d * (y / d) + y % d := hdecomp.symm
        _ ≤ d * (y / d) + d := Nat.add_le_add_left hmod.le _
        _ = (y / d + 1) * d := by rw [add_mul, one_mul, mul_comm d]
    calc
      (y : ℝ) * (Λ d / (d : ℝ)) =
          Λ d * ((y : ℝ) / (d : ℝ)) := by ring
      _ ≤ Λ d * ((y / d : ℕ) + 1) :=
        mul_le_mul_of_nonneg_left hquot vonMangoldt_nonneg
  have hsum :
      (y : ℝ) * mangoldtReciprocalPrefix y ≤
        (∑ d ∈ Finset.Ioc 0 y, Λ d * (y / d : ℕ)) +
          ∑ d ∈ Finset.Ioc 0 y, Λ d := by
    unfold mangoldtReciprocalPrefix
    rw [Finset.mul_sum]
    calc
      (∑ d ∈ Finset.Ioc 0 y, (y : ℝ) * (Λ d / (d : ℝ))) ≤
          ∑ d ∈ Finset.Ioc 0 y, Λ d * ((y / d : ℕ) + 1) := by
        exact Finset.sum_le_sum fun d hd => hterm d hd
      _ = (∑ d ∈ Finset.Ioc 0 y, Λ d * (y / d : ℕ)) +
          ∑ d ∈ Finset.Ioc 0 y, Λ d := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro d _hd
        ring
  have hlogsum :
      (∑ n ∈ Finset.Ioc 0 y, Real.log (n : ℝ)) ≤
        (y : ℝ) * Real.log (y : ℝ) := by
    calc
      (∑ n ∈ Finset.Ioc 0 y, Real.log (n : ℝ)) ≤
          ∑ _n ∈ Finset.Ioc 0 y, Real.log (y : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnpos : (0 : ℝ) < n := by
          exact_mod_cast (Finset.mem_Ioc.mp hn).1
        have hny : (n : ℝ) ≤ y := by
          exact_mod_cast (Finset.mem_Ioc.mp hn).2
        exact Real.log_le_log hnpos hny
      _ = (y : ℝ) * Real.log (y : ℝ) := by simp
  have hpsi :
      (∑ d ∈ Finset.Ioc 0 y, Λ d) ≤
        (Real.log 4 + 4) * (y : ℝ) := by
    have h := Chebyshev.psi_le_const_mul_self
      (x := (y : ℝ)) (by positivity)
    simpa [Chebyshev.psi] using! h
  have hmul :
      (y : ℝ) * mangoldtReciprocalPrefix y ≤
        (y : ℝ) *
          (Real.log (y : ℝ) + (Real.log 4 + 4)) := by
    calc
      (y : ℝ) * mangoldtReciprocalPrefix y ≤
          (∑ d ∈ Finset.Ioc 0 y, Λ d * (y / d : ℕ)) +
            ∑ d ∈ Finset.Ioc 0 y, Λ d := hsum
      _ = (∑ n ∈ Finset.Ioc 0 y, Real.log (n : ℝ)) +
            ∑ d ∈ Finset.Ioc 0 y, Λ d := by
        rw [logSum_eq_mangoldtDivisorSum]
      _ ≤ (y : ℝ) * Real.log (y : ℝ) +
            (Real.log 4 + 4) * (y : ℝ) := add_le_add hlogsum hpsi
      _ = (y : ℝ) *
          (Real.log (y : ℝ) + (Real.log 4 + 4)) := by ring
  have hyposR : (0 : ℝ) < y := by exact_mod_cast hypos
  exact (mul_le_mul_iff_of_pos_left hyposR).mp hmul

/-- Logarithmically weighted reciprocal-prime prefix. -/
noncomputable def weightedPrimeReciprocalPrefix (y : ℕ) : ℝ :=
  ∑ p ∈ (y + 1).primesBelow, Real.log (p : ℝ) / (p : ℝ)

theorem weightedPrimeReciprocalPrefix_le_mangoldt (y : ℕ) :
    weightedPrimeReciprocalPrefix y ≤ mangoldtReciprocalPrefix y := by
  classical
  have hset :
      (y + 1).primesBelow = (Finset.Ioc 0 y).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hpy, hp⟩
      exact ⟨⟨hp.pos, Nat.lt_succ_iff.mp (by simpa using! hpy)⟩, hp⟩
    · rintro ⟨⟨_hp0, hpy⟩, hp⟩
      exact ⟨by simpa using! Nat.lt_succ_of_le hpy, hp⟩
  unfold weightedPrimeReciprocalPrefix mangoldtReciprocalPrefix
  rw [hset, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro n _hn
  by_cases hp : n.Prime
  · simp [hp, vonMangoldt_apply_prime hp]
  · simp only [hp, if_false]
    exact div_nonneg vonMangoldt_nonneg (by positivity)

theorem weightedPrimeReciprocalPrefix_le_log_add_const
    {y : ℕ} (hy : 1 ≤ y) :
    weightedPrimeReciprocalPrefix y ≤
      Real.log (y : ℝ) + (Real.log 4 + 4) :=
  (weightedPrimeReciprocalPrefix_le_mangoldt y).trans
    (mangoldtReciprocalPrefix_le_log_add_const hy)

private noncomputable def weightedPrimeTerm (n : ℕ) : ℝ :=
  if n.Prime then Real.log (n : ℝ) / (n : ℝ) else 0

private theorem sum_weightedPrimeTerm_Icc (y : ℕ) :
    (∑ n ∈ Finset.Icc 0 y, weightedPrimeTerm n) =
      weightedPrimeReciprocalPrefix y := by
  classical
  have hset :
      (y + 1).primesBelow = (Finset.Ioc 0 y).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hpy, hp⟩
      exact ⟨⟨hp.pos, Nat.lt_succ_iff.mp (by simpa using! hpy)⟩, hp⟩
    · rintro ⟨⟨_hp0, hpy⟩, hp⟩
      exact ⟨by simpa using! Nat.lt_succ_of_le hpy, hp⟩
  rw [weightedPrimeReciprocalPrefix, hset, Finset.sum_filter]
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le y), Finset.sum_cons]
  simp only [weightedPrimeTerm, Nat.not_prime_zero, if_false, zero_add]

private theorem sum_inv_prime_Icc (y : ℕ) :
    (∑ n ∈ Finset.Icc 0 y,
        (Real.log (n : ℝ))⁻¹ * weightedPrimeTerm n) =
      primeReciprocalPrefix y := by
  classical
  have hset :
      (y + 1).primesBelow = (Finset.Ioc 0 y).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hpy, hp⟩
      exact ⟨⟨hp.pos, Nat.lt_succ_iff.mp (by simpa using! hpy)⟩, hp⟩
    · rintro ⟨⟨_hp0, hpy⟩, hp⟩
      exact ⟨by simpa using! Nat.lt_succ_of_le hpy, hp⟩
  rw [primeReciprocalPrefix, hset, Finset.sum_filter]
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le y), Finset.sum_cons]
  simp only [weightedPrimeTerm, Nat.not_prime_zero, if_false, mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hp : n.Prime
  · have hlog : Real.log (n : ℝ) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one
        (by exact_mod_cast hp.pos) (by exact_mod_cast hp.ne_one)
    simp [hp, hlog, div_eq_mul_inv, mul_comm]
  · simp [hp]

/-- Abel summation expresses the reciprocal-prime prefix in terms of the
coefficient-one weighted prefix. -/
theorem primeReciprocalPrefix_eq_weighted_integral (y : ℕ) :
    primeReciprocalPrefix y =
      weightedPrimeReciprocalPrefix y / Real.log (y : ℝ) +
        ∫ t in Set.Ioc (2 : ℝ) y,
          weightedPrimeReciprocalPrefix ⌊t⌋₊ / (t * Real.log t ^ 2) := by
  let f : ℝ → ℝ := fun t => (Real.log t)⁻¹
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) y, DifferentiableAt ℝ f t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlogt : Real.log t ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith [ht.1]
    dsimp [f]
    exact (Real.differentiableAt_log ht0).inv hlogt
  have hint : IntegrableOn (deriv f) (Set.Icc (2 : ℝ) y) := by
    have hcont : ContinuousOn (fun t : ℝ => -(t * Real.log t ^ 2)⁻¹)
        (Set.Icc (2 : ℝ) y) := by
      intro t ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have hlogt : Real.log t ≠ 0 := by
        apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith [ht.1]
      exact (((continuousAt_id.mul ((Real.continuousAt_log ht0).pow 2)).inv₀
        (mul_ne_zero ht0 (pow_ne_zero 2 hlogt))).neg).continuousWithinAt
    have heq : deriv f = fun t : ℝ => -(t * Real.log t ^ 2)⁻¹ := by
      funext t
      dsimp [f]
      rw [Real.deriv_inv_log]
      simp [div_eq_mul_inv, mul_inv_rev, mul_comm]
    rw [heq]
    exact hcont.integrableOn_Icc
  have hab := sum_mul_eq_sub_integral_mul₁ weightedPrimeTerm
    (by simp [weightedPrimeTerm]) (by simp [weightedPrimeTerm]) (y : ℝ)
    hdiff hint
  rw [Nat.floor_natCast] at hab
  rw [sum_inv_prime_Icc, sum_weightedPrimeTerm_Icc] at hab
  rw [hab]
  simp only [f, div_eq_mul_inv]
  have hi :
      (∫ t in Set.Ioc (2 : ℝ) y,
          deriv (fun t => (Real.log t)⁻¹) t *
            ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, weightedPrimeTerm k) =
        -∫ t in Set.Ioc (2 : ℝ) y,
          weightedPrimeReciprocalPrefix ⌊t⌋₊ *
            (t * Real.log t ^ 2)⁻¹ := by
    calc
      _ = ∫ t in Set.Ioc (2 : ℝ) y,
          -(weightedPrimeReciprocalPrefix ⌊t⌋₊ *
            (t * Real.log t ^ 2)⁻¹) := by
        apply integral_congr_ae
        filter_upwards with t
        rw [Real.deriv_inv_log, sum_weightedPrimeTerm_Icc]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by rw [integral_neg]
  rw [hi]
  ring

/-- The coefficient-one upper half of Mertens' reciprocal-prime estimate,
with a deliberately coarse explicit constant. -/
theorem primeReciprocalPrefix_le_logLog_add_const
    {y : ℕ} (hy : 2 ≤ y) :
    primeReciprocalPrefix y ≤
      logLogNat y +
        (1 - Real.log (Real.log 2) +
          2 * (Real.log 4 + 4) / Real.log 2) := by
  let K : ℝ := Real.log 4 + 4
  have hK : 0 ≤ K := by
    dsimp [K]
    have : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogy : 0 < Real.log (y : ℝ) :=
    hlog2.trans_le (Real.log_le_log (by norm_num) hyR)
  have hboundary :
      weightedPrimeReciprocalPrefix y / Real.log (y : ℝ) ≤
        1 + K / Real.log 2 := by
    have hweighted :
        weightedPrimeReciprocalPrefix y ≤ Real.log (y : ℝ) + K := by
      simpa [K] using! weightedPrimeReciprocalPrefix_le_log_add_const
        (show 1 ≤ y by omega)
    calc
      weightedPrimeReciprocalPrefix y / Real.log (y : ℝ) ≤
          (Real.log (y : ℝ) + K) / Real.log (y : ℝ) :=
        div_le_div_of_nonneg_right hweighted hlogy.le
      _ = 1 + K / Real.log (y : ℝ) := by field_simp
      _ ≤ 1 + K / Real.log 2 := by gcongr
  let g : ℝ → ℝ := fun t =>
    weightedPrimeReciprocalPrefix ⌊t⌋₊ / (t * Real.log t ^ 2)
  let G : ℝ → ℝ := fun t =>
    1 / (t * Real.log t) + K / (t * Real.log t ^ 2)
  have hgInt : IntegrableOn g (Set.Icc (2 : ℝ) y) := by
    have hdenCont : ContinuousOn (fun t : ℝ => (t * Real.log t ^ 2)⁻¹)
        (Set.Icc (2 : ℝ) y) := by
      intro t ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have hlogt : Real.log t ≠ 0 := by
        apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith [ht.1]
      exact ((continuousAt_id.mul ((Real.continuousAt_log ht0).pow 2)).inv₀
        (mul_ne_zero ht0 (pow_ne_zero 2 hlogt))).continuousWithinAt
    have hbase := integrableOn_mul_sum_Icc (m := 0) weightedPrimeTerm
      (show (0 : ℝ) ≤ 2 by norm_num) hdenCont.integrableOn_Icc
    apply hbase.congr_fun
    · intro t _ht
      dsimp [g]
      rw [← sum_weightedPrimeTerm_Icc]
      ring
    · exact measurableSet_Icc
  have hGCont : ContinuousOn G (Set.Icc (2 : ℝ) y) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlogt : Real.log t ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith [ht.1]
    dsimp [G]
    have hlogcont := Real.continuousAt_log ht0
    have hden1 : t * Real.log t ≠ 0 := mul_ne_zero ht0 hlogt
    have hden2 : t * Real.log t ^ 2 ≠ 0 :=
      mul_ne_zero ht0 (pow_ne_zero 2 hlogt)
    exact ((continuousAt_const.div (continuousAt_id.mul hlogcont) hden1).add
      (continuousAt_const.div
        (continuousAt_id.mul (hlogcont.pow 2)) hden2)).continuousWithinAt
  have hpoint : ∀ t ∈ Set.Ioc (2 : ℝ) y, g t ≤ G t := by
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hfloor : 1 ≤ ⌊t⌋₊ := by
      exact (Nat.one_le_floor_iff t).2 (by linarith [ht.1])
    have hweighted := weightedPrimeReciprocalPrefix_le_log_add_const hfloor
    have hfloorle : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith [ht.1])
    have hfloorpos : (0 : ℝ) < ⌊t⌋₊ := by exact_mod_cast hfloor
    have hnum : weightedPrimeReciprocalPrefix ⌊t⌋₊ ≤ Real.log t + K := by
      calc
        weightedPrimeReciprocalPrefix ⌊t⌋₊ ≤
            Real.log (⌊t⌋₊ : ℝ) + (Real.log 4 + 4) := hweighted
        _ ≤ Real.log t + K := by
          dsimp [K]
          gcongr
    dsimp [g, G]
    calc
      weightedPrimeReciprocalPrefix ⌊t⌋₊ / (t * Real.log t ^ 2) ≤
          (Real.log t + K) / (t * Real.log t ^ 2) := by
        exact div_le_div_of_nonneg_right hnum (by positivity)
      _ = 1 / (t * Real.log t) + K / (t * Real.log t ^ 2) := by
        field_simp
  have hintegral :
      (∫ t in Set.Ioc (2 : ℝ) y, g t) ≤
        ∫ t in Set.Ioc (2 : ℝ) y, G t := by
    apply setIntegral_mono_on
    · exact hgInt.mono_set Set.Ioc_subset_Icc_self
    · exact hGCont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    · exact measurableSet_Ioc
    · exact hpoint
  have hGIntegral :
      (∫ t in Set.Ioc (2 : ℝ) y, G t) =
        logLogNat y - Real.log (Real.log 2) +
          K / Real.log 2 - K / Real.log (y : ℝ) := by
    rw [← intervalIntegral.integral_of_le hyR]
    have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) y,
        HasDerivAt
          (fun x : ℝ => Real.log (Real.log x) - K / Real.log x)
          (G t) t := by
      intro t ht
      rw [Set.uIcc_of_le hyR] at ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have hlogt : Real.log t ≠ 0 := by
        apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith [ht.1]
      dsimp [G]
      convert! (Real.hasDerivAt_log ht0).log hlogt |>.sub
        ((hasDerivAt_const t K).div (Real.hasDerivAt_log ht0) hlogt) using 1 <;>
        field_simp <;> ring
    have hGContU : ContinuousOn G (Set.uIcc (2 : ℝ) y) := by
      simpa [Set.uIcc_of_le hyR] using! hGCont
    have hbase := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      hGContU.intervalIntegrable
    rw [hbase]
    unfold logLogNat
    ring
  rw [hGIntegral] at hintegral
  have hdrop :
      logLogNat y - Real.log (Real.log 2) +
          K / Real.log 2 - K / Real.log (y : ℝ) ≤
        logLogNat y - Real.log (Real.log 2) + K / Real.log 2 := by
    have : 0 ≤ K / Real.log (y : ℝ) := div_nonneg hK hlogy.le
    linarith
  rw [primeReciprocalPrefix_eq_weighted_integral]
  change weightedPrimeReciprocalPrefix y / Real.log (y : ℝ) +
      (∫ t in Set.Ioc (2 : ℝ) y, g t) ≤ _
  calc
    weightedPrimeReciprocalPrefix y / Real.log (y : ℝ) +
        (∫ t in Set.Ioc (2 : ℝ) y, g t) ≤
      (1 + K / Real.log 2) +
        (logLogNat y - Real.log (Real.log 2) + K / Real.log 2) :=
      add_le_add hboundary (hintegral.trans hdrop)
    _ = logLogNat y +
        (1 - Real.log (Real.log 2) +
          2 * (Real.log 4 + 4) / Real.log 2) := by
      dsimp [K]
      ring

/-- A completely explicit `O(log y)` bound for the exact Euler normalizer. -/
theorem primeEnergyNormalizer_le_mertensConstant_mul_log
    {y : ℕ} (hy : 2 ≤ y) :
    primeEnergyNormalizer y ≤
      Real.exp
          (1 - Real.log (Real.log 2) +
            2 * (Real.log 4 + 4) / Real.log 2) *
        Real.log (y : ℝ) := by
  have hprefix := primeReciprocalPrefix_le_logLog_add_const hy
  have hlogy : 0 < Real.log (y : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < y by omega)
  calc
    primeEnergyNormalizer y ≤ Real.exp (primeReciprocalPrefix y) :=
      primeEnergyNormalizer_le_exp_primeReciprocalPrefix y
    _ ≤ Real.exp
        (logLogNat y +
          (1 - Real.log (Real.log 2) +
            2 * (Real.log 4 + 4) / Real.log 2)) :=
      Real.exp_le_exp.mpr hprefix
    _ = Real.exp
          (1 - Real.log (Real.log 2) +
            2 * (Real.log 4 + 4) / Real.log 2) *
        Real.log (y : ℝ) := by
      rw [Real.exp_add]
      unfold logLogNat
      rw [Real.exp_log hlogy]
      ring

/-- Axiom-free constant-factor Mertens upper bound in the requested
existential form. -/
theorem exists_primeEnergyNormalizer_mertens_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ y : ℕ, N ≤ y →
      primeEnergyNormalizer y ≤ C * Real.log (y : ℝ) := by
  refine ⟨Real.exp
      (1 - Real.log (Real.log 2) +
        2 * (Real.log 4 + 4) / Real.log 2), Real.exp_pos _, 2, ?_⟩
  intro y hy
  exact primeEnergyNormalizer_le_mertensConstant_mul_log hy

/-! ## The matching elementary lower bound -/

/-- The completely multiplicative reciprocal weight used in the finite Euler
geometric product. -/
noncomputable def reciprocalNatMonoidHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by simp [Nat.cast_mul, mul_inv_rev, mul_comm]

private def harmonicSmoothEmbedding (y : ℕ) :
    {n // n ∈ Finset.Icc 1 y} ↪ (y + 1).smoothNumbers where
  toFun n := ⟨n.1, Nat.mem_smoothNumbers_of_lt
    (Finset.mem_Icc.mp n.2).1
    (Nat.lt_succ_of_le (Finset.mem_Icc.mp n.2).2)⟩
  inj' a b h := by
    apply Subtype.ext
    exact congrArg (fun x : (y + 1).smoothNumbers => (x : ℕ)) h

private def harmonicSmoothFinset (y : ℕ) :
    Finset (y + 1).smoothNumbers :=
  (Finset.Icc 1 y).attach.map (harmonicSmoothEmbedding y)

/-- The geometric Euler product contains every reciprocal `1/n`, `1 ≤ n ≤ y`,
because every such `n` is `(y+1)`-smooth. -/
theorem harmonic_le_geometricPrimeProduct (y : ℕ) :
    (harmonic y : ℝ) ≤
      ∏ p ∈ (y + 1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ := by
  have heuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (f := reciprocalNatMonoidHom)
      (fun {p} hp => by
        change |(p : ℝ)⁻¹| < 1
        rw [abs_of_pos (inv_pos.mpr (by exact_mod_cast hp.pos))]
        exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)) (y + 1)
  have hfin :
      (∑ m ∈ harmonicSmoothFinset y, reciprocalNatMonoidHom m) ≤
        ∑' m : (y + 1).smoothNumbers, reciprocalNatMonoidHom m := by
    exact heuler.1.of_norm.sum_le_tsum (harmonicSmoothFinset y)
      (fun m _hm => by
        change 0 ≤ ((m : ℕ) : ℝ)⁻¹
        positivity)
  rw [heuler.2.tsum_eq] at hfin
  calc
    (harmonic y : ℝ) =
        ∑ n ∈ Finset.Icc 1 y, (n : ℝ)⁻¹ := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ = ∑ m ∈ harmonicSmoothFinset y,
        reciprocalNatMonoidHom m := by
      unfold harmonicSmoothFinset
      rw [Finset.sum_map]
      rw [← Finset.sum_attach]
      rfl
    _ ≤ _ := hfin

/-- The elementary telescoping product
`∏_{2 ≤ n ≤ y} (1 - 1/n²) = (y+1)/(2y)`. -/
theorem prod_one_sub_inv_sq_Icc (y : ℕ) (hy : 1 ≤ y) :
    (∏ n ∈ Finset.Icc 2 y, (1 - ((n : ℝ)⁻¹) ^ 2)) =
      ((y + 1 : ℕ) : ℝ) / ((2 * y : ℕ) : ℝ) := by
  induction y with
  | zero => omega
  | succ y ih =>
      by_cases hy1 : y = 0
      · subst y
        norm_num
      · have hypos : 0 < y := Nat.pos_of_ne_zero hy1
        rw [Finset.prod_Icc_succ_top (by omega), ih (by omega)]
        have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy1
        have hysR : ((y + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        push_cast
        field_simp
        ring

/-- Removing the composite indices from the preceding product can only
increase it, so the prime square-loss factor is at least `1/2`. -/
theorem half_le_squareLossPrimeProduct {y : ℕ} (hy : 2 ≤ y) :
    (1 / 2 : ℝ) ≤
      ∏ p ∈ (y + 1).primesBelow, (1 - ((p : ℝ)⁻¹) ^ 2) := by
  have hsubset : (y + 1).primesBelow ⊆ Finset.Icc 2 y := by
    intro p hp
    have hmem := Nat.mem_primesBelow.mp hp
    exact Finset.mem_Icc.mpr
      ⟨hmem.2.two_le, Nat.lt_succ_iff.mp hmem.1⟩
  have hprod :
      (∏ n ∈ Finset.Icc 2 y, (1 - ((n : ℝ)⁻¹) ^ 2)) ≤
        ∏ p ∈ (y + 1).primesBelow, (1 - ((p : ℝ)⁻¹) ^ 2) := by
    exact Finset.prod_le_prod_of_subset_of_le_one hsubset
      (fun n hn => by
        have hn2 : (2 : ℝ) ≤ n := by
          exact_mod_cast (Finset.mem_Icc.mp hn).1
        have hinv : ((n : ℝ)⁻¹) ^ 2 ≤ 1 := by
          have hinv1 : (n : ℝ)⁻¹ ≤ 1 :=
            (inv_le_one₀ (by linarith : (0 : ℝ) < n)).2 (by linarith)
          nlinarith [mul_self_le_mul_self
            (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹) hinv1]
        linarith)
      (fun n _hn _hnot => by
        have := sq_nonneg ((n : ℝ)⁻¹)
        linarith)
  rw [prod_one_sub_inv_sq_Icc y (by omega)] at hprod
  calc
    (1 / 2 : ℝ) ≤
        ((y + 1 : ℕ) : ℝ) / ((2 * y : ℕ) : ℝ) := by
      have hypos : (0 : ℝ) < y := by positivity
      push_cast
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    _ ≤ _ := hprod

/-- Factor the exact normalizer into its square-loss factor and the geometric
Mertens product. -/
theorem primeEnergyNormalizer_eq_squareLoss_mul_geometric (y : ℕ) :
    primeEnergyNormalizer y =
      (∏ p ∈ (y + 1).primesBelow, (1 - ((p : ℝ)⁻¹) ^ 2)) *
        ∏ p ∈ (y + 1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ := by
  unfold primeEnergyNormalizer
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpone : (p : ℝ) ≠ 1 := by
    exact_mod_cast (Nat.Prime.ne_one (Nat.prime_of_mem_primesBelow hp))
  have hden : 1 - (p : ℝ)⁻¹ ≠ 0 := by
    intro h
    have hinv : (p : ℝ)⁻¹ = 1 := (sub_eq_zero.mp h).symm
    apply hpone
    calc
      (p : ℝ) = ((p : ℝ)⁻¹)⁻¹ := (inv_inv _).symm
      _ = 1 := by rw [hinv, inv_one]
  symm
  rw [← div_eq_mul_inv]
  apply (div_eq_iff hden).2
  ring

/-- Explicit matching lower bound for the exact normalizer. -/
theorem half_mul_log_le_primeEnergyNormalizer {y : ℕ} (hy : 2 ≤ y) :
    (1 / 2 : ℝ) * Real.log (y : ℝ) ≤ primeEnergyNormalizer y := by
  have hA := half_le_squareLossPrimeProduct hy
  have hB : Real.log (y : ℝ) ≤
      ∏ p ∈ (y + 1).primesBelow, (1 - (p : ℝ)⁻¹)⁻¹ := by
    calc
      Real.log (y : ℝ) ≤ Real.log ((y + 1 : ℕ) : ℝ) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast Nat.le_succ y
      _ ≤ (harmonic y : ℝ) := log_add_one_le_harmonic y
      _ ≤ _ := harmonic_le_geometricPrimeProduct y
  rw [primeEnergyNormalizer_eq_squareLoss_mul_geometric]
  exact mul_le_mul hA hB
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))) (by linarith)

/-- Axiom-free constant-factor Mertens lower bound in existential form. -/
theorem exists_primeEnergyNormalizer_mertens_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ y : ℕ, N ≤ y →
      c * Real.log (y : ℝ) ≤ primeEnergyNormalizer y := by
  exact ⟨1 / 2, by norm_num, 2,
    fun y hy => half_mul_log_le_primeEnergyNormalizer hy⟩

/-- Two-sided constant-factor comparison, with no analytic hypothesis and no
use of the prime number theorem. -/
theorem exists_primeEnergyNormalizer_mertens_comparison :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ y : ℕ, N ≤ y →
      c * Real.log (y : ℝ) ≤ primeEnergyNormalizer y ∧
        primeEnergyNormalizer y ≤ C * Real.log (y : ℝ) := by
  refine ⟨1 / 2,
    Real.exp
      (1 - Real.log (Real.log 2) +
        2 * (Real.log 4 + 4) / Real.log 2),
    by norm_num, Real.exp_pos _, 2, ?_⟩
  intro y hy
  exact ⟨half_mul_log_le_primeEnergyNormalizer hy,
    primeEnergyNormalizer_le_mertensConstant_mul_log hy⟩

end Problem520
end Erdos
