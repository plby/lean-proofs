/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.CongruenceCounting
import ErdosProblems.Erdos387.DivisorStructure
import ErdosProblems.Erdos896.Ford.ReductionCore
import ErdosProblems.Erdos896.PNT.Mathlib.NumberTheory.Sieve.SelbergBounds
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Chebyshev

namespace Erdos896.Ford

open Filter Asymptotics
open scoped BigOperators ArithmeticFunction.zeta

/-- An integer with no prime divisor at most `z - 1`, equivalently none
strictly below `z`. -/
def IsRough (z n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≤ z - 1 → ¬ p ∣ n

noncomputable def roughNumbersUpTo (X z : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter (IsRough z)

@[simp] theorem mem_roughNumbersUpTo {X z n : ℕ} :
    n ∈ roughNumbersUpTo X z ↔ 0 < n ∧ n ≤ X ∧ IsRough z n := by
  classical
  simp only [roughNumbersUpTo, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hn, hnX⟩, hrough⟩
    exact ⟨by omega, hnX, hrough⟩
  · rintro ⟨hn, hnX, hrough⟩
    exact ⟨⟨by omega, hnX⟩, hrough⟩

noncomputable def roughBoundingSieve (X z : ℕ) : BoundingSieve := by
  classical
  exact
    { support := Finset.Ioc 0 X
      prodPrimes := primorial (z - 1)
      prodPrimes_squarefree := Sieve.primorial_squarefree _
      weights := fun _ => 1
      weights_nonneg := fun _ => by norm_num
      totalMass := X
      nu := (ArithmeticFunction.zeta : ArithmeticFunction ℝ).pdiv .id
      nu_mult := (Sieve.CompletelyMultiplicative.pdiv
        Sieve.CompletelyMultiplicative.zeta
        Sieve.CompletelyMultiplicative.id).isMultiplicative
      nu_pos_of_prime := by
        intro p hp _
        simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
          if_neg hp.ne_zero, Nat.cast_one, ArithmeticFunction.id_apply]
        exact div_pos (by norm_num) (by exact_mod_cast hp.pos)
      nu_lt_one_of_prime := by
        intro p hp _
        simp only [ArithmeticFunction.pdiv_apply,
          ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
          if_neg hp.ne_zero, Nat.cast_one, ArithmeticFunction.id_apply]
        have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
        exact (div_lt_one hpR).2 (by exact_mod_cast hp.one_lt) }

noncomputable def roughSelbergSieve (X z : ℕ) (hz : 2 ≤ z) : SelbergSieve :=
  { roughBoundingSieve X z with
    level := (z - 1 : ℕ)
    one_le_level := by exact_mod_cast (show 1 ≤ z - 1 by omega) }

theorem coprime_primorial_pred_iff_rough {z n : ℕ} :
    Nat.Coprime (primorial (z - 1)) n ↔ IsRough z n := by
  constructor
  · intro hcop p hp hpz hpn
    have hpP : p ∣ primorial (z - 1) :=
      (Sieve.prime_dvd_primorial_iff (z - 1) p hp).2 hpz
    exact (hp.coprime_iff_not_dvd.mp (hcop.coprime_dvd_left hpP)) hpn
  · intro hrough
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hgcd
    obtain ⟨p, hp, hpDvd⟩ := Nat.exists_prime_and_dvd hgcd
    have hpP : p ∣ primorial (z - 1) :=
      hpDvd.trans (Nat.gcd_dvd_left _ _)
    have hpz1 : p ≤ z - 1 :=
      (Sieve.prime_dvd_primorial_iff (z - 1) p hp).1 hpP
    exact hrough p hp hpz1 (hpDvd.trans (Nat.gcd_dvd_right _ _))

theorem roughBoundingSieve_siftedSum (X z : ℕ) :
    (roughBoundingSieve X z).siftedSum = ((roughNumbersUpTo X z).card : ℝ) := by
  classical
  rw [BoundingSieve.siftedSum]
  change (∑ d ∈ Finset.Ioc 0 X,
      if Nat.Coprime (primorial (z - 1)) d then (1 : ℝ) else 0) = _
  simp_rw [coprime_primorial_pred_iff_rough]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1

theorem roughBoundingSieve_multSum_eq_card_modularPreimage
    {X z d : ℕ} (_hd : 0 < d) :
    (roughBoundingSieve X z).multSum d =
      ((Erdos387.modularPreimageIoc 0 X d {0}).card : ℝ) := by
  classical
  rw [BoundingSieve.multSum]
  change (∑ n ∈ Finset.Ioc 0 X, if d ∣ n then (1 : ℝ) else 0) = _
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext n
  simp only [Finset.mem_filter, Erdos387.modularPreimageIoc,
    Finset.mem_singleton]
  rw [Nat.dvd_iff_mod_eq_zero]

theorem roughBoundingSieve_abs_rem_le_two {X z d : ℕ} (hd : 0 < d) :
    |(roughBoundingSieve X z).rem d| ≤ 2 := by
  have hcount := Erdos387.abs_card_modularPreimageIoc_sub_density
    (show 0 ≤ X by omega) hd ({0} : Finset ℕ) (by
      intro a ha
      simp only [Finset.mem_singleton] at ha
      subst a
      exact hd)
  rw [BoundingSieve.rem]
  change |(roughBoundingSieve X z).multSum d -
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ).pdiv .id) d * (X : ℝ)| ≤ 2
  rw [roughBoundingSieve_multSum_eq_card_modularPreimage hd]
  have hnu : ((ArithmeticFunction.zeta : ArithmeticFunction ℝ).pdiv .id) d =
      (d : ℝ)⁻¹ := by
    simp [ArithmeticFunction.pdiv_apply, hd.ne']
  rw [hnu]
  simpa [div_eq_mul_inv, mul_comm] using hcount

theorem roughSelbergSieve_level_primes {X z : ℕ} (hz : 2 ≤ z) :
    ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (roughSelbergSieve X z hz).level →
      p ∣ (roughSelbergSieve X z hz).prodPrimes := by
  intro p hp hple
  change p ∣ primorial (z - 1)
  apply (Sieve.prime_dvd_primorial_iff (z - 1) p hp).2
  change (p : ℝ) ≤ ((z - 1 : ℕ) : ℝ) at hple
  exact_mod_cast hple

/-- The direct Selberg upper bound, before the elementary error term is
absorbed into the main term. -/
theorem roughNumbersUpTo_card_le_selberg {X z : ℕ} (hz : 3 ≤ z) :
    ((roughNumbersUpTo X z).card : ℝ) ≤
      2 * (X : ℝ) / Real.log (z - 1 : ℕ) +
        2 * (z - 1 : ℕ) * (1 + Real.log (z - 1 : ℕ)) ^ 3 := by
  let s := roughSelbergSieve X z (by omega)
  have hsieve := SelbergSieve.selberg_bound_simple s
  have herr := Sieve.rem_sum_le_of_const s 2 (by
    intro d hd
    exact roughBoundingSieve_abs_rem_le_two hd)
  have hsum := Sieve.boundingSum_ge_log s rfl
    (roughSelbergSieve_level_primes (X := X) (z := z) (by omega))
  have hlevel : s.level = ((z - 1 : ℕ) : ℝ) := rfl
  have hlevelOne : 1 < s.level := by
    rw [hlevel]
    exact_mod_cast (show 1 < z - 1 by omega)
  have hlogPos : 0 < Real.log s.level := Real.log_pos hlevelOne
  have hSPos : 0 < s.selbergBoundingSum := s.selbergBoundingSum_pos
  have hmain : (X : ℝ) / s.selbergBoundingSum ≤
      2 * (X : ℝ) / Real.log s.level := by
    rw [div_le_iff₀ hSPos]
    rw [div_mul_eq_mul_div]
    rw [le_div_iff₀ hlogPos]
    nlinarith [show (0 : ℝ) ≤ (X : ℝ) by positivity]
  change (roughBoundingSieve X z).siftedSum ≤
      (X : ℝ) / s.selbergBoundingSum + _ at hsieve
  rw [roughBoundingSieve_siftedSum] at hsieve
  calc
    ((roughNumbersUpTo X z).card : ℝ) ≤
        (X : ℝ) / s.selbergBoundingSum +
          ∑ d ∈ s.prodPrimes.divisors,
            if (d : ℝ) ≤ s.level then
              (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d *
                |BoundingSieve.rem (s := s.toBoundingSieve) d|
            else 0 := hsieve
    _ ≤ 2 * (X : ℝ) / Real.log s.level +
          2 * s.level * (1 + Real.log s.level) ^ 3 :=
      add_le_add hmain herr
    _ = 2 * (X : ℝ) / Real.log (z - 1 : ℕ) +
          2 * (z - 1 : ℕ) * (1 + Real.log (z - 1 : ℕ)) ^ 3 := by
      rw [hlevel]

private theorem eventually_log_pow_four_le_nat :
    ∀ᶠ z : ℕ in atTop, Real.log (z : ℝ) ^ 4 ≤ (z : ℝ) := by
  have hreal :=
    (Real.isLittleO_pow_log_id_atTop (n := 4)).bound (show (0 : ℝ) < 1 by norm_num)
  have hnat := tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat, eventually_ge_atTop 2] with z hzsmall hz
  have hzPos : (0 : ℝ) < (z : ℝ) := by positivity
  have hlogPos : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  simpa [Function.comp_apply, Real.norm_eq_abs, abs_of_pos hlogPos,
    abs_of_pos hzPos] using hzsmall

private theorem roughNumbersUpTo_card_le_36_aux {X z : ℕ}
    (hz : 3 ≤ z) (hX : z ^ 2 ≤ X)
    (hlog4 : Real.log (z : ℝ) ^ 4 ≤ (z : ℝ)) :
    ((roughNumbersUpTo X z).card : ℝ) ≤
      36 * (X : ℝ) / Real.log z := by
  have hzPos : (0 : ℝ) < (z : ℝ) := by positivity
  have hpredNat : 0 < z - 1 := by omega
  have hpredPos : (0 : ℝ) < ((z - 1 : ℕ) : ℝ) := by exact_mod_cast hpredNat
  have hlogPos : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hlogPredPos : 0 < Real.log ((z - 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z - 1 by omega))
  have hpredLe : ((z - 1 : ℕ) : ℝ) ≤ (z : ℝ) := by
    exact_mod_cast Nat.sub_le z 1
  have hlogPredLe : Real.log ((z - 1 : ℕ) : ℝ) ≤ Real.log (z : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hpredPos hzPos hpredLe
  have hzSqNat : z ≤ (z - 1) ^ 2 := by
    calc
      z = (z - 1) + 1 := by omega
      _ ≤ (z - 1) ^ 2 := by nlinarith [show 2 ≤ z - 1 by omega]
  have hzSq : (z : ℝ) ≤ (((z - 1 : ℕ) : ℝ) ^ 2) := by
    exact_mod_cast hzSqNat
  have hlogZLeTwo : Real.log (z : ℝ) ≤
      2 * Real.log ((z - 1 : ℕ) : ℝ) := by
    have h := Real.strictMonoOn_log.monotoneOn hzPos
      (by positivity : (0 : ℝ) < (((z - 1 : ℕ) : ℝ) ^ 2)) hzSq
    simpa [Real.log_pow] using h
  have hmain : 2 * (X : ℝ) / Real.log (z - 1 : ℕ) ≤
      4 * (X : ℝ) / Real.log z := by
    rw [div_le_div_iff₀ hlogPredPos hlogPos]
    nlinarith [show (0 : ℝ) ≤ (X : ℝ) by positivity]
  have honeLogPow : (1 + Real.log (z : ℝ)) ^ 4 ≤ 16 * (z : ℝ) := by
    by_cases hlogOne : Real.log (z : ℝ) ≤ 1
    · calc
        (1 + Real.log (z : ℝ)) ^ 4 ≤ (2 : ℝ) ^ 4 := by
          gcongr
          linarith
        _ ≤ 16 * (z : ℝ) := by norm_num; nlinarith
    · have hOneLog : 1 ≤ Real.log (z : ℝ) := le_of_not_ge hlogOne
      calc
        (1 + Real.log (z : ℝ)) ^ 4 ≤
            (2 * Real.log (z : ℝ)) ^ 4 := by
          gcongr
          linarith
        _ = 16 * Real.log (z : ℝ) ^ 4 := by ring
        _ ≤ 16 * (z : ℝ) := by nlinarith
  have herrNumerator :
      (2 * ((z - 1 : ℕ) : ℝ) *
          (1 + Real.log (z - 1 : ℕ)) ^ 3) * Real.log z ≤
        32 * (X : ℝ) := by
    calc
      (2 * ((z - 1 : ℕ) : ℝ) *
          (1 + Real.log (z - 1 : ℕ)) ^ 3) * Real.log z ≤
          2 * (z : ℝ) * (1 + Real.log (z : ℝ)) ^ 3 * Real.log z := by
        gcongr
      _ ≤ 2 * (z : ℝ) * (1 + Real.log (z : ℝ)) ^ 4 := by
        have hfac : 0 ≤
            2 * (z : ℝ) * (1 + Real.log (z : ℝ)) ^ 3 := by positivity
        calc
          2 * (z : ℝ) * (1 + Real.log (z : ℝ)) ^ 3 * Real.log z ≤
              (2 * (z : ℝ) * (1 + Real.log (z : ℝ)) ^ 3) *
                (1 + Real.log z) := by
            exact mul_le_mul_of_nonneg_left (by linarith) hfac
          _ = 2 * (z : ℝ) * (1 + Real.log (z : ℝ)) ^ 4 := by ring
      _ ≤ 2 * (z : ℝ) * (16 * (z : ℝ)) := by
        gcongr
      _ = 32 * ((z : ℝ) ^ 2) := by ring
      _ ≤ 32 * (X : ℝ) := by
        gcongr
        exact_mod_cast hX
  have herr : 2 * ((z - 1 : ℕ) : ℝ) *
      (1 + Real.log (z - 1 : ℕ)) ^ 3 ≤
        32 * (X : ℝ) / Real.log z := by
    rw [le_div_iff₀ hlogPos]
    simpa [mul_assoc] using herrNumerator
  calc
    ((roughNumbersUpTo X z).card : ℝ) ≤
        2 * (X : ℝ) / Real.log (z - 1 : ℕ) +
          2 * (z - 1 : ℕ) * (1 + Real.log (z - 1 : ℕ)) ^ 3 :=
      roughNumbersUpTo_card_le_selberg hz
    _ ≤ 4 * (X : ℝ) / Real.log z + 32 * (X : ℝ) / Real.log z :=
      add_le_add hmain herr
    _ = 36 * (X : ℝ) / Real.log z := by ring

/-- Uniform one-dimensional upper sieve in the polynomial-room range used
in Ford's reduction. -/
theorem exists_roughNumbersUpTo_card_le_div_log_of_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ {X z : ℕ},
      N₀ ≤ z → z ^ 2 ≤ X →
      ((roughNumbersUpTo X z).card : ℝ) ≤
        C * (X : ℝ) / Real.log z := by
  have hevent := eventually_log_pow_four_le_nat
  rw [eventually_atTop] at hevent
  obtain ⟨N₀, hN₀⟩ := hevent
  refine ⟨36, by norm_num, max N₀ 3, ?_⟩
  intro X z hz hX
  exact roughNumbersUpTo_card_le_36_aux
    (show 3 ≤ z from (le_max_right N₀ 3).trans hz) hX
    (hN₀ z ((le_max_left N₀ 3).trans hz))

private theorem roughNumbersUpTo_subset_one_insert_primesLE
    {X z : ℕ} (hXz : X < z ^ 2) :
    roughNumbersUpTo X z ⊆ insert 1 (Nat.primesLE X) := by
  intro n hn
  rw [mem_roughNumbersUpTo] at hn
  by_cases hn1 : n = 1
  · simp [hn1]
  have hnPrime : n.Prime := by
    by_contra hnNotPrime
    have hpPrime : n.minFac.Prime := Nat.minFac_prime hn1
    have hpDvd : n.minFac ∣ n := Nat.minFac_dvd n
    have hpLarge : z ≤ n.minFac := by
      by_contra hpNot
      have hpSmall : n.minFac ≤ z - 1 := by omega
      exact hn.2.2 n.minFac hpPrime hpSmall hpDvd
    have hpSq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self hn.1 hnNotPrime
    nlinarith [hn.2.1]
  simp [Nat.mem_primesLE, hnPrime, hn.2.1]

private theorem exists_roughNumbersUpTo_card_le_div_log_of_lt_sq :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ {X z : ℕ},
      N₀ ≤ z → z ≤ X → X < z ^ 2 →
      ((roughNumbersUpTo X z).card : ℝ) ≤
        C * (X : ℝ) / Real.log z := by
  have hevent :=
    Chebyshev.eventually_primeCounting_le (ε := (1 : ℝ)) (by norm_num)
  obtain ⟨x, hx⟩ := Filter.eventually_atTop.mp hevent
  obtain ⟨N, hxN⟩ := exists_nat_ge x
  let Cπ := Real.log 4 + 1
  have hCπ : 0 < Cπ := by
    dsimp [Cπ]
    have := Real.log_pos (show (1 : ℝ) < 4 by norm_num)
    linarith
  have hcheb : ∀ t : ℕ, N ≤ t →
      (Nat.primeCounting t : ℝ) ≤ Cπ * t / Real.log t := by
    intro t hNt
    have hxt : x ≤ (t : ℝ) := hxN.trans (by exact_mod_cast hNt)
    simpa only [Nat.floor_natCast] using hx (t : ℝ) hxt
  refine ⟨Cπ + 1, by linarith, max N 2, ?_⟩
  intro X z hzN hzX hXz
  have hNz : N ≤ z := (le_max_left N 2).trans hzN
  have hz2 : 2 ≤ z := (le_max_right N 2).trans hzN
  have hNX : N ≤ X := hNz.trans hzX
  have hcardNat : (roughNumbersUpTo X z).card ≤ Nat.primeCounting X + 1 := by
    calc
      (roughNumbersUpTo X z).card ≤ (insert 1 (Nat.primesLE X)).card :=
        Finset.card_le_card (roughNumbersUpTo_subset_one_insert_primesLE hXz)
      _ = (Nat.primesLE X).card + 1 := by
        rw [Finset.card_insert_of_notMem (by
          intro h
          exact (Nat.prime_of_mem_primesLE h).ne_one rfl)]
      _ = Nat.primeCounting X + 1 := by simp
  have hcardReal : ((roughNumbersUpTo X z).card : ℝ) ≤
      (Nat.primeCounting X : ℝ) + 1 := by exact_mod_cast hcardNat
  have hlogZPos : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hlogXPos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogZX : Real.log (z : ℝ) ≤ Real.log (X : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (show (0 : ℝ) < (z : ℝ) by exact_mod_cast (show 0 < z by omega))
      (show (0 : ℝ) < (X : ℝ) by exact_mod_cast (show 0 < X by omega))
      (by exact_mod_cast hzX)
  have hprime : (Nat.primeCounting X : ℝ) ≤
      Cπ * (X : ℝ) / Real.log z := by
    calc
      (Nat.primeCounting X : ℝ) ≤ Cπ * (X : ℝ) / Real.log X := hcheb X hNX
      _ ≤ Cπ * (X : ℝ) / Real.log z := by
        apply (div_le_div_iff_of_pos_left ?_ hlogXPos hlogZPos).2 hlogZX
        exact mul_pos hCπ (by exact_mod_cast (show 0 < X by omega))
  have hone : (1 : ℝ) ≤ (X : ℝ) / Real.log z := by
    rw [le_div_iff₀ hlogZPos]
    simpa only [one_mul] using (show Real.log (z : ℝ) ≤ (X : ℝ) from calc
      Real.log (z : ℝ) ≤ (z : ℝ) := Real.log_le_self (by positivity)
      _ ≤ (X : ℝ) := by exact_mod_cast hzX)
  calc
    ((roughNumbersUpTo X z).card : ℝ) ≤
        (Nat.primeCounting X : ℝ) + 1 := hcardReal
    _ ≤ Cπ * (X : ℝ) / Real.log z + (X : ℝ) / Real.log z :=
      add_le_add hprime hone
    _ = (Cπ + 1) * (X : ℝ) / Real.log z := by ring

/-- Uniform rough-number upper sieve for every `X ≥ z`.  Below `z²` a
rough number other than `1` is prime; above `z²` the Selberg estimate
applies. -/
theorem exists_roughNumbersUpTo_card_le_div_log :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ {X z : ℕ},
      N₀ ≤ z → z ≤ X →
      ((roughNumbersUpTo X z).card : ℝ) ≤
        C * (X : ℝ) / Real.log z := by
  obtain ⟨C₁, hC₁, N₁, hsmall⟩ :=
    exists_roughNumbersUpTo_card_le_div_log_of_lt_sq
  obtain ⟨C₂, hC₂, N₂, hlarge⟩ :=
    exists_roughNumbersUpTo_card_le_div_log_of_sq_le
  refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁ (le_max_left _ _),
    max (max N₁ N₂) 2, ?_⟩
  intro X z hz hzX
  have hN₁z : N₁ ≤ z :=
    (le_max_left N₁ N₂).trans (le_max_left (max N₁ N₂) 2) |>.trans hz
  have hN₂z : N₂ ≤ z :=
    (le_max_right N₁ N₂).trans (le_max_left (max N₁ N₂) 2) |>.trans hz
  have hzTwo : 2 ≤ z := (le_max_right (max N₁ N₂) 2).trans hz
  have hlogPos : 0 < Real.log (z : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  by_cases hsq : z ^ 2 ≤ X
  · calc
      ((roughNumbersUpTo X z).card : ℝ) ≤ C₂ * (X : ℝ) / Real.log z :=
        hlarge hN₂z hsq
      _ ≤ max C₁ C₂ * (X : ℝ) / Real.log z := by
        gcongr
        exact le_max_right C₁ C₂
  · have hlt : X < z ^ 2 := by omega
    calc
      ((roughNumbersUpTo X z).card : ℝ) ≤ C₁ * (X : ℝ) / Real.log z :=
        hsmall hN₁z hzX hlt
      _ ≤ max C₁ C₂ * (X : ℝ) / Real.log z := by
        gcongr
        exact le_max_left C₁ C₂

/-! ## Reciprocal squarefull tail -/

private theorem inv_sq_le_inv_pred_sub_inv {n : ℕ} (hn : 2 ≤ n) :
    ((n : ℝ) ^ 2)⁻¹ ≤ ((n - 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpredR : (0 : ℝ) < (n - 1 : ℕ) := by
    exact_mod_cast (by omega : 0 < n - 1)
  have hnTwo : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnsub : (n : ℝ) - 1 ≠ 0 := by nlinarith
  have heq : ((n - 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹ =
      ((n : ℝ) * (n - 1 : ℕ))⁻¹ := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    field_simp [hnR.ne', hpredR.ne', hnsub]
    ring
  rw [heq]
  refine (inv_le_inv₀ (sq_pos_of_pos hnR) (mul_pos hnR hpredR)).2 ?_
  nlinarith [show ((n - 1 : ℕ) : ℝ) ≤ n by
    exact_mod_cast (by omega : n - 1 ≤ n)]

private theorem sum_Icc_inv_sq_le_inv (L A : ℕ) (hL : 1 ≤ L) :
    (∑ n ∈ Finset.Icc (L + 1) A, ((n : ℝ) ^ 2)⁻¹) ≤ (L : ℝ)⁻¹ := by
  by_cases hLA : L < A
  · have hrewrite :
        (∑ n ∈ Finset.Icc (L + 1) A, ((n : ℝ) ^ 2)⁻¹) =
          ∑ i ∈ Finset.range (A - L),
            ((((L + i + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
      have hsets : Finset.Icc (L + 1) A = Finset.Ico (L + 1) (A + 1) := by
        ext n
        simp
      rw [hsets, Finset.sum_Ico_eq_sum_range]
      have hlen : A + 1 - (L + 1) = A - L := by omega
      rw [hlen]
      apply Finset.sum_congr rfl
      intro i hi
      congr 3
      omega
    rw [hrewrite]
    calc
      (∑ i ∈ Finset.range (A - L),
          ((((L + i + 1 : ℕ) : ℝ) ^ 2)⁻¹)) ≤
          ∑ i ∈ Finset.range (A - L),
            (((L + i : ℕ) : ℝ)⁻¹ -
              ((L + i + 1 : ℕ) : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa [Nat.add_assoc] using
          (inv_sq_le_inv_pred_sub_inv (n := L + i + 1) (by omega))
      _ = (L : ℝ)⁻¹ - (A : ℝ)⁻¹ := by
        change (Finset.range (A - L)).sum (fun i ↦
          (fun j : ℕ ↦ ((L + j : ℕ) : ℝ)⁻¹) i -
            (fun j : ℕ ↦ ((L + j : ℕ) : ℝ)⁻¹) (i + 1)) = _
        rw [Finset.sum_range_sub']
        simp [Nat.add_sub_of_le hLA.le]
      _ ≤ (L : ℝ)⁻¹ := sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg A))
  · have hempty : Finset.Icc (L + 1) A = ∅ := by
      rw [Finset.Icc_eq_empty]
      omega
    simp [hempty, inv_nonneg.mpr (show (0 : ℝ) ≤ L by positivity)]

private theorem sum_Icc_one_inv_sq_le_two (A : ℕ) :
    (∑ n ∈ Finset.Icc 1 A, ((n : ℝ) ^ 2)⁻¹) ≤ 2 := by
  by_cases hA : 1 ≤ A
  · have hset : Finset.Icc 1 A = insert 1 (Finset.Icc 2 A) := by
      ext n
      simp
      omega
    rw [hset, Finset.sum_insert (by simp)]
    norm_num
    linarith [sum_Icc_inv_sq_le_inv 1 A (by omega)]
  · have : Finset.Icc 1 A = ∅ := by
      rw [Finset.Icc_eq_empty]
      omega
    simp [this]

private noncomputable def squareCubeInnerTail (T c A : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 A,
    if T < a ^ 2 * c then (((a ^ 2 * c : ℕ) : ℝ))⁻¹ else 0

private theorem squareCubeInnerTail_factor {T c A : ℕ} :
    squareCubeInnerTail T c A =
      (c : ℝ)⁻¹ *
        ∑ a ∈ (Finset.Icc 1 A).filter (fun a ↦ T < a ^ 2 * c),
          ((a : ℝ) ^ 2)⁻¹ := by
  classical
  unfold squareCubeInnerTail
  rw [← Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Nat.cast_mul, Nat.cast_pow]
  ring

private theorem squareCubeInnerTail_le {T c A : ℕ}
    (hT : 0 < T) (hc : 0 < c) :
    squareCubeInnerTail T c A ≤
      4 / (Real.sqrt (T : ℝ) * Real.sqrt (c : ℝ)) := by
  classical
  have hTR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hsqrtT : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hTR
  have hsqrtC : 0 < Real.sqrt (c : ℝ) := Real.sqrt_pos.2 hcR
  rw [squareCubeInnerTail_factor]
  by_cases hcT : c ≤ T
  · let q := T / c
    let s := Nat.sqrt q
    have hq : 0 < q := Nat.div_pos hcT hc
    have hs : 0 < s := Nat.sqrt_pos.2 hq
    have hsubset :
        (Finset.Icc 1 A).filter (fun a ↦ T < a ^ 2 * c) ⊆
          Finset.Icc (s + 1) A := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha ⊢
      refine ⟨?_, ha.1.2⟩
      have hqa : q < a ^ 2 := by
        by_contra hnot
        have haql : a ^ 2 ≤ q := by omega
        have hmul : a ^ 2 * c ≤ q * c := Nat.mul_le_mul_right c haql
        exact (not_lt_of_ge (hmul.trans (Nat.div_mul_le_self T c))) ha.2
      exact Nat.succ_le_iff.mpr (Nat.sqrt_lt'.2 hqa)
    have hsum :
        (∑ a ∈ (Finset.Icc 1 A).filter (fun a ↦ T < a ^ 2 * c),
            ((a : ℝ) ^ 2)⁻¹) ≤ (s : ℝ)⁻¹ := by
      calc
        (∑ a ∈ (Finset.Icc 1 A).filter (fun a ↦ T < a ^ 2 * c),
            ((a : ℝ) ^ 2)⁻¹) ≤
            ∑ a ∈ Finset.Icc (s + 1) A, ((a : ℝ) ^ 2)⁻¹ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro a ha _
          positivity
        _ ≤ (s : ℝ)⁻¹ := sum_Icc_inv_sq_le_inv s A hs
    have hqUpper : q ≤ 4 * s ^ 2 := by
      have hqs : q < (s + 1) ^ 2 := Nat.sqrt_lt'.1 (Nat.lt_succ_self s)
      nlinarith
    have hTq : T < c * (q + 1) := Nat.lt_mul_div_succ T hc
    have hTbound : T ≤ 16 * c * s ^ 2 := by
      nlinarith
    have hdenom : Real.sqrt (T : ℝ) * Real.sqrt (c : ℝ) ≤
        4 * ((c : ℝ) * (s : ℝ)) := by
      have hsqrtT2 := Real.sq_sqrt hTR.le
      have hsqrtC2 := Real.sq_sqrt hcR.le
      have hTboundR : (T : ℝ) ≤ 16 * (c : ℝ) * (s : ℝ) ^ 2 := by
        exact_mod_cast hTbound
      have hsq :
          (Real.sqrt (T : ℝ) * Real.sqrt (c : ℝ)) ^ 2 ≤
            (4 * ((c : ℝ) * (s : ℝ))) ^ 2 := by
        rw [mul_pow, hsqrtT2, hsqrtC2]
        nlinarith
      nlinarith [sq_nonneg
        (Real.sqrt (T : ℝ) * Real.sqrt (c : ℝ) -
          4 * ((c : ℝ) * (s : ℝ)))]
    calc
      (c : ℝ)⁻¹ *
          ∑ a ∈ (Finset.Icc 1 A).filter (fun a ↦ T < a ^ 2 * c),
            ((a : ℝ) ^ 2)⁻¹ ≤ (c : ℝ)⁻¹ * (s : ℝ)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hcR.le)
      _ = 1 / ((c : ℝ) * (s : ℝ)) := by
        field_simp [show (c : ℝ) ≠ 0 by positivity,
          show (s : ℝ) ≠ 0 by positivity]
      _ ≤ 4 / (Real.sqrt (T : ℝ) * Real.sqrt (c : ℝ)) := by
        rw [div_le_div_iff₀ (mul_pos hcR (by exact_mod_cast hs))
          (mul_pos hsqrtT hsqrtC)]
        simpa using hdenom
  · have hTc : T < c := lt_of_not_ge hcT
    have hsumAll := sum_Icc_one_inv_sq_le_two A
    have hsumFilter :
        (∑ a ∈ (Finset.Icc 1 A).filter (fun a ↦ T < a ^ 2 * c),
            ((a : ℝ) ^ 2)⁻¹) ≤ 2 := by
      calc
        (∑ a ∈ (Finset.Icc 1 A).filter (fun a ↦ T < a ^ 2 * c),
            ((a : ℝ) ^ 2)⁻¹) ≤
            ∑ a ∈ Finset.Icc 1 A, ((a : ℝ) ^ 2)⁻¹ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro a ha _
          positivity
        _ ≤ 2 := hsumAll
    have hsqrtLe : Real.sqrt (T : ℝ) ≤ Real.sqrt (c : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hTc.le)
    have hdenom : Real.sqrt (T : ℝ) * Real.sqrt (c : ℝ) ≤ 2 * (c : ℝ) := by
      calc
        Real.sqrt (T : ℝ) * Real.sqrt (c : ℝ) ≤
            Real.sqrt (c : ℝ) * Real.sqrt (c : ℝ) := by gcongr
        _ = (c : ℝ) := Real.mul_self_sqrt hcR.le
        _ ≤ 2 * (c : ℝ) := by nlinarith
    calc
      (c : ℝ)⁻¹ *
          ∑ a ∈ (Finset.Icc 1 A).filter (fun a ↦ T < a ^ 2 * c),
            ((a : ℝ) ^ 2)⁻¹ ≤ (c : ℝ)⁻¹ * 2 := by
        exact mul_le_mul_of_nonneg_left hsumFilter (inv_nonneg.mpr hcR.le)
      _ = 2 / (c : ℝ) := by field_simp
      _ ≤ 4 / (Real.sqrt (T : ℝ) * Real.sqrt (c : ℝ)) := by
        rw [div_le_div_iff₀ hcR (mul_pos hsqrtT hsqrtC)]
        nlinarith

private theorem summable_inv_sqrt_cube :
    Summable (fun b : ℕ => 1 / Real.sqrt ((b : ℝ) ^ 3)) := by
  have h := Real.summable_one_div_nat_rpow.mpr
    (show (1 : ℝ) < 3 / 2 by norm_num)
  apply h.congr
  intro b
  congr 2
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast]
  rw [← Real.rpow_mul (Nat.cast_nonneg b)]
  norm_num

/-- An absolute constant dominating the convergent cube-root series. -/
noncomputable def squarefullTailConstant : ℝ :=
  4 * (1 + ∑' b : ℕ, 1 / Real.sqrt ((b : ℝ) ^ 3))

theorem squarefullTailConstant_pos : 0 < squarefullTailConstant := by
  have hnonneg : 0 ≤ ∑' b : ℕ, 1 / Real.sqrt ((b : ℝ) ^ 3) :=
    tsum_nonneg fun _ ↦ by positivity
  unfold squarefullTailConstant
  positivity

private noncomputable def squareCubePairTail (T R : ℕ) : ℝ :=
  ∑ b ∈ Finset.Icc 1 R, squareCubeInnerTail T (b ^ 3) R

private theorem squareCubePairTail_le {T R : ℕ} (hT : 0 < T) :
    squareCubePairTail T R ≤ squarefullTailConstant / Real.sqrt T := by
  have hsqrtT : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hT)
  have hfinite :
      (∑ b ∈ Finset.Icc 1 R, 1 / Real.sqrt ((b : ℝ) ^ 3)) ≤
        ∑' b : ℕ, 1 / Real.sqrt ((b : ℝ) ^ 3) := by
    exact summable_inv_sqrt_cube.sum_le_tsum (Finset.Icc 1 R)
      (fun _ _ ↦ by positivity)
  unfold squareCubePairTail
  calc
    (∑ b ∈ Finset.Icc 1 R, squareCubeInnerTail T (b ^ 3) R) ≤
        ∑ b ∈ Finset.Icc 1 R,
          4 / (Real.sqrt (T : ℝ) * Real.sqrt ((b ^ 3 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro b hb
      exact squareCubeInnerTail_le hT (pow_pos (by simp only [Finset.mem_Icc] at hb; omega) _)
    _ = (4 / Real.sqrt (T : ℝ)) *
        ∑ b ∈ Finset.Icc 1 R, 1 / Real.sqrt ((b : ℝ) ^ 3) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Nat.cast_pow]
      field_simp
    _ ≤ (4 / Real.sqrt (T : ℝ)) *
        (∑' b : ℕ, 1 / Real.sqrt ((b : ℝ) ^ 3)) := by
      exact mul_le_mul_of_nonneg_left hfinite (by positivity)
    _ ≤ squarefullTailConstant / Real.sqrt T := by
      unfold squarefullTailConstant
      have htsum : 0 ≤ ∑' b : ℕ, 1 / Real.sqrt ((b : ℝ) ^ 3) :=
        tsum_nonneg fun _ ↦ by positivity
      rw [div_eq_mul_inv]
      ring_nf
      nlinarith [inv_pos.mpr hsqrtT]

private def squarePartRaw (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)

private def cubePartRaw (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ (n.factorization p % 2)

private theorem squarePartRaw_sq_mul_cubePartRaw {n : ℕ} (hn : n ≠ 0) :
    squarePartRaw n ^ 2 * cubePartRaw n = n := by
  rw [squarePartRaw, cubePartRaw, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  calc
    ∏ p ∈ n.primeFactors,
        (p ^ (n.factorization p / 2)) ^ 2 *
          p ^ (n.factorization p % 2) =
        ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    _ = n := (Nat.prod_primeFactors_pow_factorization hn).symm

private theorem squarePartRaw_pos (n : ℕ) : 0 < squarePartRaw n := by
  unfold squarePartRaw
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primeFactors (by simpa using hp)).pos _

private theorem cubePartRaw_pos (n : ℕ) : 0 < cubePartRaw n := by
  unfold cubePartRaw
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primeFactors (by simpa using hp)).pos _

private theorem cubePartRaw_dvd_squarePartRaw {n : ℕ} (hn : Squarefull n) :
    cubePartRaw n ∣ squarePartRaw n := by
  unfold cubePartRaw squarePartRaw
  apply Finset.prod_dvd_prod_of_dvd
  intro p hp
  have hpMem : p ∈ n.primeFactors := by simpa using hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpMem
  have hpSq : p ^ 2 ∣ n := hn.2 p hpMem
  have htwo : 2 ≤ n.factorization p :=
    (hpPrime.pow_dvd_iff_le_factorization hn.1.ne').mp hpSq
  apply pow_dvd_pow p
  have hmod : n.factorization p % 2 < 2 := Nat.mod_lt _ (by omega)
  have hdiv : 1 ≤ n.factorization p / 2 := by omega
  omega

/-- The square coordinate in the canonical `a²b³` representation. -/
private def squarefullSquarePart (n : ℕ) : ℕ := squarePartRaw n / cubePartRaw n

/-- The cube coordinate in the canonical `a²b³` representation. -/
private def squarefullCubePart (n : ℕ) : ℕ := cubePartRaw n

private theorem squarefull_representation {n : ℕ} (hn : Squarefull n) :
    squarefullSquarePart n ^ 2 * squarefullCubePart n ^ 3 = n := by
  have hdiv := cubePartRaw_dvd_squarePartRaw hn
  have hab : squarePartRaw n / cubePartRaw n * cubePartRaw n = squarePartRaw n :=
    Nat.div_mul_cancel hdiv
  have hnrep := squarePartRaw_sq_mul_cubePartRaw hn.1.ne'
  change (squarePartRaw n / cubePartRaw n) ^ 2 * cubePartRaw n ^ 3 = n
  calc
    (squarePartRaw n / cubePartRaw n) ^ 2 * cubePartRaw n ^ 3 =
        (squarePartRaw n / cubePartRaw n * cubePartRaw n) ^ 2 *
          cubePartRaw n := by ring
    _ = squarePartRaw n ^ 2 * cubePartRaw n := by rw [hab]
    _ = n := hnrep

private theorem squarefull_parts_pos {n : ℕ} (hn : Squarefull n) :
    0 < squarefullSquarePart n ∧ 0 < squarefullCubePart n := by
  have hcpos := cubePartRaw_pos n
  have hspos := squarePartRaw_pos n
  have hdiv := cubePartRaw_dvd_squarePartRaw hn
  constructor
  · unfold squarefullSquarePart
    exact Nat.div_pos (Nat.le_of_dvd hspos hdiv) hcpos
  · exact hcpos

private def squarefullPair (n : ℕ) : ℕ × ℕ :=
  (squarefullCubePart n, squarefullSquarePart n)

private theorem squarefullPair_injective :
    Set.InjOn squarefullPair {n : ℕ | Squarefull n} := by
  intro m hm n hn hpair
  have hmrep := squarefull_representation hm
  have hnrep := squarefull_representation hn
  rw [← hmrep, ← hnrep]
  simpa [squarefullPair] using congrArg
    (fun p : ℕ × ℕ ↦ p.2 ^ 2 * p.1 ^ 3) hpair

/-- Finite reciprocal tail of positive squarefull integers in `(T,R]`. -/
noncomputable def squarefullReciprocalTail (T R : ℕ) : ℝ :=
  ∑ q ∈ squarefullTailSet R T, (q : ℝ)⁻¹

private noncomputable def squareCubePairs (T R : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 R).product (Finset.Icc 1 R)).filter fun ba ↦
    T < ba.2 ^ 2 * ba.1 ^ 3

private theorem squarefullPair_mem_squareCubePairs {T R q : ℕ}
    (hq : q ∈ squarefullTailSet R T) :
    squarefullPair q ∈ squareCubePairs T R := by
  rw [squarefullTailSet, Finset.mem_filter, mem_squarefullSet] at hq
  rcases hq with ⟨⟨hqPos, hqR, hqFull⟩, hTq⟩
  have hparts := squarefull_parts_pos hqFull
  have hrep := squarefull_representation hqFull
  have hcubeDvd : squarefullCubePart q ∣ q := by
    have hprod : squarefullCubePart q ∣
        squarefullSquarePart q ^ 2 * squarefullCubePart q ^ 3 :=
      dvd_mul_of_dvd_right
        (dvd_pow_self _ (by omega : (3 : ℕ) ≠ 0)) _
    simpa only [hrep] using hprod
  have hsquareDvd : squarefullSquarePart q ∣ q := by
    have hprod : squarefullSquarePart q ∣
        squarefullSquarePart q ^ 2 * squarefullCubePart q ^ 3 :=
      dvd_mul_of_dvd_left
        (dvd_pow_self _ (by omega : (2 : ℕ) ≠ 0)) _
    simpa only [hrep] using hprod
  have hcubeLe : squarefullCubePart q ≤ R :=
    (Nat.le_of_dvd hqPos hcubeDvd).trans hqR
  have hsquareLe : squarefullSquarePart q ≤ R :=
    (Nat.le_of_dvd hqPos hsquareDvd).trans hqR
  rw [squareCubePairs, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · apply Finset.mem_product.mpr
    exact ⟨by simp only [squarefullPair, Finset.mem_Icc]; omega,
      by simp only [squarefullPair, Finset.mem_Icc]; omega⟩
  · change T < squarefullSquarePart q ^ 2 * squarefullCubePart q ^ 3
    simpa [hrep] using hTq

private theorem squareCubePairs_sum_eq_pairTail (T R : ℕ) :
    (∑ ba ∈ squareCubePairs T R,
        (((ba.2 ^ 2 * ba.1 ^ 3 : ℕ) : ℝ))⁻¹) =
      squareCubePairTail T R := by
  classical
  unfold squareCubePairs squareCubePairTail squareCubeInnerTail
  rw [Finset.sum_filter]
  simpa [Nat.cast_mul, Nat.cast_pow, mul_comm] using
    (Finset.sum_product (Finset.Icc 1 R) (Finset.Icc 1 R)
    (fun ba : ℕ × ℕ ↦
      if T < ba.2 ^ 2 * ba.1 ^ 3 then
        (((ba.2 : ℝ) ^ 2))⁻¹ * (((ba.1 : ℝ) ^ 3))⁻¹ else 0))

/-- Sharp uniform reciprocal-tail estimate for squarefull integers. -/
theorem squarefullReciprocalTail_le {T R : ℕ} (hT : 0 < T) :
    squarefullReciprocalTail T R ≤
      squarefullTailConstant / Real.sqrt T := by
  classical
  have hinj : Set.InjOn squarefullPair
      (squarefullTailSet R T : Set ℕ) := by
    apply squarefullPair_injective.mono
    intro q hq
    change q ∈ squarefullTailSet R T at hq
    rw [squarefullTailSet, Finset.mem_filter, mem_squarefullSet] at hq
    exact hq.1.2.2
  calc
    squarefullReciprocalTail T R =
        ∑ q ∈ squarefullTailSet R T,
          ((((squarefullPair q).2 ^ 2 * (squarefullPair q).1 ^ 3 : ℕ) : ℝ))⁻¹ := by
      unfold squarefullReciprocalTail
      apply Finset.sum_congr rfl
      intro q hq
      rw [squarefullTailSet, Finset.mem_filter, mem_squarefullSet] at hq
      change (q : ℝ)⁻¹ =
        (((squarefullSquarePart q ^ 2 * squarefullCubePart q ^ 3 : ℕ) : ℝ))⁻¹
      rw [squarefull_representation hq.1.2.2]
    _ = ∑ ba ∈ (squarefullTailSet R T).image squarefullPair,
          (((ba.2 ^ 2 * ba.1 ^ 3 : ℕ) : ℝ))⁻¹ := by
      symm
      rw [Finset.sum_image]
      intro q hq q' hq' heq
      exact hinj (by simpa using hq) (by simpa using hq') heq
    _ ≤ ∑ ba ∈ squareCubePairs T R,
          (((ba.2 ^ 2 * ba.1 ^ 3 : ℕ) : ℝ))⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ba hba
        rw [Finset.mem_image] at hba
        obtain ⟨q, hq, rfl⟩ := hba
        exact squarefullPair_mem_squareCubePairs hq
      · intro ba hba _
        positivity
    _ = squareCubePairTail T R := squareCubePairs_sum_eq_pairTail T R
    _ ≤ squarefullTailConstant / Real.sqrt T := squareCubePairTail_le hT

/-- Big-O form of the squarefull reciprocal tail, uniform in the finite
upper endpoint. -/
theorem squarefullReciprocalTail_isBigO (R : ℕ) :
    (fun T : ℕ ↦ squarefullReciprocalTail T R) =O[atTop]
      (fun T : ℕ ↦ (Real.sqrt (T : ℝ))⁻¹) := by
  rw [isBigO_iff]
  refine ⟨squarefullTailConstant, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with T hT
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by unfold squarefullReciprocalTail; positivity),
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  simpa [div_eq_mul_inv] using squarefullReciprocalTail_le (R := R) (by omega : 0 < T)

end Erdos896.Ford
