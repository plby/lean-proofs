/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.PrimeReciprocalBound
import ErdosProblems.Erdos387.RoughIntervalEstimate

/-!
# Truncated Brun approximation of a rough interval

For exponential sums over a `z`-rough variable we replace the roughness
indicator by a finite even Brun truncation.  The resulting divisor sums are
ordinary interval sums and can be completed.  This file constructs the
one-dimensional interval sieve and records explicit uniform endpoint bounds.
-/

namespace Erdos387

open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.omega

open Finset Nat Real ArithmeticFunction

namespace RoughBrun

/-- The elementary one-dimensional sieve on the natural interval `(A,U]`.
Its local density is `1/p`, realized as `binomialSieveNu 1`. -/
noncomputable def intervalSieve (z A U : ℕ) : BoundingSieve := by
  classical
  exact
    { support := Finset.Ioc A U
      prodPrimes := sievePrimeProduct 1 z
      prodPrimes_squarefree := sievePrimeProduct_squarefree 1 z
      weights := fun _ => 1
      weights_nonneg := fun _ => by norm_num
      totalMass := (Finset.Ioc A U).card
      nu := binomialSieveNu 1
      nu_mult := binomialSieveNu_mult 1
      nu_pos_of_prime := by
        intro p hp _hpDvd
        rw [binomialSieveNu_prime hp]
        exact div_pos (by norm_num) (by exact_mod_cast hp.pos)
      nu_lt_one_of_prime := by
        intro p hp _hpDvd
        rw [binomialSieveNu_prime hp]
        exact (div_lt_one (by exact_mod_cast hp.pos)).mpr
          (by exact_mod_cast hp.one_lt) }

/-- Coprimality with the product of all primes below `z` is exactly
`z`-roughness. -/
theorem coprime_sievePrimeProduct_one_iff_rough {z n : ℕ} :
    Nat.Coprime (sievePrimeProduct 1 z) n ↔ IsZRough z n := by
  constructor
  · intro hcop p hp hpz hpn
    have hpMem : p ∈ sievePrimes 1 z :=
      mem_sievePrimes.mpr ⟨hp, hp.one_lt, hpz⟩
    have hpProd : p ∣ sievePrimeProduct 1 z := by
      exact Finset.dvd_prod_of_mem id hpMem
    have hpGcd : p ∣ Nat.gcd (sievePrimeProduct 1 z) n :=
      Nat.dvd_gcd hpProd hpn
    have hpOne : p ∣ 1 := by simpa [hcop.gcd_eq_one] using hpGcd
    exact hp.ne_one (Nat.dvd_one.mp hpOne)
  · intro hrough
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hgcd
    obtain ⟨p, hp, hpDvd⟩ := Nat.exists_prime_and_dvd hgcd
    have hpProd : p ∣ sievePrimeProduct 1 z :=
      hpDvd.trans (Nat.gcd_dvd_left _ _)
    have hpMem := mem_sievePrimes.mp
      (prime_mem_sievePrimes_of_dvd_product hp hpProd)
    exact hrough p hp hpMem.2.2
      (hpDvd.trans (Nat.gcd_dvd_right _ _))

theorem intervalSieve_siftedSum (z A U : ℕ) :
    (intervalSieve z A U).siftedSum =
      ((RoughHarmonic.roughPositiveIoc z A U).card : ℝ) := by
  classical
  rw [BoundingSieve.siftedSum]
  change (∑ d ∈ Finset.Ioc A U,
      if Nat.Coprime (sievePrimeProduct 1 z) d then (1 : ℝ) else 0) = _
  simp_rw [coprime_sievePrimeProduct_one_iff_rough]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rfl

/-- Multiples of `d` in `(A,U]` are one modular preimage. -/
theorem intervalSieve_multSum_eq_card_modularPreimage
    {z A U d : ℕ} (hd : 0 < d) :
    (intervalSieve z A U).multSum d =
      ((modularPreimageIoc A U d {0}).card : ℝ) := by
  classical
  rw [BoundingSieve.multSum]
  change (∑ n ∈ Finset.Ioc A U, if d ∣ n then (1 : ℝ) else 0) = _
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext n
  simp only [Finset.mem_filter, modularPreimageIoc, Finset.mem_singleton]
  rw [Nat.dvd_iff_mod_eq_zero]

theorem binomialSieveNu_one_squarefree {d : ℕ} (hd : Squarefree d) :
    binomialSieveNu 1 d = (d : ℝ)⁻¹ := by
  rw [binomialSieveNu_squarefree hd]
  simp

/-- Every sieve divisor has interval-count discrepancy at most two. -/
theorem intervalSieve_abs_rem_le_two
    {z A U d : ℕ} (hAU : A ≤ U)
    (hd : d ∣ sievePrimeProduct 1 z) :
    |(intervalSieve z A U).rem d| ≤ 2 := by
  have hdPos : 0 < d := pos_of_dvd_sievePrimeProduct hd
  have hsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd (sievePrimeProduct_squarefree 1 z)
  have hcount := abs_card_modularPreimageIoc_sub_density
    hAU hdPos ({0} : Finset ℕ) (by
      intro a ha
      simp only [Finset.mem_singleton] at ha
      subst a
      exact hdPos)
  rw [BoundingSieve.rem]
  change
    |(intervalSieve z A U).multSum d -
      binomialSieveNu 1 d * ((Finset.Ioc A U).card : ℝ)| ≤ 2
  rw [intervalSieve_multSum_eq_card_modularPreimage hdPos]
  rw [binomialSieveNu_one_squarefree hsq]
  have hcard : (Finset.Ioc A U).card = U - A := by simp
  rw [hcard]
  simpa [div_eq_mul_inv, mul_comm] using hcount

/-- The support of either level-`L` Brun weight contains at most `z^L+1`
sieve divisors. -/
theorem card_intervalBrunSupport_le {z L : ℕ} (hz : 1 ≤ z) :
    ((sievePrimeProduct 1 z).divisors.filter fun d =>
      d.primeFactors.card ≤ L).card ≤ z ^ L + 1 := by
  exact card_brunSupport_le (k := 1) hz

/-- Explicit endpoint-error bound for an interval Brun truncation. -/
theorem intervalSieve_brunErrSum_le
    {z A U L : ℕ} (hAU : A ≤ U) (hz : 1 ≤ z) :
    (intervalSieve z A U).errSum (brunUpperWeight L) ≤
      (2 : ℝ) * (z ^ L + 1 : ℕ) := by
  let s := intervalSieve z A U
  rw [BoundingSieve.errSum]
  calc
    (∑ d ∈ (sievePrimeProduct 1 z).divisors,
        |brunUpperWeight L d| * |s.rem d|) ≤
        ∑ d ∈ (sievePrimeProduct 1 z).divisors,
          if d.primeFactors.card ≤ L then 2 else 0 := by
      apply Finset.sum_le_sum
      intro d hdmem
      by_cases hdL : d.primeFactors.card ≤ L
      · rw [if_pos hdL]
        have hddiv := (Nat.mem_divisors.mp hdmem).1
        calc
          |brunUpperWeight L d| * |s.rem d| ≤ 1 * |s.rem d| := by
            gcongr
            exact abs_brunUpperWeight_le_one L d
          _ ≤ 2 := by
            simpa [s] using intervalSieve_abs_rem_le_two hAU hddiv
      · rw [if_neg hdL]
        have hzero : brunUpperWeight L d = 0 := by
          unfold brunUpperWeight
          rw [if_neg]
          simpa [cardDistinctFactors_eq_primeFactors_card] using hdL
        simp [hzero]
    _ = (((sievePrimeProduct 1 z).divisors.filter fun d =>
          d.primeFactors.card ≤ L).card : ℝ) * 2 := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (z ^ L + 1 : ℕ) * 2 := by
      gcongr
      exact_mod_cast card_intervalBrunSupport_le hz (L := L)
    _ = (2 : ℝ) * (z ^ L + 1 : ℕ) := by ring

theorem intervalSieve_brunLowerErrSum_le
    {z A U L : ℕ} (hAU : A ≤ U) (hz : 1 ≤ z) :
    (intervalSieve z A U).errSum (brunLowerWeight L) ≤
      (2 : ℝ) * (z ^ L + 1 : ℕ) := by
  change (intervalSieve z A U).errSum (brunUpperWeight L) ≤ _
  exact intervalSieve_brunErrSum_le hAU hz

/-- Real indicator of `z`-roughness. -/
def roughIndicator (z n : ℕ) : ℝ :=
  if IsZRough z n then 1 else 0

/-- The divisor-sum approximation furnished by an even Brun weight. -/
noncomputable def upperApproximation (z L n : ℕ) : ℝ := by
  classical
  exact ∑ d ∈ (sievePrimeProduct 1 z).divisors,
    if d ∣ n then brunUpperWeight L d else 0

theorem upperApproximation_eq_gcd_divisorSum
    (z L n : ℕ) :
    upperApproximation z L n =
      ∑ d ∈ (Nat.gcd (sievePrimeProduct 1 z) n).divisors,
        brunUpperWeight L d := by
  classical
  unfold upperApproximation
  rw [← Finset.sum_filter]
  congr 1
  rw [← divisors_filter_dvd_of_dvd
    (sievePrimeProduct_squarefree 1 z).ne_zero
    (Nat.gcd_dvd_left _ _)]
  ext d
  simp only [Finset.mem_filter]
  rw [dvd_gcd_iff]
  tauto

/-- An even Brun approximation pointwise majorizes the roughness
indicator. -/
theorem roughIndicator_le_upperApproximation
    {z L n : ℕ} (hL : Even L) :
    roughIndicator z n ≤ upperApproximation z L n := by
  let s := intervalSieve z 0 0
  have hupper := brunUpperWeight_isUpperOnProdPrimes s hL
    (Nat.gcd (sievePrimeProduct 1 z) n) (Nat.gcd_dvd_left _ _)
  rw [upperApproximation_eq_gcd_divisorSum]
  change roughIndicator z n ≤ _
  have hindicator : roughIndicator z n =
      if Nat.gcd (sievePrimeProduct 1 z) n = 1 then 1 else 0 := by
    unfold roughIndicator
    rw [← Nat.coprime_iff_gcd_eq_one,
      coprime_sievePrimeProduct_one_iff_rough]
  rw [hindicator]
  exact hupper

/-- Summing the divisor approximation over the interval interchanges the
two finite sums and produces the abstract multiple sums. -/
theorem sum_upperApproximation_eq_multipleSum
    (z A U L : ℕ) :
    (∑ n ∈ Finset.Ioc A U, upperApproximation z L n) =
      ∑ d ∈ (sievePrimeProduct 1 z).divisors,
        brunUpperWeight L d * (intervalSieve z A U).multSum d := by
  classical
  unfold upperApproximation
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [BoundingSieve.multSum, Finset.mul_sum]
  change (∑ n ∈ Finset.Ioc A U,
      if d ∣ n then brunUpperWeight L d else 0) =
    ∑ n ∈ Finset.Ioc A U,
      brunUpperWeight L d * if d ∣ n then 1 else 0
  apply Finset.sum_congr rfl
  intro n _hn
  split <;> simp_all

theorem sum_roughIndicator_eq_siftedSum (z A U : ℕ) :
    (∑ n ∈ Finset.Ioc A U, roughIndicator z n) =
      (intervalSieve z A U).siftedSum := by
  rw [intervalSieve_siftedSum]
  unfold roughIndicator RoughHarmonic.roughPositiveIoc
  rw [← Finset.sum_filter]
  simp

/-- The divisor-weighted multiple sum equals its main term plus the signed
remainder sum. -/
theorem multipleSum_eq_main_add_signedRemainder
    (z A U L : ℕ) :
    (∑ d ∈ (sievePrimeProduct 1 z).divisors,
        brunUpperWeight L d * (intervalSieve z A U).multSum d) =
      (intervalSieve z A U).totalMass *
          (intervalSieve z A U).mainSum (brunUpperWeight L) +
        ∑ d ∈ (sievePrimeProduct 1 z).divisors,
          brunUpperWeight L d * (intervalSieve z A U).rem d := by
  rw [BoundingSieve.mainSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [BoundingSieve.multSum_eq_main_err]
  ring

/-- The total `L¹` loss of replacing exact roughness by an even Brun
truncation is controlled by the two adjacent omitted tails and explicit
interval endpoints. -/
theorem sum_upperApproximation_sub_roughIndicator_le
    {z A U Lminus Lplus : ℕ} (hAU : A ≤ U) (hz : 1 ≤ z)
    (hminus : Odd Lminus) (hplus : Even Lplus) :
    (∑ n ∈ Finset.Ioc A U,
        (upperApproximation z Lplus n - roughIndicator z n)) ≤
      ((Finset.Ioc A U).card : ℝ) *
        (brunSubsetTail (sievePrimeProduct 1 z).primeFactors
            (fun p => binomialSieveNu 1 p) Lplus +
          brunSubsetTail (sievePrimeProduct 1 z).primeFactors
            (fun p => binomialSieveNu 1 p) Lminus) +
        2 * (z ^ Lplus + 1 : ℕ) + 2 * (z ^ Lminus + 1 : ℕ) := by
  let s := intervalSieve z A U
  let E := finiteEulerProduct (sievePrimeProduct 1 z).primeFactors
    (fun p => binomialSieveNu 1 p)
  let Tplus := brunSubsetTail (sievePrimeProduct 1 z).primeFactors
    (fun p => binomialSieveNu 1 p) Lplus
  let Tminus := brunSubsetTail (sievePrimeProduct 1 z).primeFactors
    (fun p => binomialSieveNu 1 p) Lminus
  have hsumUpper := multipleSum_eq_main_add_signedRemainder z A U Lplus
  have hsiftedLower := BoundingSieve.totalMass_mainSum_sub_errSum_le_siftedSum
    (s := s) (brunLowerWeight Lminus)
      (brunLowerWeight_isLowerOnProdPrimes s hminus)
  have hremUpper :
      (∑ d ∈ (sievePrimeProduct 1 z).divisors,
          brunUpperWeight Lplus d * s.rem d) ≤
        s.errSum (brunUpperWeight Lplus) := by
    rw [BoundingSieve.errSum]
    apply Finset.sum_le_sum
    intro d _hd
    rw [← abs_mul]
    exact le_abs_self _
  have hmainPlus :=
    boundingSieve_abs_mainSum_brunUpperWeight_sub_euler_le s Lplus
  have hmainMinus :=
    boundingSieve_abs_mainSum_brunLowerWeight_sub_euler_le s Lminus
  have hmainDiff :
      s.mainSum (brunUpperWeight Lplus) -
          s.mainSum (brunLowerWeight Lminus) ≤ Tplus + Tminus := by
    have hp := (abs_le.mp hmainPlus)
    have hm := (abs_le.mp hmainMinus)
    change |s.mainSum (brunUpperWeight Lplus) - E| ≤ Tplus at hmainPlus
    change |s.mainSum (brunLowerWeight Lminus) - E| ≤ Tminus at hmainMinus
    have hp' := (abs_le.mp hmainPlus).2
    have hm' := (abs_le.mp hmainMinus).1
    linarith
  have hmass : 0 ≤ s.totalMass := by
    change 0 ≤ ((Finset.Ioc A U).card : ℝ)
    positivity
  have herrPlus := intervalSieve_brunErrSum_le hAU hz
    (L := Lplus)
  have herrMinus := intervalSieve_brunLowerErrSum_le hAU hz
    (L := Lminus)
  rw [Finset.sum_sub_distrib, sum_upperApproximation_eq_multipleSum,
    sum_roughIndicator_eq_siftedSum]
  change _ ≤ ((Finset.Ioc A U).card : ℝ) * (Tplus + Tminus) + _
  change s.siftedSum ≥
      s.totalMass * s.mainSum (brunLowerWeight Lminus) -
        s.errSum (brunLowerWeight Lminus) at hsiftedLower
  calc
    (∑ d ∈ (sievePrimeProduct 1 z).divisors,
          brunUpperWeight Lplus d * s.multSum d) - s.siftedSum ≤
        (s.totalMass * s.mainSum (brunUpperWeight Lplus) +
            s.errSum (brunUpperWeight Lplus)) -
          (s.totalMass * s.mainSum (brunLowerWeight Lminus) -
            s.errSum (brunLowerWeight Lminus)) := by
      rw [hsumUpper]
      linarith
    _ = s.totalMass *
          (s.mainSum (brunUpperWeight Lplus) -
            s.mainSum (brunLowerWeight Lminus)) +
          s.errSum (brunUpperWeight Lplus) +
          s.errSum (brunLowerWeight Lminus) := by ring
    _ ≤ s.totalMass * (Tplus + Tminus) +
          (2 * (z ^ Lplus + 1 : ℕ)) +
          (2 * (z ^ Lminus + 1 : ℕ)) := by
      gcongr
    _ = ((Finset.Ioc A U).card : ℝ) * (Tplus + Tminus) +
          2 * (z ^ Lplus + 1 : ℕ) +
          2 * (z ^ Lminus + 1 : ℕ) := by rfl

end RoughBrun

end Erdos387
