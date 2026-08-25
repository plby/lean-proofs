import ErdosProblems.Erdos297.FactorDensity
import ErdosProblems.Erdos248.Scales
import Util.TaoTeravainen.Arithmetic

/-!
# Tao--Teräväinen: exact counting of excess multiplicity

The excess over distinct prime factors is exactly the number of proper
prime-power divisors. On a bounded interval this becomes a finite sum of
prime-power divisibility indicators, the input needed for the weighted second
moment.
-/

noncomputable section

open scoped ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators

namespace TaoTeravainen

local instance primePowerCountingDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

open Erdos297.FactorDensity

/-- The factorization excess agrees with the cardinality of the proper
prime-power divisor set. -/
theorem factorizationExcess_eq_card_properPrimePowerDivisors
    {n : ℕ} (hn : n ≠ 0) :
    factorizationExcess n = (properPrimePowerDivisors n).card := by
  have hsum := factorization_sum_eq_support_card_add_excess n
  rw [factorization_sum_eq_Omega,
    Omega_eq_omega_add_card_properPrimePowerDivisors hn] at hsum
  have hsupp : n.factorization.support.card = ω n := by
    rw [Nat.support_factorization, Erdos248.omega_eq_primeFactors_card]
  rw [hsupp] at hsum
  omega

/-- On a finite upper range, the excess multiplicity is the sum of the
proper-prime-power divisibility indicators. -/
theorem factorizationExcess_cast_eq_indicatorSum
    {B n : ℕ} (hn : n ∈ Finset.Icc 1 B) :
    (factorizationExcess n : ℝ) =
      ∑ q ∈ properPrimePowersUpTo B, if q ∣ n then (1 : ℝ) else 0 := by
  rw [factorizationExcess_eq_card_properPrimePowerDivisors
      (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1),
    properPrimePowerDivisors_eq_filter_upTo hn,
    Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, Finset.sum_filter]

/-- Every shift in the sieve interval and relevant range is below the
convenient common cutoff 3X. -/
theorem add_le_three_intervalStart_of_relevant
    {K n k : ℕ}
    (hn : n ∈ Finset.Ico (Erdos248.intervalStart K)
      (2 * Erdos248.intervalStart K))
    (hk : k ≤ Erdos248.intervalExponent K) :
    n + k ≤ 3 * Erdos248.intervalStart K := by
  have hn' := (Finset.mem_Ico.mp hn).2
  have hk' : k ≤ Erdos248.intervalStart K := by
    calc
      k ≤ Erdos248.intervalExponent K := hk
      _ ≤ 2 ^ Erdos248.intervalExponent K :=
        (Erdos248.intervalExponent K).lt_two_pow_self.le
      _ = Erdos248.intervalStart K := by
        rw [Erdos248.intervalStart]
  omega

/-- The exact excess count at a relevant shift is the finite indicator sum
over proper prime powers up to 3X. -/
theorem factorizationExcess_shift_cast_eq_indicatorSum
    {K n k : ℕ}
    (hn : n ∈ Finset.Ico (Erdos248.intervalStart K)
      (2 * Erdos248.intervalStart K))
    (hk : k ≤ Erdos248.intervalExponent K) :
    (factorizationExcess (n + k) : ℝ) =
      ∑ q ∈ properPrimePowersUpTo (3 * Erdos248.intervalStart K),
        if q ∣ n + k then (1 : ℝ) else 0 := by
  apply factorizationExcess_cast_eq_indicatorSum
  have hnpos : 0 < n :=
    (Erdos248.intervalStart_pos K).trans_le (Finset.mem_Ico.mp hn).1
  exact Finset.mem_Icc.mpr
    ⟨by omega, add_le_three_intervalStart_of_relevant hn hk⟩

/-- Prime/exponent pairs representing proper prime powers at most B. Using
pairs exposes the underlying prime needed by the Maynard transform. -/
def properPrimePowerIndices (B : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 2 B).product (Finset.Icc 2 B)).filter fun pa =>
    pa.1.Prime ∧ pa.1 ^ pa.2 ≤ B

theorem mem_properPrimePowerIndices_iff {B p a : ℕ} :
    (p, a) ∈ properPrimePowerIndices B ↔
      2 ≤ p ∧ p ≤ B ∧ 2 ≤ a ∧ a ≤ B ∧ p.Prime ∧ p ^ a ≤ B := by
  simp [properPrimePowerIndices, and_assoc, and_left_comm, and_comm]

/-- The power map from prime/exponent pairs hits exactly the proper prime
powers up to B. -/
theorem image_properPrimePowerIndices (B : ℕ) :
    (properPrimePowerIndices B).image (fun pa => pa.1 ^ pa.2) =
      properPrimePowersUpTo B := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨pa, hpa, rfl⟩ := Finset.mem_image.mp hq
    have hdata := mem_properPrimePowerIndices_iff.mp hpa
    rw [properPrimePowersUpTo, Finset.mem_filter]
    refine ⟨Finset.mem_Ioc.mpr ⟨?_, hdata.2.2.2.2.2⟩, ?_, ?_⟩
    · have hp2 : 2 ≤ pa.1 := hdata.1
      have ha2 : 2 ≤ pa.2 := hdata.2.2.1
      have hpow : 2 ^ 2 ≤ pa.1 ^ pa.2 := by
        calc
          2 ^ 2 ≤ pa.1 ^ 2 := Nat.pow_le_pow_left hp2 2
          _ ≤ pa.1 ^ pa.2 :=
            Nat.pow_le_pow_right (by omega) ha2
      omega
    · exact ⟨pa.1, pa.2, hdata.2.2.2.2.1.prime, by omega, rfl⟩
    · exact Nat.Prime.not_prime_pow hdata.2.2.1
  · intro hq
    have hqData := Finset.mem_filter.mp hq
    obtain ⟨p, a, hp, ha, hpow⟩ := hqData.2.1
    have hpNat : p.Prime := Nat.prime_iff.mpr hp
    have hqRange := Finset.mem_Ioc.mp hqData.1
    have ha2 : 2 ≤ a := by
      by_contra hnot
      have ha1 : a = 1 := by omega
      apply hqData.2.2
      rw [← hpow, ha1, pow_one]
      exact hpNat
    have hp2 : 2 ≤ p := hpNat.two_le
    have hpLe : p ≤ B := by
      calc
        p ≤ p ^ a := by
          have ha1 : 1 ≤ a := by omega
          exact Nat.le_pow ha1
        _ = q := hpow
        _ ≤ B := hqRange.2
    have haLe : a ≤ B := by
      calc
        a ≤ 2 ^ a := a.lt_two_pow_self.le
        _ ≤ p ^ a := Nat.pow_le_pow_left hp2 a
        _ = q := hpow
        _ ≤ B := hqRange.2
    apply Finset.mem_image.mpr
    refine ⟨(p, a), mem_properPrimePowerIndices_iff.mpr
      ⟨hp2, hpLe, ha2, haLe, hpNat, ?_⟩, hpow⟩
    simpa [hpow] using hqRange.2

/-- Distinct valid prime/exponent pairs represent distinct natural powers. -/
theorem properPrimePowerIndices_power_injective {B : ℕ} :
    Set.InjOn (fun pa : ℕ × ℕ => pa.1 ^ pa.2)
      (properPrimePowerIndices B) := by
  intro pa hpa qb hqb hpowe
  have hpaData := mem_properPrimePowerIndices_iff.mp hpa
  have hqbData := mem_properPrimePowerIndices_iff.mp hqb
  have hbase : pa.1 = qb.1 := by
    exact eq_of_prime_pow_eq hpaData.2.2.2.2.1.prime
      hqbData.2.2.2.2.1.prime (by omega) hpowe
  cases pa with
  | mk p a =>
    cases qb with
    | mk q b =>
      simp only at hbase hpaData hqbData hpowe ⊢
      subst q
      have hexp : a = b :=
        Nat.pow_right_injective hpaData.1 hpowe
      subst b
      rfl

/-- Reindex the proper-prime-power indicator sum by prime/exponent pairs. -/
theorem properPrimePower_indicatorSum_eq_indexSum (B n : ℕ) :
    (∑ q ∈ properPrimePowersUpTo B,
        if q ∣ n then (1 : ℝ) else 0) =
      ∑ pa ∈ properPrimePowerIndices B,
        if pa.1 ^ pa.2 ∣ n then (1 : ℝ) else 0 := by
  rw [← image_properPrimePowerIndices B]
  exact Finset.sum_image properPrimePowerIndices_power_injective

end TaoTeravainen
