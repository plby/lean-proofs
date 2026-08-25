import Util.TaoTeravainen.PrimePowerAbsorbed

/-!
# Tao--Teräväinen: deterministic prime-power truncation

The sieve only sees proper prime powers below its first radius.  This file
shows that, for integers below the corresponding hundred-and-first power,
the omitted multiplicity can be paid for by a fixed multiple of the number
of distinct prime factors.
-/

noncomputable section

open scoped ArithmeticFunction.omega ArithmeticFunction.Omega BigOperators

namespace TaoTeravainen

local instance primePowerTruncationDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Number of proper prime-power divisors represented by the finite index
set at cutoff `J`. -/
def truncatedProperPrimePowerCount (J n : ℕ) : ℕ :=
  ∑ pa ∈ properPrimePowerIndices J,
    if pa.1 ^ pa.2 ∣ n then 1 else 0

/-- The part of the truncated count carried by one fixed base prime. -/
def baseTruncatedPrimePowerCount (J n p : ℕ) : ℕ :=
  ∑ pa ∈ (properPrimePowerIndices J).filter (fun pa => pa.1 = p),
    if pa.1 ^ pa.2 ∣ n then 1 else 0

theorem baseTruncatedPrimePowerCount_le_truncated
    (J n p : ℕ) :
    baseTruncatedPrimePowerCount J n p ≤
      truncatedProperPrimePowerCount J n := by
  unfold baseTruncatedPrimePowerCount truncatedProperPrimePowerCount
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro pa hpa hnot
  split_ifs <;> omega

/-- A single factorization coordinate is bounded by its truncated
proper-power contribution plus one fixed allowance for the base prime. -/
theorem factorization_le_threehundredthree_mul_one_add_baseTruncated
    {J n p : ℕ} (hJ : 1 < J) (hn0 : n ≠ 0)
    (hsize : n < J ^ 101) (hpmem : p ∈ n.factorization.support) :
    n.factorization p ≤
      303 * (1 + baseTruncatedPrimePowerCount J n p) := by
  have hpmem' : p ∈ n.primeFactors := by
    simpa [Nat.support_factorization] using hpmem
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem'
  let e := n.factorization p
  let q := e / 101
  have hqmul : q * 101 ≤ e := by
    dsimp [q]
    exact Nat.div_mul_le_self e 101
  have helast : e < (q + 1) * 101 := by
    apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 101)).mp
    dsimp [q]
    exact Nat.lt_succ_self _
  by_cases hq2 : 2 ≤ q
  · have hq1 : 1 ≤ q := by omega
    have hpq_dvd : p ^ (q * 101) ∣ n := by
      exact (hp.pow_dvd_iff_le_factorization hn0).2 (by simpa [e] using hqmul)
    have hpq_le_n : p ^ (q * 101) ≤ n :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpq_dvd
    have hpq_lt_J : p ^ q < J := by
      by_contra hnot
      have hJle : J ≤ p ^ q := Nat.le_of_not_gt hnot
      have hpow : J ^ 101 ≤ (p ^ q) ^ 101 :=
        Nat.pow_le_pow_left hJle 101
      have hident : (p ^ q) ^ 101 = p ^ (q * 101) := by
        rw [← pow_mul]
      rw [hident] at hpow
      exact (Nat.not_le_of_gt hsize) (hpow.trans hpq_le_n)
    have hp_le_J : p ≤ J := by
      exact (Nat.le_pow hq1).trans hpq_lt_J.le
    have hq_le_J : q ≤ J := by
      calc
        q ≤ 2 ^ q := q.lt_two_pow_self.le
        _ ≤ p ^ q := Nat.pow_le_pow_left hp.two_le q
        _ ≤ J := hpq_lt_J.le
    let E : Finset (ℕ × ℕ) :=
      (Finset.Icc 2 q).map
        ⟨fun a : ℕ => (p, a), by intro a b hab; simpa using hab⟩
    have hEsub : E ⊆
        (properPrimePowerIndices J).filter (fun pa => pa.1 = p) := by
      intro pa hpa
      rcases Finset.mem_map.mp hpa with ⟨a, ha, rfl⟩
      have ha' := Finset.mem_Icc.mp ha
      have hpow_le : p ^ a ≤ J := by
        calc
          p ^ a ≤ p ^ q := Nat.pow_le_pow_right hp.pos ha'.2
          _ ≤ J := hpq_lt_J.le
      apply Finset.mem_filter.mpr
      refine ⟨mem_properPrimePowerIndices_iff.mpr ?_, rfl⟩
      exact ⟨hp.two_le, hp_le_J, ha'.1, ha'.2.trans hq_le_J,
        hp, hpow_le⟩
    have hEdvd : ∀ pa ∈ E, pa.1 ^ pa.2 ∣ n := by
      intro pa hpa
      rcases Finset.mem_map.mp hpa with ⟨a, ha, rfl⟩
      have hq_le_e : q ≤ e := by omega
      have ha_le_e : a ≤ e := (Finset.mem_Icc.mp ha).2.trans hq_le_e
      change p ^ a ∣ n
      exact (hp.pow_dvd_iff_le_factorization hn0).2 (by simpa [e] using ha_le_e)
    have hcount : q - 1 ≤ baseTruncatedPrimePowerCount J n p := by
      have hsum : (∑ pa ∈ E, 1) ≤
          baseTruncatedPrimePowerCount J n p := by
        calc
          (∑ pa ∈ E, 1) =
              ∑ pa ∈ E, if pa.1 ^ pa.2 ∣ n then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro pa hpa
            rw [if_pos (hEdvd pa hpa)]
          _ ≤ baseTruncatedPrimePowerCount J n p := by
            unfold baseTruncatedPrimePowerCount
            apply Finset.sum_le_sum_of_subset_of_nonneg hEsub
            intro pa hpa hnot
            split_ifs <;> omega
      have hcard : (∑ pa ∈ E, 1) = q - 1 := by
        simp [E]
      rw [hcard] at hsum
      exact hsum
    calc
      n.factorization p = e := rfl
      _ ≤ 303 * q := by omega
      _ = 303 * (1 + (q - 1)) := by omega
      _ ≤ 303 * (1 + baseTruncatedPrimePowerCount J n p) := by gcongr
  · have hqle : q ≤ 1 := by omega
    calc
      n.factorization p = e := rfl
      _ ≤ 303 := by omega
      _ ≤ 303 * (1 + baseTruncatedPrimePowerCount J n p) := by
        have : 0 ≤ baseTruncatedPrimePowerCount J n p := Nat.zero_le _
        omega

/-- Summing the preceding coordinate bound gives the deterministic
truncation inequality used in the final union bound. -/
theorem Omega_le_omega_add_truncatedProperPrimePowerCount
    {J n : ℕ} (hnpos : 0 < n) (hJ : 1 < J) (hsize : n < J ^ 101) :
    Ω n ≤ 303 * ω n + 303 * truncatedProperPrimePowerCount J n := by
  have hcoord : ∀ p ∈ n.factorization.support,
      n.factorization p ≤ 303 * (1 + baseTruncatedPrimePowerCount J n p) := by
    intro p hp
    exact factorization_le_threehundredthree_mul_one_add_baseTruncated hJ
      hnpos.ne' hsize hp
  have hsum : n.factorization.sum (fun _ e => e) ≤
      ∑ p ∈ n.factorization.support,
        303 * (1 + baseTruncatedPrimePowerCount J n p) := by
    unfold Finsupp.sum
    exact Finset.sum_le_sum hcoord
  rw [factorization_sum_eq_Omega] at hsum
  have hbase : (∑ p ∈ n.factorization.support,
      baseTruncatedPrimePowerCount J n p) ≤
      truncatedProperPrimePowerCount J n := by
    unfold baseTruncatedPrimePowerCount truncatedProperPrimePowerCount
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    calc
      (∑ pa ∈ properPrimePowerIndices J,
        ∑ p ∈ n.factorization.support,
          if pa.1 = p then (if pa.1 ^ pa.2 ∣ n then 1 else 0) else 0) ≤
          ∑ pa ∈ properPrimePowerIndices J,
            if pa.1 ^ pa.2 ∣ n then 1 else 0 := by
        apply Finset.sum_le_sum
        intro pa hpa
        by_cases hdiv : pa.1 ^ pa.2 ∣ n
        · simp [hdiv]
          split_ifs <;> omega
        · simp [hdiv]
      _ = truncatedProperPrimePowerCount J n := rfl
  have hsupp : n.factorization.support.card = ω n := by
    rw [Nat.support_factorization, Erdos248.omega_eq_primeFactors_card]
  calc
    Ω n ≤ ∑ p ∈ n.factorization.support,
        303 * (1 + baseTruncatedPrimePowerCount J n p) := hsum
    _ = 303 * n.factorization.support.card +
        303 * ∑ p ∈ n.factorization.support,
          baseTruncatedPrimePowerCount J n p := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      simp [Nat.mul_comm, ← Finset.mul_sum]
    _ = 303 * ω n + 303 * ∑ p ∈ n.factorization.support,
          baseTruncatedPrimePowerCount J n p := by rw [hsupp]
    _ ≤ 303 * ω n + 303 * truncatedProperPrimePowerCount J n := by gcongr

end TaoTeravainen
