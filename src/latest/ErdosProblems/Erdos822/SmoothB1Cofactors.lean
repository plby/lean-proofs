/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SmallPrimePowerMass
import ErdosProblems.Erdos822.RestrictedCofactors

/-! # A positive-mass family satisfying the full smooth-preservation condition -/

namespace Erdos822

open Filter
open scoped BigOperators Classical

noncomputable def preservingSmallFactors (N : ℕ) : Finset ℕ :=
  (b1GoodSmallFactors N).filter fun k ↦ SmallPrimePowersBounded k (b1Cutoff N)

noncomputable def smoothB1Cofactors (N : ℕ) : Finset ℕ :=
  restrictedCofactors N (preservingSmallFactors N)

theorem preservingSmallFactors_subset_odd (N : ℕ) :
    preservingSmallFactors N ⊆ oddSmallFactors N :=
  (Finset.filter_subset _ _).trans (b1GoodSmallFactors_subset_oddSmallFactors N)

theorem exists_eventually_sum_inv_preservingSmallFactors_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * Real.log (N : ℝ) ≤ ∑ k ∈ preservingSmallFactors N, (1 : ℝ) / k := by
  obtain ⟨c, hc, hmass⟩ := exists_eventually_sum_inv_b1GoodSmallFactors_lower
  refine ⟨c / 2, by positivity, ?_⟩
  filter_upwards [hmass,
      eventually_sum_inv_smallPrimePowerBadFactors_le_log (ε := c / 2) (by positivity)]
    with N hN hbad
  have hsplit : (∑ k ∈ preservingSmallFactors N, (1 : ℝ) / k) +
      (∑ k ∈ (b1GoodSmallFactors N).filter
        (fun k ↦ ¬ SmallPrimePowersBounded k (b1Cutoff N)), (1 : ℝ) / k) =
        ∑ k ∈ b1GoodSmallFactors N, (1 : ℝ) / k :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hsub : (b1GoodSmallFactors N).filter
      (fun k ↦ ¬ SmallPrimePowersBounded k (b1Cutoff N)) ⊆
      smallPrimePowerBadFactors N (b1Cutoff N) := by
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr
      ⟨b1GoodSmallFactors_subset_oddSmallFactors N hk'.1, hk'.2⟩
  have hbadmass :
      (∑ k ∈ (b1GoodSmallFactors N).filter
        (fun k ↦ ¬ SmallPrimePowersBounded k (b1Cutoff N)), (1 : ℝ) / k) ≤
        ∑ k ∈ smallPrimePowerBadFactors N (b1Cutoff N), (1 : ℝ) / k := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk hnot ↦ by positivity)
  linarith

theorem smoothB1Cofactors_subset_oddRaw (N : ℕ) :
    smoothB1Cofactors N ⊆ oddRawCofactors N :=
  restrictedCofactors_subset_oddRaw (preservingSmallFactors_subset_odd N)

theorem smoothB1Cofactors_subset_b1 (N : ℕ) : smoothB1Cofactors N ⊆ b1Cofactors N := by
  intro m hm
  obtain ⟨k, r, q, hk, hr, hq, hm⟩ := mem_restrictedCofactors_iff.mp hm
  exact mem_b1Cofactors_iff.mpr ⟨k, r, q, (Finset.mem_filter.mp hk).1, hr, hq, hm⟩

theorem exists_eventually_sum_inv_smoothB1Cofactors_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * Real.log (N : ℝ) ≤ ∑ m ∈ smoothB1Cofactors N, (1 : ℝ) / m := by
  obtain ⟨c, hc, hmass⟩ := exists_eventually_sum_inv_preservingSmallFactors_lower
  exact ⟨c / 500, by positivity,
    eventually_sum_inv_restrictedCofactors_lower hc preservingSmallFactors_subset_odd hmass⟩

theorem smallPrimePowersBounded_mul_prime {m p y : ℕ}
    (hm : 0 < m) (hp : p.Prime) (hyp : y < p)
    (hbounded : SmallPrimePowersBounded m y) :
    SmallPrimePowersBounded (m * p) y := by
  intro q hq hqy
  have hnot : ¬ q ∣ p := by
    intro hdiv
    have heq := (Nat.prime_dvd_prime_iff_eq hq hp).mp hdiv
    omega
  have hfac : (m * p).factorization q = m.factorization q := by
    rw [Nat.factorization_mul hm.ne' hp.ne_zero]
    simp [Nat.factorization_eq_zero_of_not_dvd hnot]
  rw [hfac]
  exact hbounded q hq hqy

theorem b1Cutoff_le_self (N : ℕ) : b1Cutoff N ≤ N :=
  (nthRoot_le_self_of_pos (k := 4) (N := b1DoubleLog N) (by norm_num)).trans
    ((Nat.log_le_self 2 (Nat.log 2 N)).trans (Nat.log_le_self 2 N))

theorem smoothB1Cofactors_smallPrimePowersBounded {N m : ℕ}
    (hN : 2 ≤ N) (hm : m ∈ smoothB1Cofactors N) :
    SmallPrimePowersBounded m (b1Cutoff N) := by
  obtain ⟨k, r, q, hk, hr, hq, rfl⟩ := mem_restrictedCofactors_iff.mp hm
  have hkp := Finset.mem_filter.mp hk
  have hkpos := oddSmallFactors_pos (preservingSmallFactors_subset_odd N hk)
  have hrp := (mem_middlePrimes_iff.mp hr).2.2
  have hqp := (mem_largePrimes_iff.mp hq).2.2
  have hN4 : N < N ^ 4 := by
    have hN2 : N < N ^ 2 := by nlinarith
    exact hN2.trans_le (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hyr : b1Cutoff N < r := (b1Cutoff_le_self N).trans_lt
    (hN4.trans_le (mem_middlePrimes_iff.mp hr).1)
  have hyq : b1Cutoff N < q := (b1Cutoff_le_self N).trans_lt
    (hN4.trans_le ((Nat.pow_le_pow_right (by omega) (by norm_num : 4 ≤ 21)).trans
      (mem_largePrimes_iff.mp hq).1))
  exact smallPrimePowersBounded_mul_prime (Nat.mul_pos hkpos hrp.pos) hqp hyq
    (smallPrimePowersBounded_mul_prime hkpos hrp hyr hkp.2)

theorem smoothB1Cofactors_preserving {N m : ℕ}
    (hN : 2 ≤ N) (hm : m ∈ smoothB1Cofactors N) :
    SmoothTotientPreserving m (b1Cutoff N) :=
  b1Cofactors_smoothPreserving_of_bounded (smoothB1Cofactors_subset_b1 N hm)
    (smoothB1Cofactors_smallPrimePowersBounded hN hm)

#print axioms exists_eventually_sum_inv_smoothB1Cofactors_lower
#print axioms smoothB1Cofactors_preserving

end Erdos822
