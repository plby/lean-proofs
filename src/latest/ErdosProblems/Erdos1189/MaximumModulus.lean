/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The sharp largest-modulus bound and its cardinality range.
Informal source: Section 4 of Pickhardt and Omniscience Research Agent,
"Irreducible Covering Sets: A Solution of Erdős Problem 1189".
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.Simpson
import ErdosProblems.Erdos1189.WeightBounds
import ErdosProblems.Erdos1189.ExtremalConstruction
import ErdosProblems.Erdos1189.Statements
import Mathlib.NumberTheory.Divisors

namespace Erdos1189

open Finset

lemma IsCoveringSet.lcm_pos {D : Finset ℕ} (h : IsCoveringSet D) : 0 < D.lcm id := by
  exact Nat.pos_of_ne_zero (lcm_ne_zero_iff.mpr
    (fun d hd => ne_of_gt (lt_trans Nat.zero_lt_one (h.1 d hd))))

lemma IsCoveringSet.subset_nontrivialDivisors_lcm {D : Finset ℕ} (h : IsCoveringSet D) :
    D ⊆ nontrivialDivisors (D.lcm id) := by
  intro d hd
  exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_lcm hd, h.lcm_pos.ne'⟩, h.1 d hd⟩

lemma small_divisors_card_le_weight {N : ℕ} (hN : N ≤ 8) :
    (nontrivialDivisors N).card ≤ simpsonWeight N := by
  simp only [simpsonWeight, Nat.factorization_eq_primeFactorsList_multiset,
    Multiset.toFinsupp_apply, Multiset.coe_count]
  interval_cases N <;> norm_num [Nat.primeFactors, Nat.primeFactorsList] <;> decide

lemma IsIrreducibleCoveringSet.five_le_card {D : Finset ℕ}
    (h : IsIrreducibleCoveringSet D) : 5 ≤ D.card := by
  by_contra hcard
  have hS := h.simpson
  have hW : simpsonWeight (D.lcm id) ≤ 3 := by omega
  have hN : D.lcm id ≤ 8 := calc
    D.lcm id ≤ 2 ^ simpsonWeight (D.lcm id) := le_two_pow_simpsonWeight h.1.lcm_pos.ne'
    _ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) hW
    _ = 8 := by norm_num
  have hdc := (card_le_card h.1.subset_nontrivialDivisors_lcm).trans
    (small_divisors_card_le_weight hN)
  omega

theorem IsCoveringSet.five_le_card {D : Finset ℕ} (h : IsCoveringSet D) : 5 ≤ D.card := by
  obtain ⟨E, hED, hE⟩ := h.exists_irreducible_subset
  exact hE.five_le_card.trans (card_le_card hED)

theorem not_covering_of_card_le_four {D : Finset ℕ} (hD : D.card ≤ 4) :
    ¬ IsCoveringSet D := by
  intro h
  have := h.five_le_card
  omega

lemma IsCoveringSet.lcm_ne_two_pow {D : Finset ℕ} (h : IsCoveringSet D) (a : ℕ) :
    D.lcm id ≠ 2 ^ a := by
  intro heq
  have hsub : D ⊆ binaryChain a := by
    intro d hd
    have hdiv : d ∈ (2 ^ a).divisors := by
      exact Nat.mem_divisors.mpr ⟨heq ▸ dvd_lcm hd, by positivity⟩
    obtain ⟨j, hj, rfl⟩ := (Nat.mem_divisors_prime_pow Nat.prime_two a).mp hdiv
    have hj0 : 0 < j := by
      by_contra hj0
      have hjz : j = 0 := by omega
      have := h.1 (2 ^ j) hd
      simp [hjz] at this
    exact mem_binaryChain.mpr ⟨j - 1, by omega, by rw [Nat.sub_add_cancel hj0]⟩
  obtain ⟨r, hr⟩ := h.2
  have hc := hr.period_le_sum_quotients
    (fun d hd => lt_trans Nat.zero_lt_one (h.1 d hd))
    (fun d hd => binaryChain_dvd (hsub hd))
  have hs : (∑ d ∈ D, 2 ^ a / d) ≤ ∑ d ∈ binaryChain a, 2 ^ a / d :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  have hb := binaryChain_weight a
  omega

lemma IsCoveringSet.exists_odd_prime_lcm {D : Finset ℕ} (h : IsCoveringSet D) :
    ∃ p ∈ (D.lcm id).primeFactors, 3 ≤ p := by
  by_contra hn
  push Not at hn
  apply h.lcm_ne_two_pow ((D.lcm id).factorization 2)
  apply eq_two_pow_of_primeFactors h.lcm_pos.ne'
  intro p hp
  have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
  have hp3 := hn p hp
  omega

theorem IsIrreducibleCoveringSet.lcm_le {D : Finset ℕ}
    (h : IsIrreducibleCoveringSet D) : D.lcm id ≤ 3 * 2 ^ (D.card - 3) := by
  obtain ⟨p, hp, hp3⟩ := h.1.exists_odd_prime_lcm
  have hw := four_mul_le_three_pow_weight h.1.lcm_pos.ne' hp hp3
  have hS := h.simpson
  have hk := h.five_le_card
  have hpw : 2 ^ simpsonWeight (D.lcm id) ≤ 2 ^ (D.card - 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have heq : 2 ^ (D.card - 1) = 4 * 2 ^ (D.card - 3) := by
    have hc : D.card - 1 = (D.card - 3) + 2 := by omega
    rw [hc, pow_add]
    ring
  rw [heq] at hpw
  omega

theorem IsIrreducibleCoveringSet.largest_le {D : Finset ℕ}
    (h : IsIrreducibleCoveringSet D) : D.sup id ≤ 3 * 2 ^ (D.card - 3) := by
  apply le_trans _ h.lcm_le
  apply Finset.sup_le
  intro d hd
  exact Nat.le_of_dvd h.1.lcm_pos (dvd_lcm hd)

/-- The largest possible largest modulus is exactly `3*2^(k-3)`, for every `k ≥ 5`. -/
theorem maximumLargestModulus : MaximumLargestModulusClaim := by
  intro k hk
  refine ⟨?_, ?_⟩
  · intro D hD
    have h := hD.1.largest_le
    simpa only [hD.2] using h
  · obtain ⟨D, hD, hcard, hmax⟩ := exists_irreducible_extremal hk
    exact ⟨D, ⟨hD, hcard⟩, hmax⟩

lemma finite_irreducibleSetsOfSize (k : ℕ) : (irreducibleSetsOfSize k).Finite := by
  apply ((range (3 * 2 ^ (k - 3) + 1)).powerset.finite_toSet).subset
  intro D hD
  apply mem_powerset.mpr
  intro d hd
  apply mem_range.mpr
  have hmax := hD.1.largest_le
  have hle : d ≤ D.sup id := le_sup (f := id) hd
  rw [hD.2] at hmax
  omega

lemma irreducibleSetsOfSize_nonempty_iff {k : ℕ} :
    (irreducibleSetsOfSize k).Nonempty ↔ 5 ≤ k := by
  constructor
  · rintro ⟨D, hD, hcard⟩
    simpa only [← hcard] using hD.five_le_card
  · intro hk
    obtain ⟨D, hD, hcard, _⟩ := exists_irreducible_extremal hk
    exact ⟨D, hD, hcard⟩

end Erdos1189
