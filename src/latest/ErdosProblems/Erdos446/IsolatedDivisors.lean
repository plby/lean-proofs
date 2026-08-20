/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.ClusterUpper

/-!
# Erdős Problem 446: isolated divisors

Ford's prescribed-multiplicity argument keeps divisors which have no other
divisor in a prescribed logarithmic neighbourhood.  This file proves the
finite inequality relating the number of isolated divisors to the number of
ordered close pairs.  No analytic estimate enters here.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

noncomputable def sigmaNeighborDivisors (a d : ℕ) (sigma : ℝ) : Finset ℕ :=
  a.divisors.filter fun e ↦
    |Real.log (d : ℝ) - Real.log (e : ℝ)| ≤ sigma

noncomputable def sigmaCloseDivisorPairs (a : ℕ) (sigma : ℝ) :
    Finset (ℕ × ℕ) :=
  (a.divisors ×ˢ a.divisors).filter fun de ↦
    |Real.log (de.1 : ℝ) - Real.log (de.2 : ℝ)| ≤ sigma

noncomputable def sigmaClosePairCount (a : ℕ) (sigma : ℝ) : ℕ :=
  (sigmaCloseDivisorPairs a sigma).card

noncomputable def sigmaIsolatedDivisors (a : ℕ) (sigma : ℝ) : Finset ℕ :=
  a.divisors.filter fun d ↦ sigmaNeighborDivisors a d sigma = {d}

noncomputable def sigmaIsolatedCount (a : ℕ) (sigma : ℝ) : ℕ :=
  (sigmaIsolatedDivisors a sigma).card

theorem mem_sigmaNeighborDivisors {a d e : ℕ} {sigma : ℝ} :
    e ∈ sigmaNeighborDivisors a d sigma ↔
      e ∈ a.divisors ∧
        |Real.log (d : ℝ) - Real.log (e : ℝ)| ≤ sigma := by
  simp [sigmaNeighborDivisors]

theorem mem_sigmaIsolatedDivisors {a d : ℕ} {sigma : ℝ} :
    d ∈ sigmaIsolatedDivisors a sigma ↔
      d ∈ a.divisors ∧ sigmaNeighborDivisors a d sigma = {d} := by
  simp [sigmaIsolatedDivisors]

theorem self_mem_sigmaNeighborDivisors {a d : ℕ} {sigma : ℝ}
    (hsigma : 0 ≤ sigma) (hd : d ∈ a.divisors) :
    d ∈ sigmaNeighborDivisors a d sigma := by
  rw [mem_sigmaNeighborDivisors]
  simp [hd, hsigma]

theorem sigmaClosePairCount_eq_sum_neighbors (a : ℕ) (sigma : ℝ) :
    sigmaClosePairCount a sigma =
      ∑ d ∈ a.divisors, (sigmaNeighborDivisors a d sigma).card := by
  classical
  rw [sigmaClosePairCount, sigmaCloseDivisorPairs, Finset.card_filter,
    Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d hd
  rw [sigmaNeighborDivisors, Finset.card_filter]

theorem two_le_card_sigmaNeighborDivisors_of_not_isolated
    {a d : ℕ} {sigma : ℝ} (hsigma : 0 ≤ sigma)
    (hd : d ∈ a.divisors) (hnot : d ∉ sigmaIsolatedDivisors a sigma) :
    2 ≤ (sigmaNeighborDivisors a d sigma).card := by
  have hdmem := self_mem_sigmaNeighborDivisors hsigma hd
  have hne : sigmaNeighborDivisors a d sigma ≠ {d} := by
    intro h
    exact hnot (mem_sigmaIsolatedDivisors.mpr ⟨hd, h⟩)
  have hproper : {d} ⊂ sigmaNeighborDivisors a d sigma := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · simpa using hdmem
    · exact Ne.symm hne
  have hcard := Finset.card_lt_card hproper
  have hcard' : 1 < (sigmaNeighborDivisors a d sigma).card := by
    simpa using hcard
  omega

/-- Every divisor gives a diagonal close pair, and every non-isolated divisor
gives one additional off-diagonal close pair. -/
theorem twice_card_divisors_le_close_add_isolated
    (a : ℕ) {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    2 * a.divisors.card ≤
      sigmaClosePairCount a sigma + sigmaIsolatedCount a sigma := by
  classical
  have hpoint : ∀ d ∈ a.divisors,
      (if d ∈ sigmaIsolatedDivisors a sigma then 1 else 2) ≤
        (sigmaNeighborDivisors a d sigma).card := by
    intro d hd
    by_cases hiso : d ∈ sigmaIsolatedDivisors a sigma
    · rw [if_pos hiso]
      exact Finset.one_le_card.mpr
        ⟨d, self_mem_sigmaNeighborDivisors hsigma hd⟩
    · rw [if_neg hiso]
      exact two_le_card_sigmaNeighborDivisors_of_not_isolated hsigma hd hiso
  have hsum := Finset.sum_le_sum hpoint
  rw [← sigmaClosePairCount_eq_sum_neighbors] at hsum
  have hisoSub : sigmaIsolatedDivisors a sigma ⊆ a.divisors := by
    intro d hd
    exact (mem_sigmaIsolatedDivisors.mp hd).1
  have hisoCard : (sigmaIsolatedDivisors a sigma).card ≤ a.divisors.card :=
    Finset.card_le_card hisoSub
  have hleft :
      (∑ d ∈ a.divisors,
        if d ∈ sigmaIsolatedDivisors a sigma then 1 else 2) =
        2 * a.divisors.card - sigmaIsolatedCount a sigma := by
    rw [← Finset.sum_filter_add_sum_filter_not a.divisors
      (fun d ↦ d ∈ sigmaIsolatedDivisors a sigma)
      (fun d ↦ if d ∈ sigmaIsolatedDivisors a sigma then 1 else 2)]
    have hfilter : a.divisors.filter
        (fun d ↦ d ∈ sigmaIsolatedDivisors a sigma) =
          sigmaIsolatedDivisors a sigma := by
      ext d
      simp only [Finset.mem_filter]
      constructor
      · exact fun h ↦ h.2
      · exact fun h ↦ ⟨hisoSub h, h⟩
    have hfilterNot : a.divisors.filter
        (fun d ↦ ¬ d ∈ sigmaIsolatedDivisors a sigma) =
          a.divisors \ sigmaIsolatedDivisors a sigma := by
      ext d
      simp
    rw [hfilter, hfilterNot]
    have hsumIso :
        (∑ d ∈ sigmaIsolatedDivisors a sigma,
          if d ∈ sigmaIsolatedDivisors a sigma then 1 else 2) =
            (sigmaIsolatedDivisors a sigma).card := by
      calc
        (∑ d ∈ sigmaIsolatedDivisors a sigma,
            if d ∈ sigmaIsolatedDivisors a sigma then 1 else 2) =
            ∑ _d ∈ sigmaIsolatedDivisors a sigma, 1 := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [if_pos hd]
        _ = (sigmaIsolatedDivisors a sigma).card := by simp
    have hsumNot :
        (∑ d ∈ a.divisors \ sigmaIsolatedDivisors a sigma,
          if d ∈ sigmaIsolatedDivisors a sigma then 1 else 2) =
            2 * (a.divisors \ sigmaIsolatedDivisors a sigma).card := by
      calc
        (∑ d ∈ a.divisors \ sigmaIsolatedDivisors a sigma,
            if d ∈ sigmaIsolatedDivisors a sigma then 1 else 2) =
            ∑ _d ∈ a.divisors \ sigmaIsolatedDivisors a sigma, 2 := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [if_neg (Finset.mem_sdiff.mp hd).2]
        _ = 2 * (a.divisors \ sigmaIsolatedDivisors a sigma).card := by
          simp [mul_comm]
    rw [hsumIso, hsumNot]
    rw [Finset.card_sdiff_of_subset hisoSub]
    simp only [sigmaIsolatedCount]
    omega
  rw [hleft] at hsum
  omega

theorem card_divisors_le_sigmaClosePairCount
    (a : ℕ) {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    a.divisors.card ≤ sigmaClosePairCount a sigma := by
  classical
  rw [sigmaClosePairCount_eq_sum_neighbors]
  calc
    a.divisors.card = ∑ _d ∈ a.divisors, 1 := by simp
    _ ≤ ∑ d ∈ a.divisors,
        (sigmaNeighborDivisors a d sigma).card := by
      apply Finset.sum_le_sum
      intro d hd
      exact Finset.one_le_card.mpr
        ⟨d, self_mem_sigmaNeighborDivisors hsigma hd⟩

/-- Ford's isolated-divisor inequality.  This is the factored form of
`I^r ≥ 2⁻ʳ τ^(r-1) (3τ - 2W)`. -/
theorem ford_isolated_divisor_power_lower
    (a r : ℕ) {sigma : ℝ} (hsigma : 0 ≤ sigma) (hr : 1 ≤ r) :
    ((a.divisors.card : ℝ) / 2) ^ (r - 1) *
        ((3 * (a.divisors.card : ℝ) -
          2 * (sigmaClosePairCount a sigma : ℝ)) / 2) ≤
      (sigmaIsolatedCount a sigma : ℝ) ^ r := by
  let T : ℝ := a.divisors.card
  let W : ℝ := sigmaClosePairCount a sigma
  let I : ℝ := sigmaIsolatedCount a sigma
  have hIT : 2 * T ≤ W + I := by
    dsimp [T, W, I]
    exact_mod_cast twice_card_divisors_le_close_add_isolated a hsigma
  have hTW : T ≤ W := by
    dsimp [T, W]
    exact_mod_cast card_divisors_le_sigmaClosePairCount a hsigma
  have hnonnegI : 0 ≤ I := by positivity
  have hnonnegT : 0 ≤ T := by positivity
  by_cases hsign : 3 * T ≤ 2 * W
  · have hfactor : (3 * T - 2 * W) / 2 ≤ 0 := by linarith
    have hpow : 0 ≤ (T / 2) ^ (r - 1) := by positivity
    have hleft : (T / 2) ^ (r - 1) * ((3 * T - 2 * W) / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hpow hfactor
    exact hleft.trans (pow_nonneg hnonnegI r)
  · have hsign' : 2 * W < 3 * T := lt_of_not_ge hsign
    have hIhalf : T / 2 ≤ I := by linarith
    have hIlast : (3 * T - 2 * W) / 2 ≤ I := by linarith
    have hpow : (T / 2) ^ (r - 1) ≤ I ^ (r - 1) := by
      exact pow_le_pow_left₀ (by positivity) hIhalf _
    have hlast : 0 ≤ (3 * T - 2 * W) / 2 := by linarith
    calc
      (T / 2) ^ (r - 1) * ((3 * T - 2 * W) / 2) ≤
          I ^ (r - 1) * I := by gcongr
      _ = I ^ r := by
        have hrexp : r - 1 + 1 = r := by omega
        rw [← pow_succ, hrexp]

end Erdos446
