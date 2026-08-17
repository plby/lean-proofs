/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos448.Basic
import ErdosProblems.Erdos144.FinalTransfer
import ErdosProblems.Erdos144.HarmonicHighProbability
import ErdosProblems.Erdos144.PrimeBlockAsymptotic

/-!
# Erdős Problem 144

Maier and Tenenbaum proved that almost every positive integer has two
divisors whose ratio is less than any prescribed constant greater than one.
This file specializes their result to the factor `2` asked for in Problem
144.  The mathematical proof and the formalization map are in `tex/144.tex`.
-/

namespace Erdos144

open Filter
open scoped Topology

/-- The exact set in Erdős Problem 144. -/
def closeDivisorSet : Set ℕ :=
  {n : ℕ | ∃ d₁ d₂ : ℕ,
    d₁ ∣ n ∧ d₂ ∣ n ∧ d₁ < d₂ ∧ d₂ < 2 * d₁}

/-- If the binary logarithm is not injective on the divisors of `n`, then
`n` has two divisors strictly within a factor of two.  The strict upper
endpoint follows from Mathlib's half-open convention for `Nat.log`. -/
lemma closeDivisors_of_not_injOn_log_divisors {n : ℕ}
    (h : ¬Set.InjOn (Nat.log 2) n.divisors) : n ∈ closeDivisorSet := by
  classical
  simp only [Set.InjOn] at h
  push Not at h
  obtain ⟨a, ha, b, hb, hlog, hab⟩ := h
  have ha0 : a ≠ 0 := (Nat.pos_of_mem_divisors ha).ne'
  have hb0 : b ≠ 0 := (Nat.pos_of_mem_divisors hb).ne'
  have hclose : ∀ {d₁ d₂ : ℕ}, d₁ ≠ 0 → d₂ ≠ 0 →
      Nat.log 2 d₁ = Nat.log 2 d₂ → d₁ < d₂ → d₂ < 2 * d₁ := by
    intro d₁ d₂ hd₁0 hd₂0 heq hlt
    have hd₂Upper : d₂ < 2 ^ (Nat.log 2 d₂).succ :=
      Nat.lt_pow_succ_log_self (by norm_num) d₂
    have hd₁Lower : 2 ^ Nat.log 2 d₁ ≤ d₁ :=
      Nat.pow_log_le_self 2 hd₁0
    rw [← heq] at hd₂Upper
    calc
      d₂ < 2 ^ (Nat.log 2 d₁).succ := hd₂Upper
      _ = 2 * 2 ^ Nat.log 2 d₁ := by rw [pow_succ']
      _ ≤ 2 * d₁ := Nat.mul_le_mul_left 2 hd₁Lower
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · exact ⟨a, b, Nat.dvd_of_mem_divisors ha, Nat.dvd_of_mem_divisors hb,
      hablt, hclose ha0 hb0 hlog hablt⟩
  · exact ⟨b, a, Nat.dvd_of_mem_divisors hb, Nat.dvd_of_mem_divisors ha,
      hbalt, hclose hb0 ha0 hlog.symm hbalt⟩

/-- A strict loss of cardinality under the dyadic-log map produces the
close divisor pair. -/
lemma closeDivisors_of_tauPlus_lt {n : ℕ}
    (h : Erdos448.tauPlus n < n.divisors.card) : n ∈ closeDivisorSet := by
  apply closeDivisors_of_not_injOn_log_divisors
  intro hinj
  have hcard := Finset.card_image_iff.mpr hinj
  exact h.ne (by simpa [Erdos448.tauPlus] using hcard)

/-- Pointwise inclusion of the exact dyadic collision event in the target
set of Problem 144. -/
lemma dyadicCollisionSet_subset_closeDivisorSet :
    {n : ℕ | Erdos448.tauPlus n < n.divisors.card} ⊆ closeDivisorSet := by
  intro n hn
  exact closeDivisors_of_tauPlus_lt hn

/-- Erdős Problem 144: the natural density of integers having two divisors
strictly within a factor of two exists and equals one. -/
theorem erdos_144 : closeDivisorSet.HasDensity 1 := by
  have h := FinalTransfer.hasDensity_one_of_harmonic_prob_and_occupancy_error
    Harmonic.lowerScale Harmonic.finalTop Harmonic.transferMesh
      Harmonic.cardinalCutoff
    (fun s ↦ by
      rw [Harmonic.transferMesh_eq]
      exact pow_pos (Harmonic.cardinalCutoff_pos s) 2)
    (fun s ↦ by
      simp [Harmonic.lowerScale])
    HarmonicHighProbability.tendsto_good_prob_one
    PrimeBlockAsymptotic.tendsto_two_mul_sum_subtype_abs_logBlockOccupancy_sub_inv_zero
    Harmonic.eventually_two_mul_cardinalCutoff_div_transferMesh_lt_log_two
  simpa only [closeDivisorSet, CRTClose.HasCloseDivisors] using h

end Erdos144

#print axioms Erdos144.erdos_144
