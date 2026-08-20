/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.SeparatedSelection
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integrating lower bounds on separated intervals

This measure-theoretic packing lemma converts pointwise lower bounds
propagated from separated sample points into a lower bound for one interval
integral.  Forward half-intervals avoid boundary loss at height zero.
-/

namespace Erdos48

open Set MeasureTheory
open scoped Interval

noncomputable section

/-- Disjoint forward intervals based at separated points contribute their
full total length to a nonnegative continuous mass function. -/
theorem card_mul_interval_lower_le_integral
    (S : Finset ℝ) {r T B : ℝ} (hr : 0 < r) (hT : 0 ≤ T)
    (hS : ∀ t ∈ S, 0 ≤ t ∧ t ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 2 * r < dist x y)
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ u, 0 ≤ f u)
    (hlower : ∀ t ∈ S, ∀ u, u ∈ Set.Ioc t (t + r) → B ≤ f u) :
    (S.card : ℝ) * r * B ≤ ∫ u in (0 : ℝ)..(T + r), f u := by
  let U : Set ℝ := ⋃ t ∈ S, Set.Ioc t (t + r)
  have hpair : Set.PairwiseDisjoint (S : Set ℝ)
      (fun t ↦ Set.Ioc t (t + r)) :=
    pairwiseDisjoint_Ioc_add_of_separated hsep
  have hinterval (t : ℝ) (ht : t ∈ S) :
      B * r ≤ ∫ u in Set.Ioc t (t + r), f u := by
    have hmeasure : volume (Set.Ioc t (t + r)) ≠ ⊤ := by simp
    have hint : IntegrableOn f (Set.Ioc t (t + r)) :=
      hf.continuousOn.integrableOn_compact isCompact_Icc
        |>.mono_set Set.Ioc_subset_Icc_self
    have h := setIntegral_ge_of_const_le_real
      measurableSet_Ioc hmeasure (hlower t ht) hint
    simpa [Real.volume_Ioc, hr.le, mul_comm] using h
  have hsum :
      ∑ t ∈ S, (B * r) ≤
        ∑ t ∈ S, ∫ u in Set.Ioc t (t + r), f u :=
    Finset.sum_le_sum fun t ht ↦ hinterval t ht
  have hUnionEq :
      (∫ u in U, f u) =
        ∑ t ∈ S, ∫ u in Set.Ioc t (t + r), f u := by
    unfold U
    apply integral_biUnion_finset S
    · intro t ht
      exact measurableSet_Ioc
    · exact hpair
    · intro t ht
      exact (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set
        Set.Ioc_subset_Icc_self
  have hUsub : U ⊆ Set.Ioc 0 (T + r) := by
    intro u hu
    simp only [U, Set.mem_iUnion] at hu
    obtain ⟨t, ht, htu⟩ := hu
    have htRange := hS t ht
    exact ⟨lt_of_le_of_lt htRange.1 htu.1,
      by linarith [htu.2, htRange.2]⟩
  have hbigInt : IntegrableOn f (Set.Ioc 0 (T + r)) :=
    (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hUle : (∫ u in U, f u) ≤ ∫ u in Set.Ioc 0 (T + r), f u := by
    exact setIntegral_mono_set hbigInt
      (Filter.Eventually.of_forall fun u ↦ hf0 u)
      (Filter.Eventually.of_forall hUsub)
  calc
    (S.card : ℝ) * r * B = ∑ t ∈ S, (B * r) := by
      simp [mul_comm, mul_left_comm, mul_assoc]
    _ ≤ ∑ t ∈ S, ∫ u in Set.Ioc t (t + r), f u := hsum
    _ = ∫ u in U, f u := hUnionEq.symm
    _ ≤ ∫ u in Set.Ioc 0 (T + r), f u := hUle
    _ = ∫ u in (0 : ℝ)..(T + r), f u := by
      rw [intervalIntegral.integral_of_le (by linarith)]

end

end Erdos48
