/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.WeightedQuantileBridge
import ErdosProblems.Erdos446.SmirnovWordMass

/-!
# Erdős Problem 446: weighted words and occupancy vectors

This file is the weighted analogue of the word-count identity in
`SmirnovWordMass`.  It identifies the mass of a labelled categorical word
event depending only on its occupancy vector with factorial times the
corresponding reciprocal-factorial composition mass.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- The finite set underlying a weighted word event. -/
noncomputable def weightedWordEventFinset
    {k v : ℕ} (_lam : Fin v → ℝ)
    (P : (Fin k → Fin v) → Prop) : Finset (Fin k → Fin v) := by
  classical
  exact Finset.univ.filter P

/-- Filter form of `weightedWordEventMass`. -/
theorem weightedWordEventMass_eq_sum_filter
    {k v : ℕ} (lam : Fin v → ℝ)
    (P : (Fin k → Fin v) → Prop) :
    weightedWordEventMass lam P =
      ∑ f ∈ weightedWordEventFinset lam P,
        weightedWordMass lam f := by
  classical
  rw [weightedWordEventMass, weightedWordEventFinset, Finset.sum_filter]

/-- The product weight of a word depends on the word only through its
occupancy vector. -/
theorem weightedWordMass_eq_prod_pow_wordOccupancy
    {k v : ℕ} (lam : Fin v → ℝ) (f : Fin k → Fin v) :
    weightedWordMass lam f = ∏ j : Fin v, lam j ^ wordOccupancy f j := by
  classical
  rw [weightedWordMass]
  symm
  calc
    (∏ j : Fin v, lam j ^ wordOccupancy f j) =
        ∏ j : Fin v,
          ∏ i ∈ (Finset.univ : Finset (Fin k)).filter (fun i ↦ f i = j),
            lam j := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [wordOccupancy, Finset.prod_const]
    _ = ∏ i : Fin k, lam (f i) := by
      exact Finset.prod_fiberwise_of_maps_to'
        (s := (Finset.univ : Finset (Fin k)))
        (t := (Finset.univ : Finset (Fin v)))
        (g := f) (fun _ _ ↦ Finset.mem_univ _) lam

/-- The total weight of one occupancy fiber is its multinomial coefficient
times its occupancy monomial. -/
theorem sum_weightedWordMass_wordOccupancy_fiber
    {k v : ℕ} (lam : Fin v → ℝ) (c : Fin v → ℕ)
    (hc : ∑ j, c j = k) :
    (∑ f ∈ (Finset.univ : Finset (Fin k → Fin v)).filter
        (fun f ↦ wordOccupancy f = c), weightedWordMass lam f) =
      (Nat.multinomial Finset.univ c : ℝ) * ∏ j : Fin v, lam j ^ c j := by
  classical
  calc
    (∑ f ∈ (Finset.univ : Finset (Fin k → Fin v)).filter
        (fun f ↦ wordOccupancy f = c), weightedWordMass lam f) =
        ∑ f ∈ (Finset.univ : Finset (Fin k → Fin v)).filter
          (fun f ↦ wordOccupancy f = c), ∏ j : Fin v, lam j ^ c j := by
      apply Finset.sum_congr rfl
      intro f hf
      rw [weightedWordMass_eq_prod_pow_wordOccupancy]
      exact Finset.prod_congr rfl fun j _ ↦ by
        rw [congrFun (Finset.mem_filter.mp hf).2 j]
    _ = (((Finset.univ : Finset (Fin k → Fin v)).filter
          (fun f ↦ wordOccupancy f = c)).card : ℝ) *
          ∏ j : Fin v, lam j ^ c j := by
      simp
    _ = (Nat.multinomial Finset.univ c : ℝ) *
          ∏ j : Fin v, lam j ^ c j := by
      rw [card_wordOccupancy_fiber c hc]

/-- Exact weighted word/composition identity for any family of occupancy
vectors of total size `k`. -/
theorem weightedWordEventMass_wordOccupancy
    {k v : ℕ} (lam : Fin v → ℝ) (I : Finset (Fin v → ℕ))
    (hI : I ⊆ compositionsOf v k) :
    weightedWordEventMass lam
        (fun f : Fin k → Fin v ↦ wordOccupancy f ∈ I) =
      (k.factorial : ℝ) * ∑ c ∈ I, weightedCompositionMass lam c := by
  classical
  rw [weightedWordEventMass_eq_sum_filter]
  let S : Finset (Fin k → Fin v) := weightedWordEventFinset lam
    (fun f : Fin k → Fin v ↦ wordOccupancy f ∈ I)
  change (∑ f ∈ S, weightedWordMass lam f) = _
  have hmaps : ∀ f ∈ S, wordOccupancy f ∈ I := by
    intro f hf
    simpa only [S, weightedWordEventFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] using hf
  calc
    (∑ f ∈ S, weightedWordMass lam f) =
        ∑ c ∈ I,
        ∑ f ∈ S.filter (fun f ↦ wordOccupancy f = c),
          weightedWordMass lam f := by
      exact (Finset.sum_fiberwise_of_maps_to hmaps
        (fun f ↦ weightedWordMass lam f)).symm
    _ =
        ∑ c ∈ I,
          (Nat.multinomial Finset.univ c : ℝ) *
            ∏ j : Fin v, lam j ^ c j := by
      apply Finset.sum_congr rfl
      intro c hcI
      rw [← sum_weightedWordMass_wordOccupancy_fiber lam c
        (mem_compositionsOf.mp (hI hcI))]
      congr 1
      ext f
      simp only [S, weightedWordEventFinset, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · exact fun hf ↦ hf.2
      · intro hf
        exact ⟨by simpa [hf] using hcI, hf⟩
    _ = (k.factorial : ℝ) *
        ∑ c ∈ I, weightedCompositionMass lam c := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hcI
      rw [weightedCompositionMass, div_eq_mul_inv, ← one_div,
        inv_compositionFactorial_eq_multinomial_div_of_mem (hI hcI)]
      have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
      field_simp

end Erdos446
