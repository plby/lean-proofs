/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceRegularizationOrderData
import ErdosProblems.Erdos207.RegularizationOutputWitness

/-! # Actual order regularization, separated from the ambient envelope support -/

namespace Erdos207

open Finset

noncomputable section

structure RegularizedOrderCore
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Nonempty I]
    (e : I ↪ TripleOn V) (j b : ℕ) (L earlier : Finset (Finset I))
    (Lstar : Finset (Finset I)) (Fsup : ForbiddenFamilyOn V) : Prop where
  uniform : ∀ E ∈ Lstar, E.card = j - 2
  maximum : finiteHypergraphMaxDegree Lstar ≤ 9 * finiteHypergraphMaxDegree L
  gap : finiteHypergraphDegreeGap Lstar ≤ b
  no_earlier_subset : ∀ E ∈ Lstar, ∀ C ∈ earlier, ¬ C ⊆ E
  covers_original : ∀ E ∈ L, ∃ C ∈ earlier ∪ Lstar, C ⊆ E
  contains_new_constraints : (Lstar \ L).image (Finset.map e) ⊆ Fsup

theorem SourceRegularizationOrderResult.toCore
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Nonempty I]
    {ell j b : ℕ} {W : Vortex V ell} {e : I ↪ TripleOn V}
    {L earlier Lstar : Finset (Finset I)} {F Fsup : ForbiddenFamilyOn V} {y z : NNReal}
    (h : SourceRegularizationOrderResult W e j b L earlier F y z Lstar Fsup) :
    RegularizedOrderCore e j b L earlier Lstar Fsup :=
  ⟨h.uniform, h.maximum, h.gap, h.no_earlier_subset, h.covers_original, h.contains_new_constraints⟩

theorem RegularizationOutputWitness.exists_regularizedOrderCore
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Nonempty I]
    {j b : ℕ} (e : I ↪ TripleOn V) (L earlier : Finset (Finset I))
    (hL : ∀ E ∈ L, E.card = j - 2) (R Fsup : ForbiddenFamilyOn V) (hR : R ⊆ Fsup)
    (h : RegularizationOutputWitness e (trimForbiddenSupersets L earlier)
      (regularizationForbiddenFamily e (j - 2) (trimForbiddenSupersets L earlier) earlier) (j - 2) b R) :
    ∃ Lstar, RegularizedOrderCore e j b L earlier Lstar Fsup := by
  obtain ⟨A, hAimage, havoid, hAcard, hmax, hgap⟩ := h
  let G := trimForbiddenSupersets L earlier
  refine ⟨G ∪ A, ?_, ?_, hgap, ?_, ?_, ?_⟩
  · intro E hE
    rcases mem_union.mp hE with hold | hnew
    · exact hL E (trimForbiddenSupersets_subset L earlier hold)
    · exact hAcard E hnew
  · exact hmax.trans (Nat.mul_le_mul_left 9
      (finiteHypergraphMaxDegree_mono (trimForbiddenSupersets_subset L earlier)))
  · exact regularizedFamily_no_earlier_subset e (j - 2) L earlier A hAcard havoid
  · intro E hE
    obtain ⟨C, hC, hCE⟩ := original_contains_earlier_or_trim L earlier E hE
    exact ⟨C, (union_subset_union_right (subset_union_left : G ⊆ G ∪ A)) hC, hCE⟩
  · intro C hC
    obtain ⟨E, hE, rfl⟩ := mem_image.mp hC
    have hEA : E ∈ A := by
      rcases mem_union.mp (mem_sdiff.mp hE).1 with hold | hnew
      · exact ((mem_sdiff.mp hE).2 (trimForbiddenSupersets_subset L earlier hold)).elim
      · exact hnew
    apply hR
    rw [← hAimage]
    exact mem_image.mpr ⟨E, hEA, rfl⟩

end

end Erdos207
