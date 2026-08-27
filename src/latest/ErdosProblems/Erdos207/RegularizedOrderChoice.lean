/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizedOrderCore

/-! # Deterministic order choices with explicit exceptional degree-gap events -/

namespace Erdos207

open Finset

noncomputable section

def regularizedOrderChoice
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Nonempty I]
    (e : I ↪ TripleOn V) (j b : ℕ) (L earlier : Finset (Finset I)) (Fsup : ForbiddenFamilyOn V) :
    Finset (Finset I) := by
  classical
  exact if h : ∃ Lstar, RegularizedOrderCore e j b L earlier Lstar Fsup then h.choose
    else trimForbiddenSupersets L earlier

theorem regularizedOrderChoice_core_of_exists
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Nonempty I]
    (e : I ↪ TripleOn V) (j b : ℕ) (L earlier : Finset (Finset I)) (Fsup : ForbiddenFamilyOn V)
    (h : ∃ Lstar, RegularizedOrderCore e j b L earlier Lstar Fsup) :
    RegularizedOrderCore e j b L earlier (regularizedOrderChoice e j b L earlier Fsup) Fsup := by
  classical
  rw [regularizedOrderChoice, dif_pos h]
  exact h.choose_spec

theorem regularizedOrderChoice_properties
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Nonempty I]
    (e : I ↪ TripleOn V) (j b : ℕ) (L earlier : Finset (Finset I)) (Fsup : ForbiddenFamilyOn V)
    (hL : ∀ E ∈ L, E.card = j - 2) :
    let Lstar := regularizedOrderChoice e j b L earlier Fsup
    (∀ E ∈ Lstar, E.card = j - 2) ∧
    finiteHypergraphMaxDegree Lstar ≤ 9 * finiteHypergraphMaxDegree L ∧
    (∀ E ∈ Lstar, ∀ C ∈ earlier, ¬ C ⊆ E) ∧
    (∀ E ∈ L, ∃ C ∈ earlier ∪ Lstar, C ⊆ E) ∧
    (Lstar \ L).image (Finset.map e) ⊆ Fsup := by
  classical
  dsimp only
  by_cases hex : ∃ Lstar, RegularizedOrderCore e j b L earlier Lstar Fsup
  · have h := regularizedOrderChoice_core_of_exists e j b L earlier Fsup hex
    exact ⟨h.uniform, h.maximum, h.no_earlier_subset, h.covers_original, h.contains_new_constraints⟩
  · rw [regularizedOrderChoice, dif_neg hex]
    have hsub := trimForbiddenSupersets_subset L earlier
    refine ⟨fun E hE ↦ hL E (hsub hE), ?_, ?_, original_contains_earlier_or_trim L earlier, ?_⟩
    · have hmax := finiteHypergraphMaxDegree_mono hsub
      omega
    · intro E hE
      exact ((mem_trimForbiddenSupersets_iff L earlier E).mp hE).2
    · rw [sdiff_eq_empty_iff_subset.mpr hsub, image_empty]
      exact empty_subset _

end

end Erdos207
