/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FixedRandomAllOrders
import ErdosProblems.Erdos207.LocalForbiddenConfiguration
import ErdosProblems.Erdos207.RegularizedForbiddenUnion

/-! # Every actual regularized constraint localizes a fixed ambient source family -/

namespace Erdos207

open Finset

noncomputable section

theorem localForbiddenConfigurations_mono_source
    {V : Type*} [DecidableEq V] {F H : ForbiddenFamilyOn V} (hFH : F ⊆ H)
    (available old : TripleSystemOn V) (j : ℕ) :
    localForbiddenConfigurations F available old j ⊆ localForbiddenConfigurations H available old j := by
  intro S hS
  obtain ⟨hA, hcard, E, hE, hSE, hold⟩ := (mem_localForbiddenConfigurations_iff F available old S j).mp hS
  exact (mem_localForbiddenConfigurations_iff H available old S j).mpr
    ⟨hA, hcard, E, hFH hE, hSE, hold⟩

theorem mem_localForbiddenConfigurations_of_mem
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V} {available old S : TripleSystemOn V} {j : ℕ}
    (hS : S ∈ F) (hA : S ⊆ available) (hcard : S.card = j - 2) :
    S ∈ localForbiddenConfigurations F available old j := by
  apply (mem_localForbiddenConfigurations_iff F available old S j).mpr
  exact ⟨hA, hcard, S, hS, Subset.rfl, by simp⟩

theorem decoded_regularized_localization
    {V I : Type*} [DecidableEq V] [DecidableEq I]
    (e : I ↪ TripleOn V) (j : ℕ) (L Lstar : Finset (Finset I))
    (F H : ForbiddenFamilyOn V) (available old : TripleSystemOn V)
    (hFH : F ⊆ H) (havailable : ∀ i, e i ∈ available)
    (hL : L.image (Finset.map e) ⊆ localForbiddenConfigurations F available old j)
    (huniform : ∀ E ∈ Lstar, E.card = j - 2)
    (hnew : (Lstar \ L).image (Finset.map e) ⊆ H) :
    Lstar.image (Finset.map e) ⊆ localForbiddenConfigurations H available old j := by
  intro S hS
  obtain ⟨E, hE, rfl⟩ := mem_image.mp hS
  by_cases hEL : E ∈ L
  · exact localForbiddenConfigurations_mono_source hFH available old j
      (hL (mem_image.mpr ⟨E, hEL, rfl⟩))
  · apply mem_localForbiddenConfigurations_of_mem
      (hnew (mem_image.mpr ⟨E, mem_sdiff.mpr ⟨hE, hEL⟩, rfl⟩))
    · intro T hT
      obtain ⟨i, _, rfl⟩ := mem_map.mp hT
      exact havailable i
    · simpa only [card_map] using huniform E hE

theorem FixedRandomOrderResult.localizes
    {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    {I : D → Type*} [∀ d, Fintype (I d)] [∀ d, DecidableEq (I d)] [∀ d, Nonempty (I d)]
    {ell j b : ℕ} {P : FiniteLaw D} {W : Vortex V ell} {e : (d : D) → I d ↪ TripleOn V}
    {L earlier Lstar : (d : D) → Finset (Finset (I d))}
    {F C R : ForbiddenFamilyOn V} {y z a rho : NNReal}
    (h : FixedRandomOrderResult P W e j b L earlier F C y z a rho Lstar R)
    (d : D) (F0 H : ForbiddenFamilyOn V) (available old : TripleSystemOn V)
    (hF0 : F0 ⊆ H) (hF : F ∪ R ⊆ H) (havailable : ∀ i, e d i ∈ available)
    (hL : (L d).image (Finset.map (e d)) ⊆ localForbiddenConfigurations F0 available old j) :
    (Lstar d).image (Finset.map (e d)) ⊆ localForbiddenConfigurations H available old j :=
  decoded_regularized_localization (e d) j (L d) (Lstar d) F0 H available old hF0 havailable hL
    (h.uniform d) ((h.contains_new_constraints d).trans hF)

theorem regularizedForbiddenUnion_subset_localized_union
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (e : I ↪ TripleOn V) (q : ℕ) (Lstar : ℕ → Finset (Finset I))
    (H : ForbiddenFamilyOn V) (available old : TripleSystemOn V)
    (h : ∀ j ∈ Icc 4 q, (Lstar j).image (Finset.map e) ⊆ localForbiddenConfigurations H available old j) :
    regularizedForbiddenUnion e q Lstar ⊆
      (Icc 4 q).biUnion (fun j ↦ localForbiddenConfigurations H available old j) := by
  intro S hS
  obtain ⟨E, hE, rfl⟩ := mem_image.mp hS
  obtain ⟨j, hj, hEj⟩ := mem_biUnion.mp hE
  exact mem_biUnion.mpr ⟨j, hj, h j hj (mem_image.mpr ⟨E, hEj, rfl⟩)⟩

theorem FixedRandomOrderResult.decoded_packing
    {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    {I : D → Type*} [∀ d, Fintype (I d)] [∀ d, DecidableEq (I d)] [∀ d, Nonempty (I d)]
    {ell j b : ℕ} {P : FiniteLaw D} {W : Vortex V ell} {e : (d : D) → I d ↪ TripleOn V}
    {L earlier Lstar : (d : D) → Finset (Finset (I d))}
    {F C R : ForbiddenFamilyOn V} {y z a rho : NNReal}
    (h : FixedRandomOrderResult P W e j b L earlier F C y z a rho Lstar R)
    (d : D) (hL : ∀ E ∈ L d, IsPackingOn (E.map (e d))) :
    ∀ E ∈ Lstar d, IsPackingOn (E.map (e d)) := by
  intro E hE
  by_cases hold : E ∈ L d
  · exact hL E hold
  · exact (h.spread.uniform (E.map (e d)) (h.contains_new_constraints d
      (mem_image.mpr ⟨E, mem_sdiff.mpr ⟨hE, hold⟩, rfl⟩))).2

end

end Erdos207
