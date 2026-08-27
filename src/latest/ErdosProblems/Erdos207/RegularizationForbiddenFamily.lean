/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.NonDisjointConfigurationDegree
import ErdosProblems.Erdos207.TerminalRandomConfigurations

/-! # Actual forbidden families and safe removal of smaller supersets -/

namespace Erdos207

open Finset

noncomputable section

def trimForbiddenSupersets
    {I : Type*} [DecidableEq I] (F earlier : Finset (Finset I)) : Finset (Finset I) := by
  classical
  exact F.filter (fun E ↦ ∀ C ∈ earlier, ¬ C ⊆ E)

theorem mem_trimForbiddenSupersets_iff
    {I : Type*} [DecidableEq I] (F earlier : Finset (Finset I)) (E : Finset I) :
    E ∈ trimForbiddenSupersets F earlier ↔ E ∈ F ∧ ∀ C ∈ earlier, ¬ C ⊆ E := by
  classical
  simp only [trimForbiddenSupersets, mem_filter]

theorem trimForbiddenSupersets_subset
    {I : Type*} [DecidableEq I] (F earlier : Finset (Finset I)) :
    trimForbiddenSupersets F earlier ⊆ F := filter_subset _ _

theorem trimForbiddenSupersets_disjoint_supersets
    {I : Type*} [Fintype I] [DecidableEq I] (F earlier : Finset (Finset I)) (k : ℕ) :
    Disjoint (trimForbiddenSupersets F earlier) (uniformSupersets k earlier) := by
  classical
  apply disjoint_left.mpr
  intro E hE hbad
  obtain ⟨_hcard, C, hC, hCE⟩ := (mem_uniformSupersets_iff k earlier E).mp hbad
  exact ((mem_trimForbiddenSupersets_iff F earlier E).mp hE).2 C hC hCE

theorem avoids_original_of_avoids_trim
    {I : Type*} [DecidableEq I] (F earlier : Finset (Finset I)) (M : Finset I)
    (hearlier : ∀ C ∈ earlier, ¬ C ⊆ M)
    (htrim : ∀ E ∈ trimForbiddenSupersets F earlier, ¬ E ⊆ M) :
    ∀ E ∈ F, ¬ E ⊆ M := by
  classical
  intro E hE hEM
  apply htrim E ((mem_trimForbiddenSupersets_iff F earlier E).mpr ⟨hE, ?_⟩) hEM
  intro C hC hCE
  exact hearlier C hC (hCE.trans hEM)

theorem auxiliary_nonCandidate_mem_collision
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] {ell j : ℕ}
    (W : Vortex V ell) (e : I ↪ TripleOn V)
    (hsupport : ∀ i, (e i).1 ⊆ W.U (Fin.last ell)) (E : Finset I)
    (hcard : E.card = j - 2) (hbad : E.map e ∉ terminalRandomConfigurations W j) :
    E ∈ auxiliaryNonDisjointFamily e (j - 2) := by
  rw [mem_auxiliaryNonDisjointFamily_iff]
  refine ⟨hcard, fun hp ↦ hbad ?_⟩
  apply (mem_terminalRandomConfigurations_iff W (E.map e)).mpr
  refine ⟨?_, by simpa only [card_map] using hcard, ?_⟩
  · intro T hT
    obtain ⟨i, _hi, rfl⟩ := mem_map.mp hT
    exact mem_triplesSupportedOn_iff.mpr (hsupport i)
  · intro T hT T' hT' hne
    obtain ⟨i, hi, rfl⟩ := mem_map.mp hT
    obtain ⟨i', hi', rfl⟩ := mem_map.mp hT'
    exact hp hi hi' (fun heq ↦ hne (congrArg e heq))

def regularizationForbiddenFamily
    {V I : Type*} [DecidableEq V] [Fintype I] [DecidableEq I]
    (e : I ↪ TripleOn V) (k : ℕ) (G earlier : Finset (Finset I)) : Finset (Finset I) :=
  auxiliaryNonDisjointFamily e k ∪ uniformSupersets k earlier ∪ G

theorem subset_regularizationForbiddenFamily
    {V I : Type*} [DecidableEq V] [Fintype I] [DecidableEq I]
    (e : I ↪ TripleOn V) (k : ℕ) (G earlier : Finset (Finset I)) :
    G ⊆ regularizationForbiddenFamily e k G earlier := subset_union_right

theorem regularizationForbiddenFamily_contains_nonCandidates
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] {ell j : ℕ}
    (W : Vortex V ell) (e : I ↪ TripleOn V)
    (hsupport : ∀ i, (e i).1 ⊆ W.U (Fin.last ell)) (G earlier : Finset (Finset I)) :
    ∀ E : Finset I, E.card = j - 2 → E.map e ∉ terminalRandomConfigurations W j →
      E ∈ regularizationForbiddenFamily e (j - 2) G earlier := by
  intro E hcard hbad
  exact mem_union_left _ (mem_union_left _ (auxiliary_nonCandidate_mem_collision W e hsupport E hcard hbad))

theorem regularizedFamily_no_earlier_subset
    {V I : Type*} [DecidableEq V] [Fintype I] [DecidableEq I]
    (e : I ↪ TripleOn V) (k : ℕ) (F earlier R : Finset (Finset I))
    (huniform : ∀ E ∈ R, E.card = k)
    (havoid : Disjoint R (regularizationForbiddenFamily e k (trimForbiddenSupersets F earlier) earlier)) :
    ∀ E ∈ trimForbiddenSupersets F earlier ∪ R, ∀ C ∈ earlier, ¬ C ⊆ E := by
  classical
  intro E hE C hC hCE
  rcases mem_union.mp hE with hold | hnew
  · exact ((mem_trimForbiddenSupersets_iff F earlier E).mp hold).2 C hC hCE
  · have hsup : E ∈ uniformSupersets k earlier :=
      (mem_uniformSupersets_iff k earlier E).mpr ⟨huniform E hnew, C, hC, hCE⟩
    exact disjoint_left.mp havoid hnew (mem_union_left _ (mem_union_right _ hsup))

end

end Erdos207
