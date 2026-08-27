/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceNibbleWitnessCard
import ErdosProblems.Erdos207.SourceGraphMixedLaw

/-! # Actual local forbidden configurations and their mixed witnesses -/

namespace Erdos207

open Finset

noncomputable section

def localForbiddenConfigurations
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V)
    (available old : TripleSystemOn V) (j : ℕ) : ForbiddenFamilyOn V := by
  classical
  exact (available.powersetCard (j - 2)).filter (fun S ↦ ∃ E ∈ F, S ⊆ E ∧ E \ S ⊆ old)

theorem mem_localForbiddenConfigurations_iff
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V)
    (available old S : TripleSystemOn V) (j : ℕ) :
    S ∈ localForbiddenConfigurations F available old j ↔
      S ⊆ available ∧ S.card = j - 2 ∧ ∃ E ∈ F, S ⊆ E ∧ E \ S ⊆ old := by
  classical
  simp only [localForbiddenConfigurations, mem_filter, mem_powersetCard, and_assoc]

theorem localForbiddenConfigurations_uniform
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V)
    (available old : TripleSystemOn V) (j : ℕ) :
    ∀ S ∈ localForbiddenConfigurations F available old j, S.card = j - 2 := by
  intro S hS
  exact ((mem_localForbiddenConfigurations_iff F available old S j).mp hS).2.1

theorem sourceNibbleRemaining_complement
    {V : Type*} [DecidableEq V] (T : TripleOn V) {S E : TripleSystemOn V} (hSE : S ⊆ E) :
    sourceNibbleRemaining T (E, E \ S) = S \ {T} := by
  ext U
  simp only [sourceNibbleRemaining, mem_sdiff, mem_singleton]
  constructor
  · intro h
    exact ⟨by by_contra hnot; exact h.2 ⟨h.1.1, hnot⟩, h.1.2⟩
  · intro h
    exact ⟨⟨hSE h.1, h.2⟩, fun hn ↦ hn.2 h.1⟩

theorem localForbidden_sourceNibbleCode
    {V : Type*} [Fintype V] [DecidableEq V] {ell j j' : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V)
    (huniform : ∀ E ∈ F, E.card = j' - 2) (hj : 4 ≤ j) (hjj : j ≤ j')
    (T : TripleOn V) (S E : TripleSystemOn V) (hEF : E ∈ F) (hSE : S ⊆ E)
    (hS : S.card = j - 2) (hT : T ∈ S)
    (hterminal : ∀ U ∈ S, W.level U = Fin.last ell) :
    (E, E \ S) ∈ sourceNibbleCodes W F T j j' := by
  apply mem_terminalOmissionCodes_iff.mpr
  refine ⟨mem_familyExtensions_iff.mpr ⟨hEF, singleton_subset_iff.mpr (hSE hT)⟩,
    mem_terminalRemainderChoices_iff.mpr ⟨?_, ?_, ?_⟩⟩
  · intro U hU
    have hm := mem_sdiff.mp hU
    exact mem_sdiff.mpr ⟨hm.1, fun heq ↦ hm.2 (mem_singleton.mp heq ▸ hT)⟩
  · rw [card_sdiff_of_subset hSE, huniform E hEF, hS]
    omega
  · change ∀ U ∈ sourceNibbleRemaining T (E, E \ S), W.level U = Fin.last ell
    rw [sourceNibbleRemaining_complement T hSE]
    exact fun U hU ↦ hterminal U (mem_sdiff.mp hU).1

theorem localForbidden_sourceNibbleCoordinates_selected
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (initial later : TripleSystemOn V) (T : TripleOn V)
    (S E : TripleSystemOn V) (hSE : S ⊆ E) (hold : E \ S ⊆ initial ∪ later)
    (hedges : ∀ U ∈ S, ∀ e ∈ tripleEdgeFinset U,
      e ∈ graphEdges G ∧ e ∉ (coveredGraph initial).edgeSet) :
    sourceNibbleCoordinates T (E, E \ S) ⊆
      sourceGraphMixedSelected G (fun _ : Unit ↦ initial) (fun _ ↦ later) () := by
  rw [sourceGraphMixedSelected_subset_iff]
  simp only [sourceNibbleCoordinates, toLeft_disjSum, toRight_disjSum]
  rw [sourceNibbleRemaining_complement T hSE]
  refine ⟨hold, ?_, ?_⟩
  · intro e he
    obtain ⟨U, hU, heU⟩ := mem_biUnion.mp he
    exact (hedges U (mem_sdiff.mp hU).1 e heU).1
  · intro e he
    obtain ⟨U, hU, heU⟩ := mem_biUnion.mp he
    exact (hedges U (mem_sdiff.mp hU).1 e heU).2

end

end Erdos207
