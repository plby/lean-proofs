/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularWeakPayloadPreparation

/-!
# Installing a protected selected/clean continuation

The weak half-way construction first produces a selected target track and a
terminal-clean complementary track.  Advancing the complementary track to a
later frontier preserves every field of `CleanTargetSlice` except joint
disjointness with the frozen selected target track.

This file isolates that exact boundary.  It does not postulate a geometric
provider: given the concrete cross-carrier disjointness statement, the full
later `CleanTargetSlice` is constructed from the already proved target and
clean data.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularWeakProtectedSelectedClean

open SliceSpliceSource

universe u

variable {V : Type u}

/-- Advance the clean half of a selected slice to a new right boundary.
The sole protection premise says that the new clean carrier avoids the
selected target carrier.  Source-purity at selected left vertices follows
from this disjointness; every other source-purity fact comes from the tight
clean linkage. -/
theorem CleanTargetSlice.advanceClean_of_vertexDisjoint
    {Q : DWeb V} {left stop right selected : Set V}
    (S : RegularCompletedPendingSplice.CleanTargetSlice
      Q left stop selected)
    {cleanResult : Set Q.DPath}
    (hclean : TightLinkageBetween Q (left \ selected) right cleanResult)
    (hdisjoint : Disjoint (Q.vertexSet S.target)
      (Q.vertexSet cleanResult)) :
    ∃ S' : RegularCompletedPendingSplice.CleanTargetSlice
        Q left right selected,
      S'.target = S.target ∧ S'.clean = cleanResult := by
  have htargetWarp : Q.IsWarp S.target := by
    intro p hp q hq hpq
    exact S.union_warp (Or.inl hp) (Or.inl hq) hpq
  have htargetFinite : Q.HasFiniteCharacter S.target := by
    intro p hp
    exact S.finiteCharacter (Or.inl hp)
  have hunionWarp : Q.IsWarp (S.target ∪ cleanResult) := by
    apply SingularContinuation.isWarp_union_of_disjoint_vertexSet Q
    · exact htargetWarp
    · exact hclean.1.isWarp
    · exact hdisjoint
  have hunionFinite : Q.HasFiniteCharacter (S.target ∪ cleanResult) :=
    SingularContinuation.finiteCharacter_union Q
      htargetFinite hclean.1.finiteCharacter
  have hsourcePure : ∀ p ∈ S.target ∪ cleanResult,
      p.support ∩ left = {p.initial} := by
    intro p hp
    rcases hp with hpTarget | hpClean
    · exact S.source_pure p (Or.inl hpTarget)
    · obtain ⟨f, rfl, _hends, hfSource⟩ :=
        hclean.1.endpointPure p hpClean
      have hfStart : f.start ∈ left \ selected := by
        rw [← hclean.1.initialSet_eq]
        exact ⟨Sum.inl f, hpClean, rfl⟩
      apply Set.Subset.antisymm
      · rintro x ⟨hxf, hxLeft⟩
        by_cases hxSelected : x ∈ selected
        · have hxTargetInitial : x ∈ Q.initialSet S.target := by
            rw [S.target_initial]
            exact hxSelected
          obtain ⟨q, hqTarget, hqx⟩ := hxTargetInitial
          have hxTargetCarrier : x ∈ Q.vertexSet S.target := by
            refine ⟨q, hqTarget, ?_⟩
            rw [← hqx]
            exact q.initial_mem_support
          have hxCleanCarrier : x ∈ Q.vertexSet cleanResult :=
            ⟨Sum.inl f, hpClean, hxf⟩
          exact (Set.disjoint_left.1 hdisjoint
            hxTargetCarrier hxCleanCarrier).elim
        · have hxSource : x ∈ f.support ∩ (left \ selected) :=
            ⟨hxf, hxLeft, hxSelected⟩
          rw [hfSource] at hxSource
          exact hxSource
      · intro x hx
        have hxfStart : x = f.start := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨f.start_mem_support, hfStart.1⟩
  let S' : RegularCompletedPendingSplice.CleanTargetSlice
      Q left right selected :=
    { target := S.target
      clean := cleanResult
      union_warp := hunionWarp
      finiteCharacter := hunionFinite
      target_initial := S.target_initial
      clean_initial := hclean.1.initialSet_eq
      initial_cover := S.initial_cover
      target_links := S.target_links
      clean_terminal := hclean.1.terminalFrontier_subset
      clean_terminal_only := hclean.2
      source_pure := hsourcePure }
  exact ⟨S', rfl, rfl⟩

end RegularWeakProtectedSelectedClean
end CardinalInduction
end Erdos599
