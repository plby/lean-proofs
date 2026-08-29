/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularCandidateProvider
import ErdosProblems.Erdos599.RegularCompletedPendingSplice

/-!
# Provider adapter for the regular completed/pending splice

The local provider produces a small target-ending family and a clean linkage
on the complementary sources.  This file packages that output in the
two-track slice interface consumed by `RegularCompletedPendingSplice`.

The adapter is deliberately local.  Disjointness from target paths frozen at
*earlier* recursion stages remains the explicit `cross_disjoint` obligation of
`IsCleanTargetStep`.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularCompletedPendingSplice

open SliceSpliceSource SingularExtension

universe u

variable {V : Type u}

/-- The completed/pending split supplied by the regular candidate provider is
an honest `CleanTargetSlice`.  The returned side conditions record the small
completed part and its containment in the completed part of the original
row. -/
theorem exists_cleanTargetSlice_of_linkage
    {kappa : Cardinal.{u}} (Q : DWeb V)
    {C U : Set V} {W : Set Q.DPath}
    (hNorm : Q.IsNormalized)
    (hW : IsLinkageBetween Q Q.source C W)
    (hUsource : U ⊆ Q.source)
    (hlinks : LinksToTarget Q W U) (hUsmall : #U < kappa) :
    ∃ S : CleanTargetSlice Q Q.source C U,
      #S.target < kappa ∧
        S.target ⊆ completedPart Q W := by
  obtain ⟨K, P, hKcompleted, hKlinks, hKinitial, hKsmall,
      hP, hPclean, hKPdisjoint⟩ :=
    RegularCandidateProvider.exists_completedPending_split
      Q hNorm hW hUsource hlinks hUsmall
  have hKwarp : Q.IsWarp K := by
    intro p hp q hq hpq
    exact hW.isWarp (hKcompleted hp).1 (hKcompleted hq).1 hpq
  have hKfinite : Q.HasFiniteCharacter K := by
    intro p hp
    exact hW.finiteCharacter (hKcompleted hp).1
  have hUnionWarp : Q.IsWarp (K ∪ P) :=
    SingularContinuation.isWarp_union_of_disjoint_vertexSet Q
      hKwarp hP.isWarp hKPdisjoint
  have hUnionFinite : Q.HasFiniteCharacter (K ∪ P) :=
    SingularContinuation.finiteCharacter_union Q hKfinite hP.finiteCharacter
  have hsourcePure : ∀ p ∈ K ∪ P,
      p.support ∩ Q.source = {p.initial} := by
    intro p hp
    have hpInitialSource : p.initial ∈ Q.source := by
      rcases hp with hpK | hpP
      · apply hUsource
        rw [← hKinitial]
        exact ⟨p, hpK, rfl⟩
      · exact Set.sdiff_subset <| by
          rw [← hP.initialSet_eq]
          exact ⟨p, hpP, rfl⟩
    apply Set.Subset.antisymm
    · rintro x ⟨hxp, hxSource⟩
      exact Set.mem_singleton_iff.2
        (hNorm.eq_initial_of_mem_path p hxp hxSource)
    · intro x hx
      have hxp : x = p.initial := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨p.initial_mem_support, hpInitialSource⟩
  let S : CleanTargetSlice Q Q.source C U :=
    { target := K
      clean := P
      union_warp := hUnionWarp
      finiteCharacter := hUnionFinite
      target_initial := hKinitial
      clean_initial := hP.initialSet_eq
      initial_cover := hUsource
      target_links := hKlinks
      clean_terminal := hP.terminalFrontier_subset
      clean_terminal_only := hPclean
      source_pure := hsourcePure }
  exact ⟨S, hKsmall, hKcompleted⟩

end RegularCompletedPendingSplice
end CardinalInduction
end Erdos599
