/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshRelevantAllSourceNormalization
import ErdosProblems.Erdos599.SplitGroundingGroundedFreshFullSourceRootTransfer

/-!
# Full-source split-grounding outcome

The source-first relevant frontier is tested in the actual canonical relation
stopped at that frontier.  If all its points are rooted from the ambient
source, the reserved-record geometry removes the distinguished source and the
reachable-sink compiler produces an ambient hindrance.  Otherwise the exact
pointwise failure is immediately fed to the native-frontier normalization.

Thus the remaining separator argument has no hidden global rooting provider:
it receives one concrete normalized exchange leaf.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
    L.freshInessentialGroundStages}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev AllSourceOutcomeInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev AllSourceOutcomeFrontier : Set V :=
  L.splitGroundedRelevantSourceFirstBB hL.legal S.cut

private abbrev AllSourceOutcomeControls :=
  L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

private abbrev AllSourceOutcomeRecord :=
  L.splitGroundedFreshAvoidingCanonicalUnusedRecord
    hL hground hnotFresh S

private abbrev AllSourceOutcomeEdges : Set (V × V) :=
  GroundingErasedDecode.erasedSelectedSwitchedEdgesAt
    (L.splitGroundedPopularAuxiliaryIndexed hL hground) S
    (AllSourceOutcomeControls (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S))
    (AllSourceOutcomeFrontier (L := L) (hL := hL) (S := S))

private abbrev AllSourceOutcomeAllowed : Set V :=
  Gamma.source \ {
    (AllSourceOutcomeRecord (L := L) (hL := hL)
      (hground := hground) (hnotFresh := hnotFresh) (S := S)).record.initial}

/-- On a nonreserved limiting-ladder component, failure of allowed-source
rooting is already failure of rooting from the whole ambient source. -/
theorem splitGroundedFresh_not_rooted_from_source_of_mem_nonreserved_parent
    (parent : Gamma.DPath) (hparent : parent ∈ L.limitWarp)
    (hne : parent ≠
      (AllSourceOutcomeRecord (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S)).record)
    {x : V} (hx : x ∈ parent.support)
    (hnot : ¬ ∃ a ∈ AllSourceOutcomeAllowed
        (L := L) (hL := hL) (hground := hground)
        (hnotFresh := hnotFresh) (S := S),
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ AllSourceOutcomeEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a x) :
    ¬ ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ AllSourceOutcomeEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a x := by
  intro hroot
  apply hnot
  exact L.splitGroundedFresh_root_from_source_avoids_reserved_of_not_mem_record
    (hL := hL) (hground := hground) (hnotFresh := hnotFresh) (S := S)
    (L.splitGroundedFresh_mem_parent_not_mem_reserved
      (hnotFresh := hnotFresh) (S := S) parent hparent hne hx) hroot

/-- The deleted head in a normalized backward state has the same genuine
all-source nonrootedness as its allowed-source certificate, once the state
is known to lie on a nonreserved parent. -/
theorem SplitGroundedFreshRelevantBackwardState.deleted_head_not_rooted_from_source
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (hne : state.parent ≠
      (AllSourceOutcomeRecord (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S)).record) :
    ¬ ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ AllSourceOutcomeEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a state.deleted.head := by
  exact L.splitGroundedFresh_not_rooted_from_source_of_mem_nonreserved_parent
    (hnotFresh := hnotFresh) (S := S) state.parent state.parent_mem hne
    state.deleted_head_mem state.deleted_head_not_rooted

/-- Likewise the endpoint of the current finite root segment remains
unrooted from the whole ambient source. -/
theorem SplitGroundedFreshRelevantBackwardState.rootPath_finish_not_rooted_from_source
    (state : L.SplitGroundedFreshRelevantBackwardState
      (hL := hL) (hground := hground)
      (hnotFresh := hnotFresh) (S := S))
    (hne : state.parent ≠
      (AllSourceOutcomeRecord (L := L) (hL := hL)
        (hground := hground) (hnotFresh := hnotFresh) (S := S)).record) :
    ¬ ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ AllSourceOutcomeEdges
          (L := L) (hL := hL) (hground := hground)
          (hnotFresh := hnotFresh) (S := S)) a state.rootPath.finish := by
  exact L.splitGroundedFresh_not_rooted_from_source_of_mem_nonreserved_parent
    (hnotFresh := hnotFresh) (S := S) state.parent state.parent_mem hne
    (state.rootPath_support state.rootPath.finish_mem_support)
    state.rootPath_finish_not_rooted

/-- The canonical full-source scan either already compiles an ambient
hindrance, or exposes one normalized native-frontier exchange leaf. -/
theorem exists_hindrance_or_splitGroundedFreshRelevantAllSourceNormalizedFailure
    (hC : Popular.IsSeparator
      (AllSourceOutcomeInput (L := L) (hL := hL)).lambda S.cut) :
    (∃ W : Set Gamma.DPath, Gamma.IsHindrance W) ∨
      ∃ t ∈ AllSourceOutcomeFrontier (L := L) (hL := hL) (S := S),
        L.SplitGroundedFreshRelevantAllSourceNormalizedFailureAt
          (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
          (S := S) t := by
  rcases L.splitGroundedFreshRelevantAllSource_rooted_or_failure
      (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
      (S := S) hC with hroot | ⟨t, ht, failure⟩
  · exact Or.inl
      (L.exists_hindrance_of_splitGroundedFreshFrontierRootedFromSource
        (hL := hL) (hground := hground) (hnotFresh := hnotFresh)
        (S := S) hC hroot)
  · exact Or.inr ⟨t, ht, failure.normalize ht⟩

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.exists_hindrance_or_splitGroundedFreshRelevantAllSourceNormalizedFailure
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantBackwardState.deleted_head_not_rooted_from_source
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFreshRelevantBackwardState.rootPath_finish_not_rooted_from_source
