/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SliceCandidate
import ErdosProblems.Erdos599.LadderSplitProvenance
import ErdosProblems.Erdos599.LadderConstruction
import ErdosProblems.Erdos599.AlternatingTraceOps
import ErdosProblems.Erdos599.BlueprintSplice

/-!
# Ordinary annular-slice members are exact ladder stage intervals

An ordinary member of a frontier-to-frontier linkage is a fragment of one
component of the later accumulated ladder warp.  The two frontier endpoints,
stage growth, and disjointness of the accumulated warps identify its later
owner and the unique earlier essential prefix.  Hence the member is exactly
the interval which appends that prefix to the later component.

The public statement is formulated directly over the bookkeeping-free stage
geometry.  One-sided growth between the displayed stages is explicit.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SliceCandidate

open DirectedPath

universe u

variable {V : Type u}

/-- Two finite fragments of the same finite directed path with the same
endpoints are literally the same path. -/
theorem finitePath_eq_of_common_ambient_subpaths
    {D : Digraph V} (ambient p q : FinitePath D)
    (hp : p.IsSubpathOf (.inl ambient))
    (hq : q.IsSubpathOf (.inl ambient))
    (hstart : p.start = q.start) (hfinish : p.finish = q.finish) :
    p = q := by
  classical
  apply FinitePath.eq_of_start_finish_edgeSet_eq p q hstart hfinish
  rw [Alternating.FinitePath.edgeSet_eq_position_interval ambient p hp,
    Alternating.FinitePath.edgeSet_eq_position_interval ambient q hq,
    hstart, hfinish]

/-- If two adjacent fragments cover a finite ambient path from its first to
its last vertex, their concrete concatenation reconstructs the ambient path.
-/
theorem appendFinite_eq_of_adjacent_ambient_subpaths
    {D : Digraph V} (ambient left right : FinitePath D)
    (hleft : left.IsSubpathOf (.inl ambient))
    (hright : right.IsSubpathOf (.inl ambient))
    (hambientStart : left.start = ambient.start)
    (hjoin : right.start = left.finish)
    (hambientFinish : right.finish = ambient.finish)
    (hinter : left.support ∩ right.support ⊆ {left.finish}) :
    Path.appendFinite left (.inl right) hjoin hinter =
      (.inl ambient : Path D) := by
  classical
  apply congrArg Sum.inl
  apply FinitePath.eq_of_start_finish_edgeSet_eq
  · exact (left.appendFinite_start right hjoin hinter).trans hambientStart
  · exact (left.appendFinite_finish right hjoin hinter).trans hambientFinish
  · rw [Erdos599.Blueprint.LinkageBlueprint.FinitePath.edgeSet_appendFinite]
    apply Set.Subset.antisymm
    · exact Set.union_subset hleft.2 hright.2
    · intro e he
      have heSelf := he
      rw [Alternating.FinitePath.edgeSet_eq_position_interval ambient ambient
        ambient.isSubpathOf_self] at heSelf
      by_cases hpos : ambient.walk.support.idxOf e.1 <
          ambient.walk.support.idxOf right.start
      · apply Or.inl
        rw [Alternating.FinitePath.edgeSet_eq_position_interval ambient left hleft]
        refine ⟨he, ?_, ?_⟩
        · simpa only [hambientStart] using heSelf.2.1
        · simpa only [hjoin] using hpos
      · apply Or.inr
        rw [Alternating.FinitePath.edgeSet_eq_position_interval ambient right hright]
        refine ⟨he, le_of_not_gt hpos, ?_⟩
        simpa only [hambientFinish] using heSelf.2.2

/-- A member of a tight frontier-to-frontier linkage which is already a
fragment of the later warp has the exact causal stage-interval certificate.
Only stage separation and warp geometry are used; obstruction bookkeeping
plays no role. -/
theorem isStageInterval_of_tightLinkage_fragment_of_geometry
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {T : Set Gamma.DPath}
    (hroof : L.RoofsSourceAtStages)
    (hwarp : L.HasWarpStages)
    (hgrows : Gamma.LadderGrows (L.warpAt delta) (L.warpAt beta))
    (hT : SliceSpliceSource.TightLinkageBetween Gamma
      (L.frontier delta) (L.frontier beta) T)
    {p : Gamma.DPath} (hpT : p ∈ T)
    (hpFragment : ControlledSlices.IsLadderFragment
      Gamma (L.warpAt beta) p) :
    IsStageInterval Gamma L delta beta p := by
  obtain ⟨finite, hpfinite⟩ := hT.1.2.1 hpT
  subst p
  have hstartDelta : finite.start ∈ L.frontier delta := by
    rw [← hT.1.2.2.1]
    exact ⟨.inl finite, hpT, rfl⟩
  have hfinishBeta : finite.finish ∈ L.frontier beta := by
    apply hT.1.2.2.2.1
    exact ⟨.inl finite, hpT, rfl⟩
  obtain ⟨owner, hownerBeta, hfiniteOwner⟩ := hpFragment
  have hbetaWarp : Gamma.IsWarp (L.warpAt beta) :=
    hwarp (Ladder.Stage.toExtended beta)
  have hfinishEssential :
      finite.finish ∈ Gamma.essential
        (Gamma.terminalFrontier (L.warpAt beta)) := by
    rw [← L.frontier_eq_essential_terminalFrontier
      hroof beta]
    exact hfinishBeta
  have hownerTerminal : Gamma.terminal? owner = some finite.finish :=
    DWeb.IsWarp.terminal_eq_of_mem_support_mem_terminalFrontier
      Gamma hbetaWarp hownerBeta
      (hfiniteOwner.1 finite.finish_mem_support)
      (Gamma.essential_subset _ hfinishEssential)
  rcases owner with right | ray
  · have hrightFinish : right.finish = finite.finish := by
      simpa only [Gamma.terminal?_finite, Option.some.injEq] using
        hownerTerminal
    have hrightEssential :
        (Sum.inl right : Gamma.DPath) ∈
          Gamma.essentialWarpPart (L.warpAt beta) :=
      ⟨hownerBeta, finite.finish, hownerTerminal, hfinishEssential⟩
    have hstartEssential :
        finite.start ∈ Gamma.essential
          (Gamma.terminalFrontier (L.warpAt delta)) := by
      rw [← L.frontier_eq_essential_terminalFrontier
        hroof delta]
      exact hstartDelta
    have hstartTerminal : finite.start ∈
        Gamma.terminalFrontier
          (Gamma.essentialWarpPart (L.warpAt delta)) := by
      rw [Gamma.terminalFrontier_essentialWarpPart]
      exact hstartEssential
    obtain ⟨leftPath, hleftEssential, hleftTerminal⟩ := hstartTerminal
    rcases leftPath with left | leftRay
    · have hleftFinish : left.finish = finite.start := by
        simpa only [Gamma.terminal?_finite, Option.some.injEq] using
          hleftTerminal
      obtain ⟨later, hlaterBeta, hleftLater⟩ :=
        hgrows (.inl left) hleftEssential.1
      have hlaterOwner : later = (.inl right : Gamma.DPath) := by
        apply Alternating.DWeb.IsWarp.eq_of_mem_support
          hbetaWarp hlaterBeta hownerBeta
        · exact Gamma.support_mono_of_extends hleftLater
            left.finish_mem_support
        · exact hfiniteOwner.1
            (hleftFinish.symm ▸ finite.start_mem_support)
      have hleftRight : Gamma.Extends
          (.inl left : Gamma.DPath) (.inl right) := by
        simpa only [hlaterOwner] using hleftLater
      have hleftPrefix : left.IsPrefixOf right := hleftRight
      have hleftSubpath : left.IsSubpathOf (.inl right) := by
        refine ⟨hleftPrefix.support_subset, ?_⟩
        exact Walk.edgeSet_subset_of_support_prefix left.walk right.walk
          hleftPrefix
      have hfiniteSubpath : finite.IsSubpathOf (.inl right) :=
        hfiniteOwner
      have hinterSubset : left.support ∩ finite.support ⊆ {left.finish} :=
        FinitePath.support_inter_subset_singleton_of_isSubpathOf
          left finite (.inl right) hleftSubpath hfiniteSubpath
          hleftFinish
      have hinterEq : left.support ∩ finite.support = {left.finish} := by
        apply Set.Subset.antisymm hinterSubset
        intro x hx
        have hx' : x = left.finish := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨left.finish_mem_support,
          hleftFinish ▸ finite.start_mem_support⟩
      have happend :
          Path.appendFinite left (.inl finite) hleftFinish.symm hinterSubset =
            (.inl right : Gamma.DPath) := by
        exact appendFinite_eq_of_adjacent_ambient_subpaths
          right left finite hleftSubpath hfiniteSubpath
          hleftPrefix.start_eq hleftFinish.symm hrightFinish.symm hinterSubset
      refine ⟨left, right, finite, rfl, hleftEssential,
        hrightEssential, ?_, ?_, hleftFinish.symm, hinterSubset,
        hinterEq, happend⟩
      · exact hleftFinish ▸ hstartDelta
      · exact hrightFinish ▸ hfinishBeta
    · simp at hleftTerminal
  · simp at hownerTerminal

end SliceCandidate
end CardinalInduction
end Erdos599
