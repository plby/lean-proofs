/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayRetainedLaterLinkage
import ErdosProblems.Erdos599.HalfwayStageSafeTarget
import ErdosProblems.Erdos599.SliceSuffixFromAux

/-!
# A singleton old-stage transaction

The unit used by Assertion 9.31 does not have to complete the whole old
ladder frontier.  Assertion 9.23 already supplies an ambient singleton
linkage from the scheduled old-frontier vertex to the target.  Stopping that
linkage at its first visit to the new frontier gives the required real front,
and the complementary suffix is retained verbatim.

This construction deliberately has no cardinality hypothesis on the old
frontier.  A global scheduler may accumulate these singleton transactions
one request at a time.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath
open CardinalInduction
open CardinalInduction.ControlledSlices
open CardinalInduction.SliceCandidate

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}

/-- The source-faithful one-request form of Assertion 9.31. -/
structure OldStageSingletonTransaction
    (C : ClubStageGeometry Gamma Y kappa theta) (z : V) where
  safe : SafeOldStageTargetPath C z
  current : CurrentLaterLinkage C ({z} : Set V)
  /-- The local ambient row is the deletion-safe singleton family itself. -/
  ambient_eq_safe : current.ambient = safe.ambientFamily
  path : FinitePath Gamma.graph
  /-- The scheduled path is literally the member of the deletion-safe
  family, not merely a path with the same endpoints. -/
  path_mem_safe : (Sum.inl path : Gamma.DPath) ∈ safe.ambientFamily
  path_mem_ambient : (Sum.inl path : Gamma.DPath) ∈ current.ambient
  path_start : path.start = z
  path_finish : path.finish ∈ Gamma.target
  front : FinitePath Gamma.graph
  front_mem_later : (Sum.inl front : Gamma.DPath) ∈ current.later
  front_start : front.start = z
  front_finish_mem : front.finish ∈ C.newSlice
  front_slice_pure : front.support ∩ C.newSlice = {front.finish}
  front_isPrefix : front.IsPrefixOf path
  tail : FinitePath Gamma.graph
  tail_start : tail.start = front.finish
  front_tail_inter : front.support ∩ tail.support = {front.finish}
  splice_eq : front.appendFinite tail tail_start
      front_tail_inter.subset = path

namespace OldStageSingletonTransaction

variable {C : ClubStageGeometry Gamma Y kappa theta} {z : V}

theorem front_support_subset_outerRoof
    (T : OldStageSingletonTransaction C z) :
    T.front.support ⊆ C.outerRoof :=
  T.current.later_in_outerRoof _ T.front_mem_later

theorem tail_boundary (T : OldStageSingletonTransaction C z) :
    T.tail.start ∈ C.newSlice ∧ T.tail.finish ∈ Gamma.target := by
  refine ⟨T.tail_start.symm ▸ T.front_finish_mem, ?_⟩
  have hfinish : T.tail.finish = T.path.finish := by
    calc
      T.tail.finish =
          (T.front.appendFinite T.tail T.tail_start
            T.front_tail_inter.subset).finish :=
        (T.front.appendFinite_finish T.tail T.tail_start
          T.front_tail_inter.subset).symm
      _ = T.path.finish := congrArg FinitePath.finish T.splice_eq
  exact hfinish.symm ▸ T.path_finish

theorem front_support_subset_path
    (T : OldStageSingletonTransaction C z) :
    T.front.support ⊆ T.path.support :=
  T.front_isPrefix.support_subset

theorem tail_support_subset_path
    (T : OldStageSingletonTransaction C z) :
    T.tail.support ⊆ T.path.support := by
  rw [← T.splice_eq,
    T.front.support_appendFinite_eq_union T.tail T.tail_start
      T.front_tail_inter.subset]
  exact Set.subset_union_right

end OldStageSingletonTransaction

/-- Assertion 9.23 followed directly by first-hit truncation.  No full
old-frontier linkage and hence no bound on `#C.oldSlice` is used. -/
theorem ClubStageGeometry.exists_oldStageSingletonTransaction
    (C : ClubStageGeometry Gamma Y kappa theta)
    {z : V} (hz : z ∈ C.oldSlice) :
    Nonempty (OldStageSingletonTransaction C z) := by
  obtain ⟨S⟩ := C.exists_safeOldStageTargetPath hz
  let W : Set Gamma.DPath := S.ambientFamily
  have hW : IsLinkageBetween Gamma ({z} : Set V) Gamma.target W :=
    S.ambient_linkage
  have hzRoof : z ∈ C.outerRoof :=
    C.legal.frontierChronology C.old_lt_new hz
  have hsourceRoof : ({z} : Set V) ⊆ C.outerRoof := by
    simpa only [Set.singleton_subset_iff]
  let hsep : RelationalRoof.Separates Gamma.graph.Adj
      ({z} : Set V) Gamma.target C.newSlice :=
    separates_target_of_subset_roof hsourceRoof
  let later : Set Gamma.DPath := firstHitPrefixFamily hW hsep
  have hlater : IsLinkageBetween Gamma ({z} : Set V) C.newSlice later :=
    firstHitPrefixFamily_isLinkageBetween hW hsep
  have hlaterRoof : ∀ q ∈ later, q.support ⊆ C.outerRoof := by
    rintro q hq
    change q ∈ SliceSegmentCore.segmentFamily
      (firstHitSegmentRealization hW hsep) at hq
    obtain ⟨a, rfl⟩ := hq
    exact SliceRestrictedDelta.firstHit_support_subset_roof_ambient
      Gamma C.newSlice (linkageFiniteAt hW a)
      (by
        simpa only [linkageFiniteAt_start] using hsourceRoof a.2)
      (linkageFiniteAt_meets hW hsep a)
  have hlaterFragment : ∀ q ∈ later,
      IsLadderFragment Gamma W q := by
    change ∀ q ∈ SliceSegmentCore.segmentFamily
        (firstHitSegmentRealization hW hsep),
      IsLadderFragment Gamma W q
    exact SliceSegmentCore.segmentFamily_isLadderFragment
      (firstHitSegmentRealization hW hsep)
  let D : CurrentLaterLinkage C ({z} : Set V) := {
    ambient := W
    later := later
    ambient_linkage := hW
    later_linkage := hlater
    later_in_outerRoof := hlaterRoof
    later_is_ambient_fragment := hlaterFragment }
  let a : ({z} : Set V) := ⟨z, Set.mem_singleton z⟩
  let path : FinitePath Gamma.graph := linkageFiniteAt hW a
  have hpathW : (Sum.inl path : Gamma.DPath) ∈ W := by
    rw [← linkageMemberAt_eq_finite hW a]
    exact (linkageMemberAt hW a).2
  let front : FinitePath Gamma.graph := linkageFirstHitAt hW hsep a
  have hfrontLater : (Sum.inl front : Gamma.DPath) ∈ later :=
    ⟨a, rfl⟩
  have hfrontPath : front.IsPrefixOf path :=
    (linkageFiniteAt hW a).walk.firstHit C.newSlice
      (linkageFiniteAt_meets hW hsep a) |>.support_prefix
  let hfinish : front.finish ∈ path.support :=
    hfrontPath.support_subset front.finish_mem_support
  let tail : FinitePath Gamma.graph :=
    path.suffixFromAux front.finish hfinish
  obtain ⟨htailStart, _hinter, hinterEq, hsplice⟩ :=
    appendFinite_suffixFromAux_eq_of_prefix hfrontPath
  exact ⟨{
    safe := S
    current := D
    ambient_eq_safe := rfl
    path := path
    path_mem_safe := hpathW
    path_mem_ambient := hpathW
    path_start := by
      simpa only [path, a] using linkageFiniteAt_start hW a
    path_finish := linkageFiniteAt_finish_mem hW a
    front := front
    front_mem_later := hfrontLater
    front_start := by
      simpa only [front, a] using linkageFirstHitAt_start hW hsep a
    front_finish_mem := linkageFirstHitAt_finish_mem hW hsep a
    front_slice_pure := linkageFirstHitAt_targetPure hW hsep a
    front_isPrefix := hfrontPath
    tail := tail
    tail_start := htailStart
    front_tail_inter := hinterEq
    splice_eq := hsplice }⟩

#print axioms ClubStageGeometry.exists_oldStageSingletonTransaction

end LinkageBlueprint
end Blueprint
end Erdos599
