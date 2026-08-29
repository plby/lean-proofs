/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClause
import ErdosProblems.Erdos599.HalfwayRetainedLaterLinkage
import ErdosProblems.Erdos599.HalfwayStageSafeTarget
import ErdosProblems.Erdos599.SliceSuffixFromAux

/-!
# The source-faithful old-stage path transaction

Assertion 9.31 starts with a scheduled vertex on the old ladder frontier.
Assertion 9.23 supplies a deletion-safe path in the old essential quotient
stage.  The residual stage web is solved by the simultaneous induction
hypotheses, the chosen path is retained in that solution, and the entire
stage linkage is lifted to the ambient web.  Only then is the linkage
stopped at its first hit of the new ladder frontier.

The output keeps both halves of the chosen path.  Its `front` is a literal
member of the old-to-new stopped linkage, while its `tail` is the suffix of
the same deletion-safe ambient target path.  Thus no containment of the
unrelated selected ladder reference is assumed.
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
open _root_.Erdos599.Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}

/-- Normalization is inherited by the essential quotient stage.  This
small local form avoids importing the much later regular candidate
provider merely for this structural fact. -/
private theorem stageWeb_isNormalized_for_oldTransaction
    (hNorm : Gamma.IsNormalized) (L : Gamma.KappaLadder theta)
    (delta : Ladder.Stage theta) :
    (L.stageWeb delta).IsNormalized := by
  intro x y hxy
  let Q := Gamma.quotient
    (Gamma.terminalFrontier (L.warpAt delta))
  have hxyQ : Q.graph.Adj x y := Q.essentialPart_adj_imp hxy
  have hxyGamma : Gamma.graph.Adj x y := Gamma.quotient_adj_imp hxyQ
  refine ⟨?_, (hNorm hxyGamma).2⟩
  have hNoEnterQ : Q.NoEdgeEnters Q.source :=
    DWeb.NoEdgeEnters.quotient (G := Gamma)
      (fun {_ _} e hy ↦ (hNorm e).1 hy)
  exact fun hy ↦ hNoEnterQ hxyQ hy.1

/-- A scheduled path selected in the old essential quotient stage, together
with the full old-frontier linkage retaining it.

`ambient` is the lift of the full stage linkage and `later` is its first-hit
truncation at `C.newSlice`.  The exact splice equation records that `front`
and `tail` are pieces of the safe path chosen by Assertion 9.23. -/
structure OldStageSafePathTransaction
    (C : ClubStageGeometry Gamma Y kappa theta) (z : V) where
  safe : SafeOldStageTargetPath C z
  current : CurrentLaterLinkage C C.oldSlice
  path : FinitePath Gamma.graph
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

namespace OldStageSafePathTransaction

variable {C : ClubStageGeometry Gamma Y kappa theta} {z : V}

/-- The stopped part of the selected path stays in the selected new-stage
roof. -/
theorem front_support_subset_outerRoof
    (T : OldStageSafePathTransaction C z) :
    T.front.support ⊆ C.outerRoof :=
  T.current.later_in_outerRoof _ T.front_mem_later

/-- The stored suffix starts at the new frontier and reaches the original
ambient target. -/
theorem tail_boundary (T : OldStageSafePathTransaction C z) :
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

/-- The front and tail are literal subpaths of the selected safe path. -/
theorem front_support_subset_path
    (T : OldStageSafePathTransaction C z) :
    T.front.support ⊆ T.path.support :=
  T.front_isPrefix.support_subset

theorem tail_support_subset_path
    (T : OldStageSafePathTransaction C z) :
    T.tail.support ⊆ T.path.support := by
  rw [← T.splice_eq,
    T.front.support_appendFinite_eq_union T.tail T.tail_start
      T.front_tail_inter.subset]
  exact Set.subset_union_right

end OldStageSafePathTransaction

/-- The source-faithful Assertion 9.23-to-9.31 transaction.

The only stage-size input is the correct inequality
`#C.oldSlice ≤ kappa`.  Strict inequality is solved by `hlower`; equality
is solved by `hext`.  This avoids the unsupported stronger assertion that
every old ladder frontier has cardinality exactly `kappa`. -/
theorem ClubStageGeometry.exists_oldStageSafePathTransaction
    (C : ClubStageGeometry Gamma Y kappa theta)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hext : UniversalExtensionClauseAt V kappa)
    (holdCard : #C.oldSlice ≤ kappa)
    {z : V} (hz : z ∈ C.oldSlice) :
    Nonempty (OldStageSafePathTransaction C z) := by
  let H : DWeb V := C.ladder.stageWeb C.oldStage
  obtain ⟨S⟩ := C.exists_safeOldStageTargetPath hz
  have hHNorm : H.IsNormalized := by
    exact stageWeb_isNormalized_for_oldTransaction
      C.normalized C.ladder C.oldStage
  have hzH : z ∈ H.source := by
    exact hz
  have hzsub : ({z} : Set V) ⊆ H.source := by
    simpa only [Set.singleton_subset_iff]
  have hresCard :
      #((H.delete (H.vertexSet S.stageFamily)).source) ≤ kappa := by
    apply (Cardinal.mk_subtype_mono ?_).trans holdCard
    exact Set.sdiff_subset
  have hresLinkable :
      IsLinkable (H.delete (H.vertexSet S.stageFamily)) :=
    isLinkable_of_source_mk_le_current hlower hext
      (H.delete (H.vertexSet S.stageFamily)) S.deletion_safe hresCard
  obtain ⟨Wstage, hWstage, hSWstage⟩ :=
    exists_fullLinkage_containing_of_delete_linkable hHNorm hzsub
      S.stage_linkage hresLinkable
  let W : Set Gamma.DPath :=
    SliceSegmentCore.liftStageFamily C.ladder C.oldStage Wstage
  have hW : IsLinkageBetween Gamma C.oldSlice Gamma.target W := by
    exact CardinalInduction.SliceDeltaLift.IsLinkageBetween.liftStageFamily
      hWstage
  have hSafeW : S.ambientFamily ⊆ W := by
    rw [S.ambient_eq_lift]
    rintro _q ⟨q, hq, rfl⟩
    exact ⟨q, hSWstage hq, rfl⟩
  have holdRoof : C.oldSlice ⊆ C.outerRoof :=
    C.legal.frontierChronology C.old_lt_new
  let hsep : RelationalRoof.Separates Gamma.graph.Adj
      C.oldSlice Gamma.target C.newSlice :=
    separates_target_of_subset_roof holdRoof
  let later : Set Gamma.DPath := firstHitPrefixFamily hW hsep
  have hlater : IsLinkageBetween Gamma C.oldSlice C.newSlice later :=
    firstHitPrefixFamily_isLinkageBetween hW hsep
  have hlaterRoof : ∀ q ∈ later, q.support ⊆ C.outerRoof := by
    rintro q hq
    change q ∈ SliceSegmentCore.segmentFamily
      (firstHitSegmentRealization hW hsep) at hq
    obtain ⟨a, rfl⟩ := hq
    exact SliceRestrictedDelta.firstHit_support_subset_roof_ambient
      Gamma C.newSlice (linkageFiniteAt hW a)
      (by simpa only [linkageFiniteAt_start] using holdRoof a.2)
      (linkageFiniteAt_meets hW hsep a)
  have hlaterFragment : ∀ q ∈ later,
      IsLadderFragment Gamma W q := by
    change ∀ q ∈ SliceSegmentCore.segmentFamily
        (firstHitSegmentRealization hW hsep),
      IsLadderFragment Gamma W q
    exact SliceSegmentCore.segmentFamily_isLadderFragment
      (firstHitSegmentRealization hW hsep)
  let D : CurrentLaterLinkage C C.oldSlice := {
    ambient := W
    later := later
    ambient_linkage := hW
    later_linkage := hlater
    later_in_outerRoof := hlaterRoof
    later_is_ambient_fragment := hlaterFragment }
  let a : ({z} : Set V) := ⟨z, Set.mem_singleton z⟩
  let b : C.oldSlice := ⟨z, hz⟩
  let path : FinitePath Gamma.graph :=
    linkageFiniteAt S.ambient_linkage a
  have hpathSafe : (Sum.inl path : Gamma.DPath) ∈ S.ambientFamily := by
    rw [← linkageMemberAt_eq_finite S.ambient_linkage a]
    exact (linkageMemberAt S.ambient_linkage a).2
  have hpathW : (Sum.inl path : Gamma.DPath) ∈ W :=
    hSafeW hpathSafe
  have hmember : (linkageMemberAt hW b).1 =
      (Sum.inl path : Gamma.DPath) := by
    apply Alternating.DWeb.IsWarp.eq_of_mem_support hW.isWarp
      (linkageMemberAt hW b).2 hpathW
    · exact (linkageMemberAt hW b).1.initial_mem_support
    · have hinit : (linkageMemberAt hW b).1.initial = z := by
        simpa only [b] using linkageMemberAt_initial hW b
      have hpathStart : path.start = z := by
        simpa only [path, a] using linkageFiniteAt_start S.ambient_linkage a
      rw [hinit, ← hpathStart]
      exact path.start_mem_support
  have hfinite : linkageFiniteAt hW b = path := by
    have hm := linkageMemberAt_eq_finite hW b
    rw [hmember] at hm
    exact Sum.inl.inj hm.symm
  let front : FinitePath Gamma.graph := linkageFirstHitAt hW hsep b
  have hfrontLater : (Sum.inl front : Gamma.DPath) ∈ later :=
    ⟨b, rfl⟩
  have hfrontPath : front.IsPrefixOf path := by
    have hpref : (linkageFirstHitAt hW hsep b).IsPrefixOf
        (linkageFiniteAt hW b) :=
      (linkageFiniteAt hW b).walk.firstHit C.newSlice
        (linkageFiniteAt_meets hW hsep b) |>.support_prefix
    simpa only [front, hfinite] using hpref
  let hfinish : front.finish ∈ path.support :=
    hfrontPath.support_subset front.finish_mem_support
  let tail : FinitePath Gamma.graph :=
    path.suffixFromAux front.finish hfinish
  obtain ⟨htailStart, _hinter, hinterEq, hsplice⟩ :=
    appendFinite_suffixFromAux_eq_of_prefix hfrontPath
  exact ⟨{
    safe := S
    current := D
    path := path
    path_mem_safe := hpathSafe
    path_mem_ambient := hpathW
    path_start := by
      simpa only [path, a] using linkageFiniteAt_start S.ambient_linkage a
    path_finish := linkageFiniteAt_finish_mem S.ambient_linkage a
    front := front
    front_mem_later := hfrontLater
    front_start := by
      simpa only [front, b] using linkageFirstHitAt_start hW hsep b
    front_finish_mem := linkageFirstHitAt_finish_mem hW hsep b
    front_slice_pure := linkageFirstHitAt_targetPure hW hsep b
    front_isPrefix := hfrontPath
    tail := tail
    tail_start := htailStart
    front_tail_inter := hinterEq
    splice_eq := hsplice }⟩

end LinkageBlueprint
end Blueprint
end Erdos599
