/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshAvoidingControls
import ErdosProblems.Erdos599.SplitGroundingGroundedCutAvoidingRecord
import ErdosProblems.Erdos599.GroundingErasedCarrierRank

/-!
# A cut-avoiding reserved record is disjoint from every selected route

The reserved selector excludes the complete Lambda trace of the omitted
record away from a request apex.  If that trace avoids the popular cut, the
apex is excluded as well.  The only decoded carrier not visible in the trace
is an initial proxy; the grounded source-representation certificate identifies
that proxy with the separately reserved auxiliary source.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath Stationary PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedCarrierRank GroundingErasedSwitchRelation
open PopularAuxiliary.Input

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev ReservedInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev ReservedIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private theorem directionEdge_endpoints_mem_vertexSet
    {D : Digraph V} (Q : Alternating.AltPath D)
    {d : Alternating.Direction} {e : V × V}
    (he : e ∈ Q.directionEdges d) :
    e.1 ∈ Q.vertexSet ∧ e.2 ∈ Q.vertexSet := by
  simp only [Alternating.AltPath.directionEdges, Set.mem_iUnion] at he
  obtain ⟨l, hlQ, _hld, hel⟩ := he
  have hend := l.path.edgeSet_subset_support_prod hel
  cases Q with
  | trivial v => simp [Alternating.AltPath.links] at hlQ
  | finite Q =>
      obtain ⟨j, rfl⟩ := hlQ
      exact ⟨Set.mem_iUnion.2 ⟨j, hend.1⟩,
        Set.mem_iUnion.2 ⟨j, hend.2⟩⟩
  | infinite Q =>
      obtain ⟨j, rfl⟩ := hlQ
      exact ⟨Set.mem_iUnion.2 ⟨j, hend.1⟩,
        Set.mem_iUnion.2 ⟨j, hend.2⟩⟩

/-- Every compressed route selected after reserving `R` is vertex-disjoint
from the represented original record, provided its complete Lambda trace
avoids the popular cut. -/
theorem splitGroundedReservedControlsFrom_selectedRoute_disjoint_record
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hcut : Disjoint (PopularSwitching.ladderTrace
      (ReservedInput (L := L) (hL := hL)) R.record) S.cut)
    (r : Request (ReservedInput (L := L) (hL := hL)) S.cut) :
    Disjoint
      (selectedErasedCompression
        (ReservedIndexed (L := L) (hL := hL) (hground := hground)) S
        (splitGroundedReservedControlsFrom R) r).path.vertexSet
      R.record.support := by
  let J := ReservedInput (L := L) (hL := hL)
  let U := ReservedIndexed (L := L) (hL := hL) (hground := hground)
  let K' := splitGroundedReservedControlsFrom R
  let p := strongSelectedPath U S K' r
  have hpStart : p.start ∈ J.lambda.source :=
    (strongSelectedWarp U S K').starts_in_source ⟨r, rfl⟩
  apply Set.disjoint_left.mpr
  intro x hxRoute hxRecord
  have hxDecoded : x ∈ J.decodedVertexCarrier p :=
    selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
      U S K' r hxRoute
  simp only [PopularAuxiliary.Input.decodedVertexCarrier,
    Set.mem_iUnion] at hxDecoded
  obtain ⟨a, haPath, hxa⟩ := hxDecoded
  rcases J.gadget_mem_ladderTrace_or_proxy_eq_of_mem_carrier_of_mem_support
      (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
      p hpStart haPath R.limit_inessential.1 hxa hxRecord with
    haTrace | ⟨i, haProxy, hproxyRecord⟩
  · have haNotApex : a ≠ requestAuxVertex r := by
      intro haApex
      exact Set.disjoint_left.mp hcut haTrace
        (haApex ▸ requestAuxVertex_mem_cut r)
    exact (splitGroundedReservedControlsFrom_no_offApex_contact
      R r (Or.inl haTrace) haNotApex) haPath
  · have hpStartProxy : p.start = LambdaVertex.proxy i :=
      J.proxy_mem_support_eq_start p hpStart (haProxy ▸ haPath)
    rcases R.source_represents with
      ⟨q, hrecordFinite, _hsourceFinite⟩ |
      ⟨j, hrecordInfinite, hsourceProxy⟩
    · obtain ⟨ray, hproxyRay⟩ := J.proxy_isRay i
      have : (Sum.inr ray : Gamma.DPath) = Sum.inl q := by
        exact hproxyRay.symm.trans (hproxyRecord.trans hrecordFinite)
      cases this
    · have hij : i = j := by
        apply Subtype.ext
        simpa only [J, ReservedInput, splitGroundedPopularAuxiliaryInput,
          splitGroundedInfinitePath] using
          hproxyRecord.trans hrecordInfinite
      apply splitGroundedReservedControlsFrom_start_ne_reservedSource R r
      rw [hpStartProxy, hij, hsourceProxy]

/-- Every selected direction edge for the reserved controls has both
endpoints outside the represented record.  This includes inactive directions
only after they enter the active union at the supplied stopping frontier. -/
theorem splitGroundedReservedControlsFrom_directionEdgeAt_endpoints_not_mem_record
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hcut : Disjoint (PopularSwitching.ladderTrace
      (ReservedInput (L := L) (hL := hL)) R.record) S.cut)
    (T : Set V) (d : Alternating.Direction) {e : V × V}
    (he : e ∈ erasedSelectedDirectionEdgesAt
      (ReservedIndexed (L := L) (hL := hL) (hground := hground)) S
      (splitGroundedReservedControlsFrom R) T d) :
    e.1 ∉ R.record.support ∧ e.2 ∉ R.record.support := by
  simp only [erasedSelectedDirectionEdgesAt, Set.mem_iUnion] at he
  obtain ⟨c, he⟩ := he
  have hend := directionEdge_endpoints_mem_vertexSet
    (selectedErasedCompression
      (ReservedIndexed (L := L) (hL := hL) (hground := hground)) S
      (splitGroundedReservedControlsFrom R) (chosenRequest c.1)).path he
  have hdisjoint :=
    splitGroundedReservedControlsFrom_selectedRoute_disjoint_record
      R hcut (chosenRequest c.1)
  exact ⟨fun h ↦ Set.disjoint_left.mp hdisjoint hend.1 h,
    fun h ↦ Set.disjoint_left.mp hdisjoint hend.2 h⟩

/-- Every original edge of a cut-avoiding reserved record survives the
actual stopped simultaneous switch, as long as the stopping frontier lies
in the relevant grounding frontier. -/
theorem SplitGroundedUnusedRecord.edgeSet_subset_reservedSwitchedEdgesAt
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hcut : Disjoint (PopularSwitching.ladderTrace
      (ReservedInput (L := L) (hL := hL)) R.record) S.cut)
    (T : Set V) (hT : T ⊆ L.splitGroundedRelevantBB hL.legal S.cut) :
    R.record.edgeSet ⊆ erasedSelectedSwitchedEdgesAt
      (ReservedIndexed (L := L) (hL := hL) (hground := hground)) S
      (splitGroundedReservedControlsFrom R) T := by
  let J := ReservedInput (L := L) (hL := hL)
  let U := ReservedIndexed (L := L) (hL := hL) (hground := hground)
  let K' := splitGroundedReservedControlsFrom R
  intro e heRecord
  have heFamily : e ∈ J.familyEdges := by
    change ∃ Y ∈ J.ladder.paths, e ∈ Y.edgeSet
    exact ⟨R.record, R.limit_inessential.1, heRecord⟩
  have heNotCE : e ∉ GroundingCut.CE J S.cut := by
    exact fun he ↦ Set.disjoint_left.mp
      (R.edgeSet_disjoint_CE_of_trace_disjoint hcut) heRecord he
  have heResidual : e ∈ residualLadderEdges U S :=
    ⟨heFamily, heNotCE⟩
  left
  refine ⟨heResidual, ?_⟩
  simp only [erasedSelectedToggleEdgesAt, Set.mem_union]
  rintro (heBackward | heConflict | heBoundary)
  · exact
      (splitGroundedReservedControlsFrom_directionEdgeAt_endpoints_not_mem_record
        R hcut T .backward heBackward).1
        (R.record.edgeSet_subset_support_prod heRecord).1
  · obtain ⟨_heResidual, f, hfRetained, hef⟩ := heConflict
    have hfForward : f ∈ erasedSelectedDirectionEdgesAt U S K' T .forward :=
      erasedSelectedRetainedForwardEdgesAt_subset_forward U S K' T hfRetained
    have hfOutside :=
      splitGroundedReservedControlsFrom_directionEdgeAt_endpoints_not_mem_record
        R hcut T .forward hfForward
    rcases hef with htail | hhead
    · exact hfOutside.1
        (htail ▸ (R.record.edgeSet_subset_support_prod heRecord).1)
    · exact hfOutside.2
        (hhead ▸ (R.record.edgeSet_subset_support_prod heRecord).2)
  · exact Set.disjoint_left.mp
      (R.relevantBB_disjoint_record_of_trace_disjoint hcut)
      (hT heBoundary.2)
      (R.record.edgeSet_subset_support_prod heRecord).1

/-- Every limiting-ladder edge beginning on the reserved record stays on
that same limiting-warp component. -/
theorem SplitGroundedUnusedRecord.familyEdge_head_mem_record
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    {x y : V} (hx : x ∈ R.record.support)
    (hxy : (x, y) ∈
      (ReservedInput (L := L) (hL := hL)).familyEdges) :
    y ∈ R.record.support := by
  obtain ⟨Y, hYL, hxyY⟩ := hxy
  have hxY : x ∈ Y.support := (Y.edgeSet_subset_support_prod hxyY).1
  have hrecordY : R.record = Y :=
    Alternating.DWeb.IsWarp.eq_of_mem_support
      (ReservedInput (L := L) (hL := hL)).ladder.disjoint
      R.limit_inessential.1 hYL hx hxY
  rw [hrecordY]
  exact (Y.edgeSet_subset_support_prod hxyY).2

/-- The omitted record's support is forward closed under the actual stopped
simultaneous switch.  A retained ladder edge stays on its unique limiting
component, while an inserted selected edge cannot touch the record at all. -/
theorem SplitGroundedUnusedRecord.reservedSwitchedEdge_head_mem_record
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hcut : Disjoint (PopularSwitching.ladderTrace
      (ReservedInput (L := L) (hL := hL)) R.record) S.cut)
    (T : Set V) {x y : V} (hx : x ∈ R.record.support)
    (hxy : (x, y) ∈ erasedSelectedSwitchedEdgesAt
      (ReservedIndexed (L := L) (hL := hL) (hground := hground)) S
      (splitGroundedReservedControlsFrom R) T) :
    y ∈ R.record.support := by
  rcases hxy with hbase | hforward
  · exact R.familyEdge_head_mem_record hx hbase.1.1
  · exact False.elim
      ((splitGroundedReservedControlsFrom_directionEdgeAt_endpoints_not_mem_record
        R hcut T .forward hforward.1).1 hx)

/-- Consequently every vertex reachable from the reserved original source
in the stopped switch remains on the reserved record. -/
theorem SplitGroundedUnusedRecord.reservedSwitched_reachable_mem_record
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hcut : Disjoint (PopularSwitching.ladderTrace
      (ReservedInput (L := L) (hL := hL)) R.record) S.cut)
    (T : Set V) {x : V}
    (hx : Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈ erasedSelectedSwitchedEdgesAt
        (ReservedIndexed (L := L) (hL := hL) (hground := hground)) S
        (splitGroundedReservedControlsFrom R) T)
      R.record.initial x) :
    x ∈ R.record.support := by
  induction hx with
  | refl => exact R.record.initial_mem_support
  | tail _hxy hyz ih =>
      exact R.reservedSwitchedEdge_head_mem_record hcut T ih hyz

/-- No vertex of a relevant stopping frontier is reachable from the reserved
grounded source in the actual switch. -/
theorem SplitGroundedUnusedRecord.not_reaches_reservedStoppingFrontier
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hcut : Disjoint (PopularSwitching.ladderTrace
      (ReservedInput (L := L) (hL := hL)) R.record) S.cut)
    (T : Set V) (hT : T ⊆ L.splitGroundedRelevantBB hL.legal S.cut)
    {x : V}
    (hx : Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈ erasedSelectedSwitchedEdgesAt
        (ReservedIndexed (L := L) (hL := hL) (hground := hground)) S
        (splitGroundedReservedControlsFrom R) T)
      R.record.initial x) :
    x ∉ T := by
  intro hxT
  exact Set.disjoint_left.mp
    (R.relevantBB_disjoint_record_of_trace_disjoint hcut)
    (hT hxT) (R.reservedSwitched_reachable_mem_record hcut T hx)

end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedReservedControlsFrom_selectedRoute_disjoint_record
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.edgeSet_subset_reservedSwitchedEdgesAt
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.reservedSwitchedEdge_head_mem_record
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.not_reaches_reservedStoppingFrontier
