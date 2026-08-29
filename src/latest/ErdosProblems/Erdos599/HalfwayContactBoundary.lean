/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayContactSuccessorRun
import ErdosProblems.Erdos599.HalfwayClubFinalGeometry
import ErdosProblems.Erdos599.HalfwaySelectedClubGeometry

/-!
# The exact real boundary of a contact transaction

Deleting the imaginary edges of a Section 9 transaction can create new
roots and sinks.  Consequently the source/sink boundary of the full splice
relation does not by itself give the boundary required by the final real
scheduler relation.

This file records the dependency-correct conversion.  Once the transaction
proves the two exact boundary equalities for its surviving real relation,
endpoint purity of both the root-orbit blueprint and the untouched part of
the selected ladder reference is a theorem.  The only additional path
hypothesis is that no surviving real edge is strong imaginary; together with
the cofinal localization theorem this excludes a forward ray.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u v

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {I : Type v}

variable [Preorder I] [Nonempty I] [IsDirectedOrder I]

namespace ClubStageUnionData

variable {theta : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa theta}
variable {W : LinkageBlueprint Gamma Y kappa}
variable {Zf : FracturedWarp Gamma}
variable {A : SimultaneousAssignment Zf.paths Y} {u : V}

/-- Passing from the full imaginary splice to its surviving real edges can
create roots, but cannot destroy an existing root.  Thus the source-coverage
direction already stored in `ClubStageUnionData` remains valid for the real
relation. -/
theorem source_subset_realBoundary (D : ClubStageUnionData C W A u) :
    Gamma.source ⊆
      {x | x ∈ D.carrier ∧ ¬ ∃ y,
        (y, x) ∈ relationRealEdges (Gamma := Gamma)
          (D.inside ∪ assignedFiniteEdges A)} ∪
      Gamma.initialSet
        (referencePathsMeeting Y C.newSlice \
          referencePathsMeeting Y D.carrier) := by
  intro x hx
  rcases D.covers_source hx with hxRoot | hxReference
  · apply Or.inl
    refine ⟨hxRoot.1, ?_⟩
    rintro ⟨y, hyx⟩
    exact hxRoot.2 ⟨y, hyx.1⟩
  · exact Or.inr hxReference

/-- Likewise, every source of an infinite assigned route remains a sink
after imaginary edges are deleted. -/
theorem infiniteSources_subset_realSinks (D : ClubStageUnionData C W A u) :
    assignedInfiniteSources A ⊆
      {x | x ∈ D.carrier ∧ ¬ ∃ y,
        (x, y) ∈ relationRealEdges (Gamma := Gamma)
          (D.inside ∪ assignedFiniteEdges A)} := by
  intro x hx
  have hxFull := D.infinite_sources_sink hx
  refine ⟨hxFull.1, ?_⟩
  rintro ⟨y, hxy⟩
  exact hxFull.2 ⟨y, hxy.1⟩

/-- Exact source of the possible new roots created by deleting imaginary
edges.  A real root is either already a root of the full transaction or is
the head of a deleted non-original edge. -/
theorem realRoots_subset_fullRoots_union_deletedHeads
    (D : ClubStageUnionData C W A u) :
    {x | x ∈ D.carrier ∧ ¬ ∃ y,
        (y, x) ∈ relationRealEdges (Gamma := Gamma)
          (D.inside ∪ assignedFiniteEdges A)} ⊆
      {x | x ∈ D.carrier ∧ ¬ ∃ y,
        (y, x) ∈ D.inside ∪ assignedFiniteEdges A} ∪
      {x | x ∈ D.carrier ∧ ∃ y,
        (y, x) ∈ D.inside ∪ assignedFiniteEdges A ∧
          ¬ Gamma.graph.Adj y x} := by
  intro x hx
  by_cases hfull : ∃ y, (y, x) ∈ D.inside ∪ assignedFiniteEdges A
  · apply Or.inr
    obtain ⟨y, hyx⟩ := hfull
    refine ⟨hx.1, y, hyx, ?_⟩
    intro hyxReal
    exact hx.2 ⟨y, hyx, hyxReal⟩
  · exact Or.inl ⟨hx.1, hfull⟩

/-- Dually, a sink newly exposed by imaginary-edge deletion is the tail of
a deleted non-original edge.  This is the precise gap between the stored
full-relation sink boundary and the real scheduler boundary. -/
theorem realSinks_subset_fullSinks_union_deletedTails
    (D : ClubStageUnionData C W A u) :
    {x | x ∈ D.carrier ∧ ¬ ∃ y,
        (x, y) ∈ relationRealEdges (Gamma := Gamma)
          (D.inside ∪ assignedFiniteEdges A)} ⊆
      {x | x ∈ D.carrier ∧ ¬ ∃ y,
        (x, y) ∈ D.inside ∪ assignedFiniteEdges A} ∪
      {x | x ∈ D.carrier ∧ ∃ y,
        (x, y) ∈ D.inside ∪ assignedFiniteEdges A ∧
          ¬ Gamma.graph.Adj x y} := by
  intro x hx
  by_cases hfull : ∃ y, (x, y) ∈ D.inside ∪ assignedFiniteEdges A
  · apply Or.inr
    obtain ⟨y, hxy⟩ := hfull
    refine ⟨hx.1, y, hxy, ?_⟩
    intro hxyReal
    exact hx.2 ⟨y, hxy, hxyReal⟩
  · exact Or.inl ⟨hx.1, hfull⟩

end ClubStageUnionData

namespace SingleGlobalClubStageTransaction

variable {C : ClubStageGeometry Gamma Y kappa (Order.succ kappa)}

private theorem finalEdge_eq_realEdge
    (T : SingleGlobalClubStageTransaction C) (hkappa : aleph0 ≤ kappa) :
    (T.successorRun.toCofinalRun hkappa).finalEdge = T.realEdge := by
  apply Set.Subset.antisymm
  · intro e he
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 he
    exact hi
  · intro e he
    exact Set.mem_iUnion.2 ⟨Classical.arbitrary _, he⟩

private theorem finalCarrier_eq_carrier
    (T : SingleGlobalClubStageTransaction C) (hkappa : aleph0 ≤ kappa) :
    (T.successorRun.toCofinalRun hkappa).finalCarrier = T.data.carrier := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact hi
  · intro x hx
    exact Set.mem_iUnion.2 ⟨Classical.arbitrary _, hx⟩

/-- For the constant successor run induced by one global transaction, the
source-coverage half of the final root equality is already unconditional. -/
theorem source_subset_successorRun_realBoundary
    (T : SingleGlobalClubStageTransaction C) (hkappa : aleph0 ≤ kappa) :
    Gamma.source ⊆
      {x | x ∈ (T.successorRun.toCofinalRun hkappa).finalCarrier ∧
        ¬ ∃ y, (y, x) ∈
          (T.successorRun.toCofinalRun hkappa).finalEdge} ∪
      Gamma.initialSet
        (referencePathsMeeting Y C.newSlice \
          referencePathsMeeting Y
            (T.successorRun.toCofinalRun hkappa).finalCarrier) := by
  simpa only [finalEdge_eq_realEdge T hkappa,
    finalCarrier_eq_carrier T hkappa,
    SingleGlobalClubStageTransaction.realEdge] using
      T.data.source_subset_realBoundary

/-- Infinite assigned sources remain sinks in the final real relation of
the constant successor run. -/
theorem infiniteSources_subset_successorRun_realSinks
    (T : SingleGlobalClubStageTransaction C) (hkappa : aleph0 ≤ kappa) :
    assignedInfiniteSources T.assignment ⊆
      {x | x ∈ (T.successorRun.toCofinalRun hkappa).finalCarrier ∧
        ¬ ∃ y, (x, y) ∈
          (T.successorRun.toCofinalRun hkappa).finalEdge} := by
  simpa only [finalEdge_eq_realEdge T hkappa,
    finalCarrier_eq_carrier T hkappa,
    SingleGlobalClubStageTransaction.realEdge] using
      T.data.infiniteSources_subset_realSinks

end SingleGlobalClubStageTransaction

omit [Preorder I] [Nonempty I] [IsDirectedOrder I] in
/-- Exact root/source and sink/frontier equalities already imply endpoint
purity of the canonical root-orbit blueprint, provided forward rays have
been excluded.  The proof also shows why no separate "internal source" or
"internal frontier" assumptions are needed: the untouched reference
remainder is disjoint from the relation carrier. -/
theorem blueprintEndpointPure_of_boundary
    (R : CardinalInduction.HalfwayScheduler.RankedFairGlobalRelation
      Gamma Y kappa Gamma.target I)
    (T : Set V)
    (hnoRay : ¬ ContainsDirectedRay R.edge)
    (hsource :
      {x | x ∈ R.carrier ∧ ¬ ∃ y, (y, x) ∈ R.edge} ∪
          Gamma.initialSet
            (referencePathsMeeting Y T \
              referencePathsMeeting Y R.carrier) =
        Gamma.source)
    (hterminal :
      {x | x ∈ R.carrier ∧ ¬ ∃ y, (x, y) ∈ R.edge} ∪
          Gamma.terminalFrontier
            (referencePathsMeeting Y T \
              referencePathsMeeting Y R.carrier) =
        T) :
    ∀ p ∈ (orientationBlueprint R.oriented.orientation).paths,
      (orientationBlueprint R.oriented.orientation).IsPathBetween
        Gamma.source T p := by
  let O := R.oriented.orientation
  have hrootSource : {x | O.IsRoot x} ⊆ Gamma.source := by
    intro x hx
    have hxInitial : x ∈ (orientationBlueprint O).initialSet := by
      rw [orientationBlueprint_initialSet]
      exact hx
    rw [orientationBlueprint_initialSet_eq_no_incoming,
      R.oriented.carrier_eq, R.oriented.edge_eq] at hxInitial
    rw [← hsource]
    exact Or.inl hxInitial
  have hsourceRoot : ∀ x, x ∈ O.carrier → x ∈ Gamma.source →
      ¬ ∃ y, (y, x) ∈ O.edge := by
    intro x hxCarrier hxSource
    have hxUnion :
        x ∈ {x | x ∈ R.carrier ∧ ¬ ∃ y, (y, x) ∈ R.edge} ∪
          Gamma.initialSet
            (referencePathsMeeting Y T \
              referencePathsMeeting Y R.carrier) := by
      rw [hsource]
      exact hxSource
    rcases hxUnion with hxRoot | hxReference
    · rw [R.oriented.edge_eq]
      exact hxRoot.2
    · obtain ⟨q, hq, hqx⟩ := hxReference
      apply False.elim
      apply hq.2
      refine ⟨hq.1.1, x, hqx ▸ q.initial_mem_support, ?_⟩
      simpa [O, R.oriented.carrier_eq] using hxCarrier
  have hsinkFrontier :
      {x | x ∈ O.carrier ∧ ¬ ∃ y, (x, y) ∈ O.edge} ⊆ T := by
    intro x hx
    rw [← hterminal]
    apply Or.inl
    simpa only [O, R.oriented.carrier_eq, R.oriented.edge_eq] using hx
  have hfrontierSink : ∀ x, x ∈ O.carrier → x ∈ T →
      ¬ ∃ y, (x, y) ∈ O.edge := by
    intro x hxCarrier hxT
    have hxUnion :
        x ∈ {x | x ∈ R.carrier ∧ ¬ ∃ y, (x, y) ∈ R.edge} ∪
          Gamma.terminalFrontier
            (referencePathsMeeting Y T \
              referencePathsMeeting Y R.carrier) := by
      rw [hterminal]
      exact hxT
    rcases hxUnion with hxSink | hxReference
    · rw [R.oriented.edge_eq]
      exact hxSink.2
    · obtain ⟨q, hq, _hqterm⟩ := hxReference
      apply False.elim
      apply hq.2
      refine ⟨hq.1.1, x, Gamma.terminal_mem_support _hqterm, ?_⟩
      simpa [O, R.oriented.carrier_eq] using hxCarrier
  exact CardinalInduction.HalfwayScheduler.orientationBlueprint_endpointPure_of_no_directedRay
    (by simpa only [R.oriented.edge_eq] using hnoRay)
    hrootSource hsourceRoot hsinkFrontier hfrontierSink

namespace SuccessorClubStageRun

variable {C : ClubStageGeometry Gamma Y kappa (Order.succ kappa)}

/-- The selected ladder reference remainder is endpoint-pure once the exact
real source boundary is known.  Marker-starting reference members cannot
remain untouched, because their initial vertex would then occur on the
reference side of the source equality. -/
theorem referenceEndpointPure_of_sourceBoundary
    (R : SuccessorClubStageRun C) (hkappa : aleph0 ≤ kappa)
    (href : Y = C.selectedReference)
    (hsource :
      {x | x ∈ (R.toCofinalRun hkappa).finalCarrier ∧
          ¬ ∃ y, (y, x) ∈ (R.toCofinalRun hkappa).finalEdge} ∪
        Gamma.initialSet
          (referencePathsMeeting Y C.newSlice \
            referencePathsMeeting Y
              (R.toCofinalRun hkappa).finalCarrier) =
        Gamma.source) :
    ∀ p ∈
        (referencePathsMeeting Y C.newSlice \
          referencePathsMeeting Y
            (R.toCofinalRun hkappa).finalCarrier),
      CardinalInduction.IsPathBetween Gamma Gamma.source C.newSlice p := by
  intro p hp
  have hpSource : p.initial ∈ Gamma.source := by
    rw [← hsource]
    apply Or.inr
    exact ⟨p, hp, rfl⟩
  have hpSelected : p ∈ C.selectedReference := href ▸ hp.1.1
  exact ladderReference.endpointPure_of_initial_mem_source
    C.normalized C.legal hpSelected hpSource

/-- A concrete successor run needs only its exact real root/source and
sink/frontier equalities, designated roots, and exclusion of surviving
strong edges.  All path-level boundary fields of
`RankedClubFrontierBoundary` are then derived. -/
theorem rankedClubFrontierBoundary_of_exactRealBoundary
    (R : SuccessorClubStageRun C) (hkappa : aleph0 ≤ kappa)
    {A0 : Set V}
    (href : Y = C.selectedReference)
    (hdesignatedSource : A0 ⊆ Gamma.source)
    (hdesignatedRoot : A0 ⊆
      {x | x ∈ (R.toCofinalRun hkappa).finalCarrier ∧
        ¬ ∃ y, (y, x) ∈ (R.toCofinalRun hkappa).finalEdge})
    (hsource :
      {x | x ∈ (R.toCofinalRun hkappa).finalCarrier ∧
          ¬ ∃ y, (y, x) ∈ (R.toCofinalRun hkappa).finalEdge} ∪
        Gamma.initialSet
          (referencePathsMeeting Y C.newSlice \
            referencePathsMeeting Y
              (R.toCofinalRun hkappa).finalCarrier) =
        Gamma.source)
    (hterminal :
      {x | x ∈ (R.toCofinalRun hkappa).finalCarrier ∧
          ¬ ∃ y, (x, y) ∈ (R.toCofinalRun hkappa).finalEdge} ∪
        Gamma.terminalFrontier
          (referencePathsMeeting Y C.newSlice \
            referencePathsMeeting Y
              (R.toCofinalRun hkappa).finalCarrier) =
        C.newSlice)
    (hnoStrong : ∀ {x y},
      (x, y) ∈ (R.toCofinalRun hkappa).finalEdge →
        ¬ IsStrongImaginaryEdge Gamma Y kappa x y) :
    CardinalInduction.HalfwayScheduler.RankedClubFrontierBoundary C
      (R.toCofinalRun hkappa).rankedFairGlobalRelation A0 := by
  let Q := (R.toCofinalRun hkappa).rankedFairGlobalRelation
  have hnoRay : ¬ ContainsDirectedRay Q.edge := by
    apply Q.no_directedRay_of_no_strong_edge
    · exact (R.toCofinalRun hkappa).finalEdge_every_relation_ray_strong
    · exact hnoStrong
  refine {
    reference_isWarp := by
      rw [href]
      exact C.selectedReference_isWarp
    designated_source := hdesignatedSource
    designated_root := hdesignatedRoot
    source_cover := hsource
    terminal_frontier := hterminal
    blueprint_endpointPure := ?_
    reference_endpointPure := ?_ }
  · exact blueprintEndpointPure_of_boundary Q C.newSlice hnoRay
      hsource hterminal
  · exact R.referenceEndpointPure_of_sourceBoundary hkappa href hsource

/-- Direct form of the final-boundary constructor for a provenance-filtered
transaction.  A tagged construction may establish absence of a surviving
forward ray directly, without first expressing it as exclusion of strong
imaginary edges. -/
theorem rankedClubFrontierBoundary_of_noDirectedRay
    (R : SuccessorClubStageRun C) (hkappa : aleph0 ≤ kappa)
    {A0 : Set V}
    (href : Y = C.selectedReference)
    (hdesignatedSource : A0 ⊆ Gamma.source)
    (hdesignatedRoot : A0 ⊆
      {x | x ∈ (R.toCofinalRun hkappa).finalCarrier ∧
        ¬ ∃ y, (y, x) ∈ (R.toCofinalRun hkappa).finalEdge})
    (hsource :
      {x | x ∈ (R.toCofinalRun hkappa).finalCarrier ∧
          ¬ ∃ y, (y, x) ∈ (R.toCofinalRun hkappa).finalEdge} ∪
        Gamma.initialSet
          (referencePathsMeeting Y C.newSlice \
            referencePathsMeeting Y
              (R.toCofinalRun hkappa).finalCarrier) =
        Gamma.source)
    (hterminal :
      {x | x ∈ (R.toCofinalRun hkappa).finalCarrier ∧
          ¬ ∃ y, (x, y) ∈ (R.toCofinalRun hkappa).finalEdge} ∪
        Gamma.terminalFrontier
          (referencePathsMeeting Y C.newSlice \
            referencePathsMeeting Y
              (R.toCofinalRun hkappa).finalCarrier) =
        C.newSlice)
    (hnoRay : ¬ ContainsDirectedRay
      (R.toCofinalRun hkappa).finalEdge) :
    CardinalInduction.HalfwayScheduler.RankedClubFrontierBoundary C
      (R.toCofinalRun hkappa).rankedFairGlobalRelation A0 := by
  let Q := (R.toCofinalRun hkappa).rankedFairGlobalRelation
  refine {
    reference_isWarp := by
      rw [href]
      exact C.selectedReference_isWarp
    designated_source := hdesignatedSource
    designated_root := hdesignatedRoot
    source_cover := hsource
    terminal_frontier := hterminal
    blueprint_endpointPure := ?_
    reference_endpointPure := ?_ }
  · exact blueprintEndpointPure_of_boundary Q C.newSlice hnoRay
      hsource hterminal
  · exact R.referenceEndpointPure_of_sourceBoundary hkappa href hsource

end SuccessorClubStageRun

end LinkageBlueprint
end Blueprint
end Erdos599
