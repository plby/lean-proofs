/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointMovingClosure
import ErdosProblems.Erdos599.ColouredSafeEndpointImaginaryClassification
import ErdosProblems.Erdos599.ColouredSafeExplicitPostClosureEndpointReference
import ErdosProblems.Erdos599.ColouredSafeExplicitPostClosureClosedRelation

/-!
# Endpoint classification of the unchanged native assignment

The endpoint-pruned words keep their actual cut geometry and captured roof.
The enriched moving closure therefore classifies every assigned endpoint,
including those on the original reference. Non-marked finite edges retain
one original uncut forward owner. The literal closed relation consequently
has infinitely many marked edges on each ray and only endpoint-popular
sinks. These are explicit endpoint-indexed predicates, not an identification
with the older full-reference imaginary graph or a grounding theorem.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint

open Set Cardinal Order DirectedPath
open _root_.Erdos599.Alternating
open SwitchingCore.RelationalInterval
open ColouredSafeReverseReachability ColouredSafeMovingStages
open ColouredSafeAmbientOccurrence ColouredSafeHammock
open FracturedFixedSafeAssignment

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {alpha : Ladder.Stage (succ kappa)}
variable {seed : Set V} {z : V} {R : LimitClosure C seed}
variable {T : StagePostClosureIntervalTransaction C alpha seed z R}
variable {F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
  (Gamma := Gamma) T.interval.ambientInterval R.closedSet}

namespace StagePostClosureIntervalTransaction.EndpointReferenceAssignment

theorem word_endpoints_subset_closed (A : EndpointReferenceAssignment T F)
    (s : Source F.outside.holes (outsideReference T.intervalReference R.closedSet)) :
    endpoints s.1 (A.original.assigned s).terminal? ⊆ R.closedSet := by
  rintro x (hxs | hxt)
  · exact hxs ▸ T.uncovered_initials_subset_closedSet F.outside s.2
  · have ht := A.original.finite_terminal s hxt
    exact T.finite_terminal_mem_closedSet F.outside ht.1 ht.2

theorem word_cut_intersection (A : EndpointReferenceAssignment T F)
    (s : Source F.outside.holes (outsideReference T.intervalReference R.closedSet)) :
    (A.word s).vertexSet ∩ R.closedSet ⊆ endpoints s.1 (A.original.assigned s).terminal? := by
  rw [A.vertices_eq]
  cases ht : (A.original.assigned s).terminal? with
  | none => simpa only [endpoints_none] using (A.geometry s).infinite_cut ht
  | some t => simpa only [endpoints_some] using (A.geometry s).finite_cut t ht

theorem word_not_contained (A : EndpointReferenceAssignment T F)
    (s : Source F.outside.holes (outsideReference T.intervalReference R.closedSet)) :
    ¬(A.word s).vertexSet ⊆ R.closedSet := by
  rw [A.vertices_eq]
  exact (A.geometry s).not_contained

theorem word_captured (A : EndpointReferenceAssignment T F)
    (s : Source F.outside.holes (outsideReference T.intervalReference R.closedSet)) :
    ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder s.1
      (A.original.assigned s).terminal? (toAmbient (A.word s)) := by
  refine ⟨R.later.stage, ?_⟩
  simpa only [toAmbient_vertexSet] using A.word_vertices_subset_capturedRoof s

variable (hclosed : ColouredSafeEndpointHammock.Closed C.ladder.limitWarp
  (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa R.closedSet)

include hclosed in
/-- The actual external word gives a large hammock at its exact optional
terminal, with its endpoint-indexed reference and captured filter unchanged. -/
theorem word_hasCard (A : EndpointReferenceAssignment T F)
    (s : Source F.outside.holes (outsideReference T.intervalReference R.closedSet)) :
    ColouredSafeHammock.HasCard
      (ColouredSafeEndpointReference.reference C.ladder.limitWarp s.1
        (A.original.assigned s).terminal?) s.1 (A.original.assigned s).terminal?
      (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder s.1
        (A.original.assigned s).terminal?) (succ kappa) :=
  ColouredSafeEndpointHammock.hasCard_of_external_occurrence (A.word s)
    T.interval.ambientInterval_linkage.isWarp T.interval.ambientInterval_linkage.finiteCharacter
    hclosed (A.terminal_eq s) (A.word_endpoints_subset_closed s)
    (A.word_captured s) (A.word_cut_intersection s) (A.word_not_contained s)

include hclosed in
theorem finite_isImaginary (A : EndpointReferenceAssignment T F)
    (s : Source F.outside.holes (outsideReference T.intervalReference R.closedSet))
    {t : V} (ht : (A.original.assigned s).terminal? = some t) :
    ColouredSafeEndpointHammock.IsImaginary C.ladder.limitWarp
      (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa s.1 t := by
  have h := A.word_hasCard hclosed s
  generalize he : (A.original.assigned s).terminal? = e at h
  have he' : e = some t := he.symm.trans ht
  cases he'
  exact h

include hclosed in
theorem finite_common_owner_of_not_marked (A : EndpointReferenceAssignment T F)
    (s : Source F.outside.holes (outsideReference T.intervalReference R.closedSet))
    {t : V} (ht : (A.original.assigned s).terminal? = some t) (hne : s.1 ≠ t)
    (hnot : ¬ColouredSafeEndpointHammock.IsMarked C.ladder.limitWarp
      (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa s.1 t) :
    ∃ p ∈ T.interval.ambientInterval, s.1 ∈ p.support ∧ t ∈ p.support :=
  ColouredSafeEndpointHammock.common_owner_of_not_marked (A.word s)
    T.interval.ambientInterval_linkage.isWarp T.interval.ambientInterval_linkage.finiteCharacter
    T.outsideIntervalGlobalReferenceEmbedding.global_isWarp hclosed (A.terminal_eq s) ht hne
    (A.word_endpoints_subset_closed s) (A.word_captured s)
    (A.word_cut_intersection s) (A.word_not_contained s) hnot

include hclosed in
theorem infinite_isPopular (A : EndpointReferenceAssignment T F)
    (s : Source F.outside.holes (outsideReference T.intervalReference R.closedSet))
    (ht : (A.original.assigned s).terminal? = none) :
    ColouredSafeEndpointHammock.IsPopular C.ladder.limitWarp
      (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) C.persistent kappa s.1 := by
  right
  have h := A.word_hasCard hclosed s
  generalize he : (A.original.assigned s).terminal? = e at h
  have he' : e = none := he.symm.trans ht
  cases he'
  exact h

/-- Retain the exact assignment when applying the earlier incidence API. -/
def toClassified (A : EndpointReferenceAssignment T F) : ClassifiedFixedOutsideAssignment T F :=
  T.classifyFixedOutsideAssignment F A.original A.geometry

def closedEdges (A : EndpointReferenceAssignment T F) : Set (V × V) :=
  sourceInsideEdges T.interval.ambientInterval R.closedSet ∪ A.original.toCompressed.finiteEdges

theorem closedEdges_biUnique (A : EndpointReferenceAssignment T F) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ A.closedEdges) :=
  A.toClassified.closedEdges_biUnique

theorem closedEdges_subset_closed (A : EndpointReferenceAssignment T F) :
    A.closedEdges ⊆ R.closedSet ×ˢ R.closedSet :=
  A.toClassified.closedEdges_subset_closed

theorem noIncoming_of_original_initial (A : EndpointReferenceAssignment T F)
    {x : V} (hx : x ∈ Gamma.initialSet T.interval.ambientInterval) :
    ¬HasIncoming A.closedEdges x :=
  A.toClassified.noIncoming_of_original_initial hx

include hclosed in
theorem closedEdge_original_or_imaginary (A : EndpointReferenceAssignment T F)
    {x y : V} (he : (x, y) ∈ A.closedEdges) :
    Gamma.graph.Adj x y ∨ ColouredSafeEndpointHammock.IsImaginary C.ladder.limitWarp
      (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa x y := by
  rcases he with he | he
  · exact Or.inl (familyEdges_subset_adj _ he.1)
  · obtain ⟨s, hs, rfl⟩ := he
    exact Or.inr (A.finite_isImaginary hclosed s hs)

include hclosed in
theorem closedEdge_common_owner_of_not_marked (A : EndpointReferenceAssignment T F)
    {x y : V} (he : (x, y) ∈ A.closedEdges)
    (hnot : ¬ColouredSafeEndpointHammock.IsMarked C.ladder.limitWarp
      (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa x y) :
    ∃ p ∈ T.interval.ambientInterval, x ∈ p.support ∧ y ∈ p.support := by
  rcases he with he | he
  · have hrow := he.1
    simp only [familyEdges, Set.mem_iUnion] at hrow
    obtain ⟨p, hp, hep⟩ := hrow
    exact ⟨p, hp, p.edgeSet_subset_support_prod hep⟩
  · obtain ⟨s, hs, rfl⟩ := he
    by_cases hne : s.1 = y
    · obtain ⟨v, hsv⟩ := A.toClassified.source_hasOutgoing_outside s
      have hsource := (familyEdges_subset_vertexSet_prod _ hsv.1).1
      obtain ⟨p, hp, hsp⟩ := hsource
      exact ⟨p, hp, hsp, hne ▸ hsp⟩
    · exact A.finite_common_owner_of_not_marked hclosed s hs hne hnot

include hclosed in
/-- Every ray of the literal relation is strong for the explicit
endpoint-indexed marked predicate. No full-reference identification occurs. -/
theorem markedIndices_infinite (A : EndpointReferenceAssignment T F)
    {D : Digraph V} (r : Ray D) (hr : r.edgeSet ⊆ A.closedEdges) :
    {n : Nat | ColouredSafeEndpointHammock.IsMarked C.ladder.limitWarp
      (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder)
        kappa (r n) (r (n + 1))}.Infinite :=
  edgePredicateIndices_infinite_of_complement_common_finite_owner
    (ColouredSafeEndpointHammock.IsMarked C.ladder.limitWarp
      (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) kappa)
    T.interval.ambientInterval_linkage.isWarp T.interval.ambientInterval_linkage.finiteCharacter
    (fun he hnot ↦ A.closedEdge_common_owner_of_not_marked hclosed he hnot) r hr

include hclosed in
theorem sink_isPopular (A : EndpointReferenceAssignment T F)
    {x : V} (hx : x ∈ sourceInsideCarrier T.interval.ambientInterval R.closedSet)
    (hsink : ¬HasOutgoing A.closedEdges x) :
    ColouredSafeEndpointHammock.IsPopular C.ladder.limitWarp
      (ColouredSafeEndpointHammock.CapturedByStageRoof C.ladder) C.persistent kappa x := by
  by_cases ht : x ∈ Gamma.terminalFrontier T.interval.ambientInterval
  · left
    have hxFrontier := T.interval.ambientInterval_linkage.terminalFrontier_subset ht
    exact (R.frontier_inter ▸ (show x ∈
      R.closedSet ∩ C.ladder.frontier R.later.stage from ⟨hx.2, hxFrontier⟩)).2
  have hout : ∃ y, (x, y) ∈ familyEdges T.interval.ambientInterval := by
    by_contra hnone
    apply ht
    rw [isWarp_terminalFrontier_eq_noOutgoing T.interval.ambientInterval_linkage.isWarp]
    exact ⟨hx.1, hnone⟩
  obtain ⟨y, hxy⟩ := hout
  have hyNotX : y ∉ R.closedSet := by
    intro hyX
    exact hsink ⟨y, Or.inl ⟨hxy, hx.2, hyX⟩⟩
  have hxHole : x ∈ Gamma.initialSet F.outside.holes.paths := by
    rw [F.outside.initialSet_eq]
    exact Or.inl ⟨hx.2, y, hxy, fun hboth ↦ hyNotX hboth.2⟩
  have hxOff : x ∉ Gamma.initialSet (outsideReference T.intervalReference R.closedSet) := by
    rintro ⟨p, hp, hpx⟩
    exact Set.disjoint_left.mp hp.2 (hpx ▸ p.initial_mem_support) hx.2
  let s : Source F.outside.holes (outsideReference T.intervalReference R.closedSet) :=
    ⟨x, hxHole, hxOff⟩
  cases hs : (A.original.assigned s).terminal? with
  | none => exact A.infinite_isPopular hclosed s hs
  | some t => exact False.elim (hsink ⟨t, Or.inr ⟨s, hs, rfl⟩⟩)

end StagePostClosureIntervalTransaction.EndpointReferenceAssignment

namespace StagePostClosureIntervalTransaction.EndpointReferenceAssignment

#print axioms word_hasCard
#print axioms markedIndices_infinite
#print axioms sink_isPopular

end StagePostClosureIntervalTransaction.EndpointReferenceAssignment

end Erdos599.Blueprint.LinkageBlueprint

