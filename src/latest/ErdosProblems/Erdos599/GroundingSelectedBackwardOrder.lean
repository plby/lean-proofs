/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingCutEndpointOrder
import ErdosProblems.Erdos599.GroundingErasedDecode

/-!
# Order of selected backward edges on retained fragments

Every backward edge of a selected erased route comes from an edge gadget of
the underlying normalized auxiliary path.  If that edge lies in a surviving
fragment, the edge gadget is outside the popular cut.  The first prefix ending
at the gadget therefore avoids the cut, and the edge-endpoint form of
Assertion 8.21 puts its tail no later than the fragment blocking point.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingSelectedBackwardOrder

open DirectedPath Alternating
open PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- The first prefix of a normalized request path ending at a represented
surviving edge avoids the complete popular cut. -/
theorem firstHit_edgeContact_avoids_cut
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut)
    {p : FinitePath L.lambda.graph}
    (hp : p ∈ (GroundingAssembly.normalizedRequestFan S K r).paths)
    {x y : V}
    (hxy : (x, y) ∈ L.familyEdges)
    (hxyNotCE : (x, y) ∉ GroundingCut.CE L S.cut)
    (hedge : (PopularAuxiliary.Input.LambdaVertex.edge x y : L.LV) ∈
      p.support) :
    let hmeet : p.walk.Meets
        ({PopularAuxiliary.Input.LambdaVertex.edge x y} : Set L.LV) :=
      ⟨.edge x y, hedge, Set.mem_singleton _⟩
    L.lambda.Avoids
      (p.firstHit
        ({PopularAuxiliary.Input.LambdaVertex.edge x y} : Set L.LV)
        hmeet) S.cut := by
  let edgeVertex : L.LV :=
    PopularAuxiliary.Input.LambdaVertex.edge x y
  have hedgeNotCut : edgeVertex ∉ S.cut :=
    GroundingCutDecoder.edge_not_mem_cut_of_not_mem_CE
      L S.cut hxy hxyNotCE
  have hedgeNotApex : edgeVertex ≠ requestAuxVertex r := by
    intro heq
    exact hedgeNotCut (heq ▸ requestAuxVertex_mem_cut r)
  let hmeet : p.walk.Meets ({edgeVertex} : Set L.LV) :=
    ⟨edgeVertex, hedge, Set.mem_singleton _⟩
  let q := p.firstHit ({edgeVertex} : Set L.LV) hmeet
  have hpfinish : p.finish = requestAuxVertex r :=
    Set.mem_singleton_iff.mp
      ((GroundingAssembly.normalizedRequestFan S K r).ends_in_join hp)
  have hpfinishNot : p.finish ∉ ({edgeVertex} : Set L.LV) := by
    intro h
    have heq : p.finish = edgeVertex := Set.mem_singleton_iff.mp h
    exact hedgeNotApex (heq.symm.trans hpfinish)
  have hpfinishNotQ : p.finish ∉ q.support :=
    Popular.firstHit_not_mem_of_finish_not_mem p
      ({edgeVertex} : Set L.LV) hmeet hpfinishNot
  have hapexNotQ : requestAuxVertex r ∉ q.support := by
    intro h
    exact hpfinishNotQ (hpfinish ▸ h)
  change Disjoint q.support S.cut
  rw [Set.disjoint_left]
  intro z hzq hzcut
  have hzp : z ∈ p.support := p.firstHit_support_subset _ hmeet hzq
  have hzApex := GroundingAssembly.normalizedRequestFan_cut_normalized
    S K r hp ⟨hzp, hzcut⟩
  exact hapexNotQ (Set.mem_singleton_iff.mp hzApex ▸ hzq)

/-- Assertion 8.21 at an arbitrary off-apex edge gadget of a strongly
selected request path.  This form does not require the represented backward
edge to survive chronological erasure, so it also applies when classifying
the tail of a retained forward connector. -/
theorem strongSelectedPath_edgeGadgetTail_beforeEq_or_mem_CV
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (r : Request L S.cut)
    (P : L.Fragment) (hP : P ∈ GroundingCut.G0 L S.cut)
    (hblockable : GroundingCut.IsBlockable L S.cut P)
    {x y : V}
    (hedge : (PopularAuxiliary.Input.LambdaVertex.edge x y : L.LV) ∈
      (strongSelectedPath U S K r).support)
    (hedgeNotApex :
      (PopularAuxiliary.Input.LambdaVertex.edge x y : L.LV) ≠
        requestAuxVertex r)
    (hxP : x ∈ P.path.support) :
    GroundingCut.BeforeEq P.path x
        (GroundingCut.blockingPoint L S.cut P) ∨
      x ∈ GroundingCut.CV L S.cut := by
  let p := strongSelectedPath U S K r
  have hpFan : p ∈ (GroundingAssembly.normalizedRequestFan S K r).paths :=
    (strongSelectedPath_mem_controlledRequestFan U S K r).1
  have hpStart : p.start ∈ L.lambda.source :=
    (GroundingAssembly.normalizedRequestFan S K r).starts_in_source hpFan
  have hxyFamily : (x, y) ∈ L.familyEdges :=
    L.edgeNode_mem_familyEdges_of_start_in_source p hpStart hedge
  have hxyNotCE : (x, y) ∉ GroundingCut.CE L S.cut := by
    intro hxyCE
    have hedgeCut :
        (PopularAuxiliary.Input.LambdaVertex.edge x y : L.LV) ∈ S.cut :=
      (GroundingCut.mem_CE.mp hxyCE).1
    have hedgeApex := GroundingAssembly.normalizedRequestFan_cut_normalized
      S K r hpFan ⟨hedge, hedgeCut⟩
    exact hedgeNotApex (Set.mem_singleton_iff.mp hedgeApex)
  let hmeet : p.walk.Meets
      ({PopularAuxiliary.Input.LambdaVertex.edge x y} : Set L.LV) :=
    ⟨.edge x y, hedge, Set.mem_singleton _⟩
  let q := p.firstHit
    ({PopularAuxiliary.Input.LambdaVertex.edge x y} : Set L.LV) hmeet
  have horder :=
    GroundingCutEndpointOrder.assertion8_21_edgeTail_or_old_mem_cut
      L S.cut S.separates P hP hblockable q hpStart
        (firstHit_edgeContact_avoids_cut
          S K r hpFan hxyFamily hxyNotCE hedge)
        (Set.mem_singleton_iff.mp (p.firstHit_finish_mem _ hmeet))
        hxP hxyFamily hxyNotCE
  exact horder.imp_right GroundingCut.mem_CV.mpr

/-- Every retained selected backward edge lying on a blockable `G0`
fragment has its tail weakly before that fragment's blocking point.  This is
the literal edgewise invariant used in Assertion 8.22.  The hypothesis that
the old copy of the tail is not already a Lambda target is essential: a tail
which is itself a cut target is one of the boundary cases handled separately
in the blocking-point argument. -/
theorem backwardEdgeTail_beforeEq_blockingPoint
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (r : Request L S.cut)
    (P : L.Fragment) (hP : P ∈ GroundingCut.G0 L S.cut)
    (hblockable : GroundingCut.IsBlockable L S.cut P)
    {x y : V}
    (hback : (x, y) ∈
      (selectedErasedCompression U S K r).path.directionEdges .backward)
    (hxyP : (x, y) ∈ P.path.edgeSet)
    (hxnotTarget :
      (PopularAuxiliary.Input.LambdaVertex.old x : L.LV) ∉
        L.lambda.target) :
    GroundingCut.BeforeEq P.path x
      (GroundingCut.blockingPoint L S.cut P) := by
  let p := strongSelectedPath U S K r
  have hpFan : p ∈ (GroundingAssembly.normalizedRequestFan S K r).paths :=
    (strongSelectedPath_mem_controlledRequestFan U S K r).1
  obtain ⟨s, hs, hsback, hsedge⟩ :=
    selectedErasedCompression_directionEdge_provenance
      U S K r .backward hback
  have hedge :
      (PopularAuxiliary.Input.LambdaVertex.edge x y : L.LV) ∈
        p.support := by
    have hdecoded : (x, y) ∈
        PopularAuxiliary.Input.directedSignedEdgeSet .backward
        (L.decodeWalkSteps p.walk) :=
      ⟨s, hs, hsback, hsedge⟩
    rw [L.backwardEdges_decodeWalkSteps p.walk] at hdecoded
    exact hdecoded
  have hxyFamily : (x, y) ∈ L.familyEdges :=
    ⟨P.parent, P.parent_mem, P.edges_subset hxyP⟩
  have hxyNotCE : (x, y) ∉ GroundingCut.CE L S.cut := by
    intro hxyCE
    exact Set.disjoint_left.1 hP.1.1 hxyP hxyCE
  let hmeet : p.walk.Meets
      ({PopularAuxiliary.Input.LambdaVertex.edge x y} : Set L.LV) :=
    ⟨.edge x y, hedge, Set.mem_singleton _⟩
  let q := p.firstHit
    ({PopularAuxiliary.Input.LambdaVertex.edge x y} : Set L.LV) hmeet
  apply GroundingCutEndpointOrder.assertion8_21_edgeTail
    L S.cut S.separates P hP hblockable q
  · change p.start ∈ L.lambda.source
    exact (GroundingAssembly.normalizedRequestFan S K r).starts_in_source hpFan
  · exact firstHit_edgeContact_avoids_cut
      S K r hpFan hxyFamily hxyNotCE hedge
  · exact Set.mem_singleton_iff.mp (p.firstHit_finish_mem _ hmeet)
  · exact (P.path.edgeSet_subset_support_prod hxyP).1
  · exact hxyFamily
  · exact hxyNotCE
  · exact hxnotTarget

/-- Boundary-complete form of the edgewise invariant.  A selected backward
edge on a retained fragment either leaves that fragment no later than its
blocking point, or its tail is itself represented in the old-vertex part of
the cut.  The second alternative follows directly from separator geometry
when the old tail is a Lambda target. -/
theorem backwardEdgeTail_beforeEq_or_mem_CV
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (r : Request L S.cut)
    (P : L.Fragment) (hP : P ∈ GroundingCut.G0 L S.cut)
    (hblockable : GroundingCut.IsBlockable L S.cut P)
    {x y : V}
    (hback : (x, y) ∈
      (selectedErasedCompression U S K r).path.directionEdges .backward)
    (hxyP : (x, y) ∈ P.path.edgeSet) :
    GroundingCut.BeforeEq P.path x
        (GroundingCut.blockingPoint L S.cut P) ∨
      x ∈ GroundingCut.CV L S.cut := by
  by_cases hxTarget :
      (PopularAuxiliary.Input.LambdaVertex.old x : L.LV) ∈
        L.lambda.target
  · right
    let p := strongSelectedPath U S K r
    have hpFan : p ∈ (GroundingAssembly.normalizedRequestFan S K r).paths :=
      (strongSelectedPath_mem_controlledRequestFan U S K r).1
    obtain ⟨s, hs, hsback, hsedge⟩ :=
      selectedErasedCompression_directionEdge_provenance
        U S K r .backward hback
    have hedge :
        (PopularAuxiliary.Input.LambdaVertex.edge x y : L.LV) ∈
          p.support := by
      have hdecoded : (x, y) ∈
          PopularAuxiliary.Input.directedSignedEdgeSet .backward
            (L.decodeWalkSteps p.walk) :=
        ⟨s, hs, hsback, hsedge⟩
      rw [L.backwardEdges_decodeWalkSteps p.walk] at hdecoded
      exact hdecoded
    have hxyFamily : (x, y) ∈ L.familyEdges :=
      ⟨P.parent, P.parent_mem, P.edges_subset hxyP⟩
    have hxyNotCE : (x, y) ∉ GroundingCut.CE L S.cut := by
      intro hxyCE
      exact Set.disjoint_left.1 hP.1.1 hxyP hxyCE
    let hmeet : p.walk.Meets
        ({PopularAuxiliary.Input.LambdaVertex.edge x y} : Set L.LV) :=
      ⟨.edge x y, hedge, Set.mem_singleton _⟩
    let q := p.firstHit
      ({PopularAuxiliary.Input.LambdaVertex.edge x y} : Set L.LV) hmeet
    apply GroundingCut.mem_CV.mpr
    apply GroundingCutEndpointOrder.oldTail_mem_cut_of_edgeContact_of_target
      L S.cut S.separates q
    · change p.start ∈ L.lambda.source
      exact (GroundingAssembly.normalizedRequestFan S K r).starts_in_source hpFan
    · exact firstHit_edgeContact_avoids_cut
        S K r hpFan hxyFamily hxyNotCE hedge
    · exact Set.mem_singleton_iff.mp (p.firstHit_finish_mem _ hmeet)
    · exact hxyFamily
    · exact hxTarget
  · left
    exact backwardEdgeTail_beforeEq_blockingPoint
      U S K r P hP hblockable hback hxyP hxTarget

/-- Union-level form of `backwardEdgeTail_beforeEq_blockingPoint`.  This is
the convenient interface for a backward edge encountered while analysing a
chain in the complete switched relation. -/
theorem erasedSelectedBackwardEdgeTail_beforeEq_blockingPoint
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (P : L.Fragment) (hP : P ∈ GroundingCut.G0 L S.cut)
    (hblockable : GroundingCut.IsBlockable L S.cut P)
    {x y : V}
    (hback : (x, y) ∈ erasedSelectedDirectionEdges U S K .backward)
    (hxyP : (x, y) ∈ P.path.edgeSet)
    (hxnotTarget :
      (PopularAuxiliary.Input.LambdaVertex.old x : L.LV) ∉
        L.lambda.target) :
    GroundingCut.BeforeEq P.path x
      (GroundingCut.blockingPoint L S.cut P) := by
  simp only [erasedSelectedDirectionEdges, Set.mem_iUnion] at hback
  obtain ⟨c, hback⟩ := hback
  exact backwardEdgeTail_beforeEq_blockingPoint
    U S K (chosenRequest c.1) P hP hblockable hback hxyP hxnotTarget

/-- Union-level boundary-complete form. -/
theorem erasedSelectedBackwardEdgeTail_beforeEq_or_mem_CV
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (P : L.Fragment) (hP : P ∈ GroundingCut.G0 L S.cut)
    (hblockable : GroundingCut.IsBlockable L S.cut P)
    {x y : V}
    (hback : (x, y) ∈ erasedSelectedDirectionEdges U S K .backward)
    (hxyP : (x, y) ∈ P.path.edgeSet) :
    GroundingCut.BeforeEq P.path x
        (GroundingCut.blockingPoint L S.cut P) ∨
      x ∈ GroundingCut.CV L S.cut := by
  simp only [erasedSelectedDirectionEdges, Set.mem_iUnion] at hback
  obtain ⟨c, hback⟩ := hback
  exact backwardEdgeTail_beforeEq_or_mem_CV
    U S K (chosenRequest c.1) P hP hblockable hback hxyP

end GroundingSelectedBackwardOrder
end Erdos599
