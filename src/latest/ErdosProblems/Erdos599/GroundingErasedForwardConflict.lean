/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedCarrierRank

/-!
# Localization of cross-route forward conflicts

Freshness of the selected auxiliary paths does not make their decoded
original-vertex carriers disjoint: an old gadget and an edge gadget can
represent the same original vertex.  Rank separation does, however, locate
every such contact in the later request's own gadget.  Head-stopping then
sharpens the location to the request exit or, for an edge request, its tail.

These lemmas expose the exact remaining incidence issue in the literal
simultaneous forward union.  In particular, they do not assume the false
claim that vertex-disjoint auxiliary paths always decode to a bi-unique
original relation.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace GroundingErasedForwardConflict

open DirectedPath Alternating
open PopularAuxiliary.Input PopularGroundingBridge
open GroundingSimultaneousDecode GroundingErasedDecode
open GroundingErasedSwitchRelation GroundingErasedCarrierRank

universe u

variable {V I : Type u} {Gamma : DWeb V}

private theorem edgeSet_endpoints_mem_vertexSet
    (Q : Alternating.AltPath Gamma.graph) {e : V × V}
    (he : e ∈ Q.edgeSet) :
    e.1 ∈ Q.vertexSet ∧ e.2 ∈ Q.vertexSet := by
  cases Q with
  | trivial x => simp at he
  | finite Q =>
      simp only [Alternating.AltPath.edgeSet,
        Alternating.FiniteTrace.edgeSet, Set.mem_iUnion] at he
      obtain ⟨i, he⟩ := he
      have hs := (Q.link i).path.edgeSet_subset_support_prod he
      exact ⟨Set.mem_iUnion.2 ⟨i, hs.1⟩,
        Set.mem_iUnion.2 ⟨i, hs.2⟩⟩
  | infinite Q =>
      simp only [Alternating.AltPath.edgeSet,
        Alternating.InfiniteTrace.edgeSet, Set.mem_iUnion] at he
      obtain ⟨i, he⟩ := he
      have hs := (Q.link i).path.edgeSet_subset_support_prod he
      exact ⟨Set.mem_iUnion.2 ⟨i, hs.1⟩,
        Set.mem_iUnion.2 ⟨i, hs.2⟩⟩

private theorem forwardEdge_mem_edgeSet
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) {e : V × V}
    (he : e ∈ (selectedErasedCompression U S K r).path.directionEdges
      .forward) :
    e ∈ (selectedErasedCompression U S K r).path.edgeSet := by
  rw [(selectedErasedCompression U S K r).path.edgeSet_eq_directionEdges_union]
  exact Or.inl he

private theorem directionVertices_subset_vertexSet
    (Q : Alternating.AltPath Gamma.graph) (d : Alternating.Direction) :
    Q.directionVertices d ⊆ Q.vertexSet := by
  intro x hx
  simp only [Alternating.AltPath.directionVertices, Set.mem_iUnion] at hx
  obtain ⟨l, hl, _hdir, hxl⟩ := hx
  cases Q with
  | trivial v => simp at hl
  | finite Q =>
      rcases hl with ⟨i, rfl⟩
      exact Set.mem_iUnion.2 ⟨i, hxl⟩
  | infinite Q =>
      rcases hl with ⟨i, rfl⟩
      exact Set.mem_iUnion.2 ⟨i, hxl⟩

/-- The endpoints of an actual forward edge lie in the actual forward
vertex carrier.  Full route incidence would additionally contain deleted
backward-run interiors and is therefore too broad for the active test. -/
private theorem forwardEdge_endpoints_mem_directionVertices
    (Q : Alternating.AltPath Gamma.graph) {e : V × V}
    (he : e ∈ Q.directionEdges .forward) :
    e.1 ∈ Q.directionVertices .forward ∧
      e.2 ∈ Q.directionVertices .forward := by
  simp only [Alternating.AltPath.directionEdges, Set.mem_iUnion] at he
  obtain ⟨l, hl, hdir, hel⟩ := he
  have hs := l.path.edgeSet_subset_support_prod hel
  constructor
  · simp only [Alternating.AltPath.directionVertices, Set.mem_iUnion]
    exact ⟨l, hl, hdir, hs.1⟩
  · simp only [Alternating.AltPath.directionVertices, Set.mem_iUnion]
    exact ⟨l, hl, hdir, hs.2⟩

/-- Two non-proxy gadgets with the same entry are either literally the same
gadget or are the old/edge representations of one vertex on one limiting
ladder component. -/
theorem entryGadgets_eq_or_commonLadderTrace
    {L : PopularAuxiliary.Input Gamma I}
    (p q : FinitePath L.lambda.graph)
    (hpstart : p.start ∈ L.lambda.source)
    (hqstart : q.start ∈ L.lambda.source)
    {a b : L.LV} (ha : a ∈ p.support) (hb : b ∈ q.support)
    {x : V} (hax : L.gadgetEntry a = some x)
    (hbx : L.gadgetEntry b = some x) :
    a = b ∨ ∃ Y ∈ L.ladder.paths,
      a ∈ PopularSwitching.ladderTrace L Y ∧
        b ∈ PopularSwitching.ladderTrace L Y := by
  cases a with
  | proxy i => simp at hax
  | old u =>
      cases b with
      | proxy j => simp at hbx
      | old v =>
          left
          have hux : u = x := Option.some.inj hax
          have hvx : v = x := Option.some.inj hbx
          exact congrArg LambdaVertex.old (hux.trans hvx.symm)
      | edge v w =>
          right
          have hux : u = x := Option.some.inj hax
          have hwx : w = x := Option.some.inj hbx
          have hvw : (v, w) ∈ L.familyEdges :=
            L.edgeNode_mem_familyEdges_of_start_in_source q hqstart hb
          obtain ⟨Y, hYL, hvwY⟩ := hvw
          refine ⟨Y, hYL, ?_, ?_⟩
          · left
            exact ⟨u, hux.trans hwx.symm ▸
              (Y.edgeSet_subset_support_prod hvwY).2, rfl⟩
          · right
            exact ⟨(v, w), hvwY, rfl⟩
  | edge u v =>
      cases b with
      | proxy j => simp at hbx
      | old w =>
          right
          have hvx : v = x := Option.some.inj hax
          have hwx : w = x := Option.some.inj hbx
          have huv : (u, v) ∈ L.familyEdges :=
            L.edgeNode_mem_familyEdges_of_start_in_source p hpstart ha
          obtain ⟨Y, hYL, huvY⟩ := huv
          refine ⟨Y, hYL, ?_, ?_⟩
          · right
            exact ⟨(u, v), huvY, rfl⟩
          · left
            exact ⟨w, hwx.trans hvx.symm ▸
              (Y.edgeSet_subset_support_prod huvY).2, rfl⟩
      | edge w z =>
          left
          have hvx : v = x := Option.some.inj hax
          have hzx : z = x := Option.some.inj hbx
          have huv : (u, v) ∈ L.familyEdges :=
            L.edgeNode_mem_familyEdges_of_start_in_source p hpstart ha
          have hwz : (w, z) ∈ L.familyEdges :=
            L.edgeNode_mem_familyEdges_of_start_in_source q hqstart hb
          have huw : u = w := by
            apply (Alternating.IsWarp.familyEdges_biUnique
              L.ladder.disjoint).1
            · simpa [PopularAuxiliary.Input.familyEdges,
                Alternating.familyEdges] using huv
            · simpa [PopularAuxiliary.Input.familyEdges,
                Alternating.familyEdges, hvx, hzx] using hwz
          exact congrArg₂ LambdaVertex.edge huw (hvx.trans hzx.symm)

/-- After the all-component active-control thinning, the actual forward
vertex carriers of two rank-ordered chronologically loop-erased routes are
genuinely disjoint.  The broader gadget carrier is used only to localize a
putative contact at the later request gadget; inactivity is then witnessed
by a vertex on an actual surviving forward link. -/
theorem activeDecodedCarriers_disjoint_of_rank_lt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (hfaith : ProxyPathsFaithful L)
    (c d : ActiveControlRequest U S K)
    (hcd : controlRank U S c.1 < controlRank U S d.1) :
    Disjoint
      (retainedForwardVertices (L := L) S.cut
        (selectedErasedCompression U S K (chosenRequest d.1)).path)
      (retainedForwardVertices (L := L) S.cut
        (selectedErasedCompression U S K (chosenRequest c.1)).path) := by
  let p := strongSelectedPath U S K (chosenRequest d.1)
  let q := strongSelectedPath U S K (chosenRequest c.1)
  have hpFan : p ∈
      (GroundingControlledAssembly.controlledRequestFan S K
        (chosenRequest d.1)).paths :=
    strongSelectedPath_mem_controlledRequestFan U S K (chosenRequest d.1)
  have hpstart : p.start ∈ L.lambda.source :=
    (GroundingControlledAssembly.controlledRequestFan S K
      (chosenRequest d.1)).starts_in_source hpFan
  have hqstart : q.start ∈ L.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source
      ⟨chosenRequest c.1, rfl⟩
  have hfresh := (strongSelectedPath_spec U S K (chosenRequest d.1)).2.2
    (controlRank U S c.1) hcd q
      (strongSelectedPath_spec U S K (chosenRequest c.1)).1
  rw [Set.disjoint_left]
  intro x hxp hxq
  have hxp' := retainedForwardVertices_subset_directionVertices S.cut
    (selectedErasedCompression U S K (chosenRequest d.1)).path hxp
  have hxq' := retainedForwardVertices_subset_directionVertices S.cut
    (selectedErasedCompression U S K (chosenRequest c.1)).path hxq
  have hxapex : x ∈ L.gadgetCarrier
      (requestAuxVertex (chosenRequest d.1)) :=
    strongSelectedPath_decodedVertexCarrier_inter_subset_apex
      U S K hfaith (chosenRequest c.1) (chosenRequest d.1) hcd
        ⟨selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
            U S K (chosenRequest d.1)
              (directionVertices_subset_vertexSet _ _ hxp'),
          selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
            U S K (chosenRequest c.1)
              (directionVertices_subset_vertexSet _ _ hxq')⟩
  have hdApex : requestAuxVertex (chosenRequest d.1) ∈ p.support := by
    rw [← strongSelectedPath_finish U S K (chosenRequest d.1)]
    exact p.finish_mem_support
  rcases L.mem_old_support_or_exposedLadderPath_of_mem_decodedVertexCarrier
      q hqstart
        (selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
          U S K (chosenRequest c.1)
            (directionVertices_subset_vertexSet _ _ hxq')) with
      hxold | ⟨Y, hYexposed, hxY⟩
  · cases hr : chosenRequest d.1 with
    | inl z =>
        have hzx : x = z.1 := by
          simpa [hr, PopularAuxiliary.Input.gadgetCarrier,
            requestAuxVertex] using hxapex
        apply Set.disjoint_left.1 hfresh.1 hdApex
        simpa [hr, requestAuxVertex, ← hzx] using hxold
    | inr e =>
        have huv : (e.1.1, e.1.2) ∈ L.familyEdges :=
          L.edgeNode_mem_familyEdges_of_start_in_source p hpstart
            (by simpa [hr, requestAuxVertex] using hdApex)
        obtain ⟨Z, hZL, huvZ⟩ := huv
        have hxEnds : x = e.1.1 ∨ x = e.1.2 := by
          simpa [hr, requestAuxVertex,
            PopularAuxiliary.Input.gadgetCarrier, eq_comm] using hxapex
        have hxZ : x ∈ Z.support := hxEnds.elim
          (fun h ↦ h.symm ▸ (Z.edgeSet_subset_support_prod huvZ).1)
          (fun h ↦ h.symm ▸ (Z.edgeSet_subset_support_prod huvZ).2)
        have hZexposed : Z ∈ exposedLadderPaths L q := by
          left
          exact ⟨hZL, .old x, hxold, Or.inl ⟨x, hxZ, rfl⟩⟩
        apply active_not_hits_of_rank_lt U S K c.2 d.2 hcd
        refine ⟨Z, hZexposed, ?_, x, hxq, hxZ, ?_⟩
        · rw [← requestVertex_chosenRequest d.1,
            ← requestExit_eq_requestVertex (chosenRequest d.1), hr]
          exact (Z.edgeSet_subset_support_prod huvZ).2
        · rw [← requestVertex_chosenRequest d.1,
            ← requestExit_eq_requestVertex (chosenRequest d.1), hr]
          rcases hxEnds with hxtail | hxhead
          · rw [hxtail]
            exact GroundingCut.beforeEq_of_mem_edgeSet huvZ
          · rw [hxhead]
            exact GroundingCut.beforeEq_refl
              (Z.edgeSet_subset_support_prod huvZ).2
  · have hYL : Y ∈ L.ladder.paths :=
      exposedLadderPaths_subset_ladder hfaith q hYexposed
    cases hr : chosenRequest d.1 with
    | inl z =>
        have hzx : x = z.1 := by
          simpa [hr, PopularAuxiliary.Input.gadgetCarrier,
            requestAuxVertex] using hxapex
        apply active_not_hits_of_rank_lt U S K c.2 d.2 hcd
        refine ⟨Y, hYexposed, ?_, x, hxq, hxY, ?_⟩
        · rw [← requestVertex_chosenRequest d.1,
            ← requestExit_eq_requestVertex (chosenRequest d.1), hr]
          change z.1 ∈ Y.support
          exact hzx ▸ hxY
        · rw [← requestVertex_chosenRequest d.1,
            ← requestExit_eq_requestVertex (chosenRequest d.1), hr]
          change GroundingCut.BeforeEq Y x z.1
          rw [← hzx]
          exact GroundingCut.beforeEq_refl hxY
    | inr e =>
        have huv : (e.1.1, e.1.2) ∈ L.familyEdges :=
          L.edgeNode_mem_familyEdges_of_start_in_source p hpstart
            (by simpa [hr, requestAuxVertex] using hdApex)
        obtain ⟨Z, hZL, huvZ⟩ := huv
        have hxEnds : x = e.1.1 ∨ x = e.1.2 := by
          simpa [hr, requestAuxVertex,
            PopularAuxiliary.Input.gadgetCarrier, eq_comm] using hxapex
        have hxZ : x ∈ Z.support := hxEnds.elim
          (fun h ↦ h.symm ▸ (Z.edgeSet_subset_support_prod huvZ).1)
          (fun h ↦ h.symm ▸ (Z.edgeSet_subset_support_prod huvZ).2)
        have hZY : Z = Y :=
          Alternating.DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint
            hZL hYL hxZ hxY
        have hZexposed : Z ∈ exposedLadderPaths L q := hZY ▸ hYexposed
        apply active_not_hits_of_rank_lt U S K c.2 d.2 hcd
        refine ⟨Z, hZexposed, ?_, x, hxq, hxZ, ?_⟩
        · rw [← requestVertex_chosenRequest d.1,
            ← requestExit_eq_requestVertex (chosenRequest d.1), hr]
          exact (Z.edgeSet_subset_support_prod huvZ).2
        · rw [← requestVertex_chosenRequest d.1,
            ← requestExit_eq_requestVertex (chosenRequest d.1), hr]
          rcases hxEnds with hxtail | hxhead
          · rw [hxtail]
            exact GroundingCut.beforeEq_of_mem_edgeSet huvZ
          · rw [hxhead]
            exact GroundingCut.beforeEq_refl
              (Z.edgeSet_subset_support_prod huvZ).2

/-- Boundary-parametric version of active forward-carrier disjointness. -/
theorem activeDecodedCarriersAt_disjoint_of_rank_lt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T : Set V) (hfaith : ProxyPathsFaithful L)
    (c d : ActiveControlRequestAt U S K T)
    (hcd : controlRank U S c.1 < controlRank U S d.1) :
    Disjoint
      (retainedForwardVerticesAt T
        (selectedErasedCompression U S K (chosenRequest d.1)).path)
      (retainedForwardVerticesAt T
        (selectedErasedCompression U S K (chosenRequest c.1)).path) := by
  let p := strongSelectedPath U S K (chosenRequest d.1)
  let q := strongSelectedPath U S K (chosenRequest c.1)
  have hpFan : p ∈
      (GroundingControlledAssembly.controlledRequestFan S K
        (chosenRequest d.1)).paths :=
    strongSelectedPath_mem_controlledRequestFan U S K (chosenRequest d.1)
  have hpstart : p.start ∈ L.lambda.source :=
    (GroundingControlledAssembly.controlledRequestFan S K
      (chosenRequest d.1)).starts_in_source hpFan
  have hqstart : q.start ∈ L.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source
      ⟨chosenRequest c.1, rfl⟩
  have hfresh := (strongSelectedPath_spec U S K (chosenRequest d.1)).2.2
    (controlRank U S c.1) hcd q
      (strongSelectedPath_spec U S K (chosenRequest c.1)).1
  rw [Set.disjoint_left]
  intro x hxp hxq
  have hxp' := retainedForwardVerticesAt_subset_directionVertices T
    (selectedErasedCompression U S K (chosenRequest d.1)).path hxp
  have hxq' := retainedForwardVerticesAt_subset_directionVertices T
    (selectedErasedCompression U S K (chosenRequest c.1)).path hxq
  have hxapex : x ∈ L.gadgetCarrier
      (requestAuxVertex (chosenRequest d.1)) :=
    strongSelectedPath_decodedVertexCarrier_inter_subset_apex
      U S K hfaith (chosenRequest c.1) (chosenRequest d.1) hcd
        ⟨selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
            U S K (chosenRequest d.1)
              (directionVertices_subset_vertexSet _ _ hxp'),
          selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
            U S K (chosenRequest c.1)
              (directionVertices_subset_vertexSet _ _ hxq')⟩
  have hdApex : requestAuxVertex (chosenRequest d.1) ∈ p.support := by
    rw [← strongSelectedPath_finish U S K (chosenRequest d.1)]
    exact p.finish_mem_support
  rcases L.mem_old_support_or_exposedLadderPath_of_mem_decodedVertexCarrier
      q hqstart
        (selectedErasedCompression_vertexSet_subset_decodedVertexCarrier
          U S K (chosenRequest c.1)
            (directionVertices_subset_vertexSet _ _ hxq')) with
      hxold | ⟨Y, hYexposed, hxY⟩
  · cases hr : chosenRequest d.1 with
    | inl z =>
        have hzx : x = z.1 := by
          simpa [hr, PopularAuxiliary.Input.gadgetCarrier,
            requestAuxVertex] using hxapex
        apply Set.disjoint_left.1 hfresh.1 hdApex
        simpa [hr, requestAuxVertex, ← hzx] using hxold
    | inr e =>
        have huv : (e.1.1, e.1.2) ∈ L.familyEdges :=
          L.edgeNode_mem_familyEdges_of_start_in_source p hpstart
            (by simpa [hr, requestAuxVertex] using hdApex)
        obtain ⟨Z, hZL, huvZ⟩ := huv
        have hxEnds : x = e.1.1 ∨ x = e.1.2 := by
          simpa [hr, requestAuxVertex,
            PopularAuxiliary.Input.gadgetCarrier, eq_comm] using hxapex
        have hxZ : x ∈ Z.support := hxEnds.elim
          (fun h ↦ h.symm ▸ (Z.edgeSet_subset_support_prod huvZ).1)
          (fun h ↦ h.symm ▸ (Z.edgeSet_subset_support_prod huvZ).2)
        have hZexposed : Z ∈ exposedLadderPaths L q := by
          left
          exact ⟨hZL, .old x, hxold, Or.inl ⟨x, hxZ, rfl⟩⟩
        apply activeAt_not_hits_of_rank_lt U S K T c.2 d.2 hcd
        refine ⟨Z, hZexposed, ?_, x, hxq, hxZ, ?_⟩
        · rw [← requestVertex_chosenRequest d.1,
            ← requestExit_eq_requestVertex (chosenRequest d.1), hr]
          exact (Z.edgeSet_subset_support_prod huvZ).2
        · rw [← requestVertex_chosenRequest d.1,
            ← requestExit_eq_requestVertex (chosenRequest d.1), hr]
          rcases hxEnds with hxtail | hxhead
          · rw [hxtail]
            exact GroundingCut.beforeEq_of_mem_edgeSet huvZ
          · rw [hxhead]
            exact GroundingCut.beforeEq_refl
              (Z.edgeSet_subset_support_prod huvZ).2
  · have hYL : Y ∈ L.ladder.paths :=
      exposedLadderPaths_subset_ladder hfaith q hYexposed
    cases hr : chosenRequest d.1 with
    | inl z =>
        have hzx : x = z.1 := by
          simpa [hr, PopularAuxiliary.Input.gadgetCarrier,
            requestAuxVertex] using hxapex
        apply activeAt_not_hits_of_rank_lt U S K T c.2 d.2 hcd
        refine ⟨Y, hYexposed, ?_, x, hxq, hxY, ?_⟩
        · rw [← requestVertex_chosenRequest d.1,
            ← requestExit_eq_requestVertex (chosenRequest d.1), hr]
          change z.1 ∈ Y.support
          exact hzx ▸ hxY
        · rw [← requestVertex_chosenRequest d.1,
            ← requestExit_eq_requestVertex (chosenRequest d.1), hr]
          change GroundingCut.BeforeEq Y x z.1
          rw [← hzx]
          exact GroundingCut.beforeEq_refl hxY
    | inr e =>
        have huv : (e.1.1, e.1.2) ∈ L.familyEdges :=
          L.edgeNode_mem_familyEdges_of_start_in_source p hpstart
            (by simpa [hr, requestAuxVertex] using hdApex)
        obtain ⟨Z, hZL, huvZ⟩ := huv
        have hxEnds : x = e.1.1 ∨ x = e.1.2 := by
          simpa [hr, requestAuxVertex,
            PopularAuxiliary.Input.gadgetCarrier, eq_comm] using hxapex
        have hxZ : x ∈ Z.support := hxEnds.elim
          (fun h ↦ h.symm ▸ (Z.edgeSet_subset_support_prod huvZ).1)
          (fun h ↦ h.symm ▸ (Z.edgeSet_subset_support_prod huvZ).2)
        have hZY : Z = Y :=
          Alternating.DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint
            hZL hYL hxZ hxY
        have hZexposed : Z ∈ exposedLadderPaths L q := hZY ▸ hYexposed
        apply activeAt_not_hits_of_rank_lt U S K T c.2 d.2 hcd
        refine ⟨Z, hZexposed, ?_, x, hxq, hxZ, ?_⟩
        · rw [← requestVertex_chosenRequest d.1,
            ← requestExit_eq_requestVertex (chosenRequest d.1), hr]
          exact (Z.edgeSet_subset_support_prod huvZ).2
        · rw [← requestVertex_chosenRequest d.1,
            ← requestExit_eq_requestVertex (chosenRequest d.1), hr]
          rcases hxEnds with hxtail | hxhead
          · rw [hxtail]
            exact GroundingCut.beforeEq_of_mem_edgeSet huvZ
          · rw [hxhead]
            exact GroundingCut.beforeEq_refl
              (Z.edgeSet_subset_support_prod huvZ).2

/-- The boundary-parametric retained forward union is locally bi-unique. -/
theorem erasedSelectedForwardEdgesAt_biUnique
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T : Set V) (hfaith : ProxyPathsFaithful L) :
    Relator.BiUnique (fun x y ↦
      (x, y) ∈ erasedSelectedRetainedForwardEdgesAt U S K T) := by
  constructor
  · intro x y z hxz hyz
    simp only [erasedSelectedRetainedForwardEdgesAt,
      Set.mem_iUnion] at hxz hyz
    obtain ⟨c, hxz⟩ := hxz
    obtain ⟨d, hyz⟩ := hyz
    by_cases hcd : c = d
    · subst d
      exact (selectedErasedForwardEdges_biUnique U S K
        (chosenRequest c.1)).1
          (retainedForwardEdgesAt_subset_directionEdges T _ hxz)
          (retainedForwardEdgesAt_subset_directionEdges T _ hyz)
    · have hxzEnds := retainedForwardEdgeAt_endpoints T
        (selectedErasedCompression U S K (chosenRequest c.1)).path hxz
      have hyzEnds := retainedForwardEdgeAt_endpoints T
        (selectedErasedCompression U S K (chosenRequest d.1)).path hyz
      exfalso
      rcases lt_trichotomy (controlRank U S c.1)
          (controlRank U S d.1) with hlt | heq | hgt
      · exact Set.disjoint_left.1
          (activeDecodedCarriersAt_disjoint_of_rank_lt
            U S K T hfaith c d hlt) hyzEnds.2 hxzEnds.2
      · exact hcd (Subtype.ext ((controlRank U S).injective heq))
      · exact Set.disjoint_left.1
          (activeDecodedCarriersAt_disjoint_of_rank_lt
            U S K T hfaith d c hgt) hxzEnds.2 hyzEnds.2
  · intro x y z hxy hxz
    simp only [erasedSelectedRetainedForwardEdgesAt,
      Set.mem_iUnion] at hxy hxz
    obtain ⟨c, hxy⟩ := hxy
    obtain ⟨d, hxz⟩ := hxz
    by_cases hcd : c = d
    · subst d
      exact (selectedErasedForwardEdges_biUnique U S K
        (chosenRequest c.1)).2
          (retainedForwardEdgesAt_subset_directionEdges T _ hxy)
          (retainedForwardEdgesAt_subset_directionEdges T _ hxz)
    · have hxyEnds := retainedForwardEdgeAt_endpoints T
        (selectedErasedCompression U S K (chosenRequest c.1)).path hxy
      have hxzEnds := retainedForwardEdgeAt_endpoints T
        (selectedErasedCompression U S K (chosenRequest d.1)).path hxz
      exfalso
      rcases lt_trichotomy (controlRank U S c.1)
          (controlRank U S d.1) with hlt | heq | hgt
      · exact Set.disjoint_left.1
          (activeDecodedCarriersAt_disjoint_of_rank_lt
            U S K T hfaith c d hlt) hxzEnds.1 hxyEnds.1
      · exact hcd (Subtype.ext ((controlRank U S).injective heq))
      · exact Set.disjoint_left.1
          (activeDecodedCarriersAt_disjoint_of_rank_lt
            U S K T hfaith d c hgt) hxyEnds.1 hxzEnds.1

/-- The complete boundary-parametric switched relation is locally
bi-unique. -/
theorem erasedSelectedSwitchedEdgesAt_biUnique
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (T : Set V) (hfaith : ProxyPathsFaithful L) :
    Relator.BiUnique (fun x y ↦
      (x, y) ∈ erasedSelectedSwitchedEdgesAt U S K T) := by
  have hbase : Relator.BiUnique (fun x y ↦
      (x, y) ∈ residualLadderEdges U S \
        erasedSelectedToggleEdgesAt U S K T) := by
    constructor
    · intro x y z hxz hyz
      exact (residualLadderEdges_biUnique U S).1 hxz.1 hyz.1
    · intro x y z hxy hxz
      exact (residualLadderEdges_biUnique U S).2 hxy.1 hxz.1
  have hforward := erasedSelectedForwardEdgesAt_biUnique
    U S K T hfaith
  constructor
  · intro x y z hxz hyz
    change (x, z) ∈
      (residualLadderEdges U S \ erasedSelectedToggleEdgesAt U S K T) ∪
        (erasedSelectedDirectionEdgesAt U S K T .forward \
          erasedSelectedForwardCutEdgesAt U S K T) at hxz
    change (y, z) ∈
      (residualLadderEdges U S \ erasedSelectedToggleEdgesAt U S K T) ∪
        (erasedSelectedDirectionEdgesAt U S K T .forward \
          erasedSelectedForwardCutEdgesAt U S K T) at hyz
    rw [forward_diff_erasedSelectedForwardCutEdgesAt_eq_retained
      U S K T] at hxz hyz
    rcases hxz with hxz | hxz <;> rcases hyz with hyz | hyz
    · exact hbase.1 hxz hyz
    · exact survivingResidual_forwardAt_incoming_unique
        U S K T hxz hyz
    · exact (survivingResidual_forwardAt_incoming_unique
        U S K T hyz hxz).symm
    · exact hforward.1 hxz hyz
  · intro x y z hxy hxz
    change (x, y) ∈
      (residualLadderEdges U S \ erasedSelectedToggleEdgesAt U S K T) ∪
        (erasedSelectedDirectionEdgesAt U S K T .forward \
          erasedSelectedForwardCutEdgesAt U S K T) at hxy
    change (x, z) ∈
      (residualLadderEdges U S \ erasedSelectedToggleEdgesAt U S K T) ∪
        (erasedSelectedDirectionEdgesAt U S K T .forward \
          erasedSelectedForwardCutEdgesAt U S K T) at hxz
    rw [forward_diff_erasedSelectedForwardCutEdgesAt_eq_retained
      U S K T] at hxy hxz
    rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
    · exact hbase.2 hxy hxz
    · exact survivingResidual_forwardAt_outgoing_unique
        U S K T hxy hxz
    · exact (survivingResidual_forwardAt_outgoing_unique
        U S K T hxz hxy).symm
    · exact hforward.2 hxy hxz
/-- The union of all forward erased routes selected by active controls is
locally bi-unique.  Within one active control this is the path property of
the erased compression.  Between distinct controls, injectivity of the
control rank orders their owners, and the preceding theorem makes their
decoded vertex carriers disjoint. -/
theorem erasedSelectedForwardEdges_biUnique
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (hfaith : ProxyPathsFaithful L) :
    Relator.BiUnique (fun x y ↦
      (x, y) ∈ erasedSelectedRetainedForwardEdges U S K) := by
  constructor
  · intro x y z hxz hyz
    simp only [erasedSelectedRetainedForwardEdges, Set.mem_iUnion] at hxz hyz
    obtain ⟨c, hxz⟩ := hxz
    obtain ⟨d, hyz⟩ := hyz
    by_cases hcd : c = d
    · subst d
      exact (selectedErasedForwardEdges_biUnique U S K
        (chosenRequest c.1)).1
          (retainedForwardEdges_subset_directionEdges S.cut _ hxz)
          (retainedForwardEdges_subset_directionEdges S.cut _ hyz)
    · have hxzEnds := retainedForwardEdge_endpoints S.cut
        (selectedErasedCompression U S K (chosenRequest c.1)).path
        hxz
      have hyzEnds := retainedForwardEdge_endpoints S.cut
        (selectedErasedCompression U S K (chosenRequest d.1)).path
        hyz
      exfalso
      rcases lt_trichotomy (controlRank U S c.1)
          (controlRank U S d.1) with hlt | heq | hgt
      · exact Set.disjoint_left.1
          (activeDecodedCarriers_disjoint_of_rank_lt
            U S K hfaith c d hlt) hyzEnds.2 hxzEnds.2
      · exact hcd (Subtype.ext ((controlRank U S).injective heq))
      · exact Set.disjoint_left.1
          (activeDecodedCarriers_disjoint_of_rank_lt
            U S K hfaith d c hgt) hxzEnds.2 hyzEnds.2
  · intro x y z hxy hxz
    simp only [erasedSelectedRetainedForwardEdges, Set.mem_iUnion] at hxy hxz
    obtain ⟨c, hxy⟩ := hxy
    obtain ⟨d, hxz⟩ := hxz
    by_cases hcd : c = d
    · subst d
      exact (selectedErasedForwardEdges_biUnique U S K
        (chosenRequest c.1)).2
          (retainedForwardEdges_subset_directionEdges S.cut _ hxy)
          (retainedForwardEdges_subset_directionEdges S.cut _ hxz)
    · have hxyEnds := retainedForwardEdge_endpoints S.cut
        (selectedErasedCompression U S K (chosenRequest c.1)).path
        hxy
      have hxzEnds := retainedForwardEdge_endpoints S.cut
        (selectedErasedCompression U S K (chosenRequest d.1)).path
        hxz
      exfalso
      rcases lt_trichotomy (controlRank U S c.1)
          (controlRank U S d.1) with hlt | heq | hgt
      · exact Set.disjoint_left.1
          (activeDecodedCarriers_disjoint_of_rank_lt
            U S K hfaith c d hlt) hxzEnds.1 hxyEnds.1
      · exact hcd (Subtype.ext ((controlRank U S).injective heq))
      · exact Set.disjoint_left.1
          (activeDecodedCarriers_disjoint_of_rank_lt
            U S K hfaith d c hgt) hxyEnds.1 hxzEnds.1

/-- The repaired residual/forward switch relation is locally bi-unique for
the all-component active-control thinning. -/
theorem erasedSelectedSwitchedEdges_biUnique
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (hfaith : ProxyPathsFaithful L) :
    Relator.BiUnique (fun x y ↦
      (x, y) ∈ erasedSelectedSwitchedEdges U S K) :=
  erasedSelectedSwitchedEdges_biUnique_of_forward_biUnique U S K
    (erasedSelectedForwardEdges_biUnique U S K hfaith)

/-- Two distinct active forward routes with the same head can collide only
at the exit, or at the represented tail of an edge request, of the later
active control. -/
theorem incomingConflict_localized
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (hfaith : ProxyPathsFaithful L)
    (c d : ActiveControlRequest U S K)
    (hcd : c ≠ d) {x y z : V}
    (hxz : (x, z) ∈ (selectedErasedCompression U S K
      (chosenRequest c.1)).path.directionEdges .forward)
    (hyz : (y, z) ∈ (selectedErasedCompression U S K
      (chosenRequest d.1)).path.directionEdges .forward) :
    (controlRank U S c.1 < controlRank U S d.1 ∧
        z ∈ {requestExit (chosenRequest d.1)} ∪
          requestTailSet (chosenRequest d.1)) ∨
      (controlRank U S d.1 < controlRank U S c.1 ∧
        z ∈ {requestExit (chosenRequest c.1)} ∪
          requestTailSet (chosenRequest c.1)) := by
  have hxzEdge := forwardEdge_mem_edgeSet U S K (chosenRequest c.1) hxz
  have hyzEdge := forwardEdge_mem_edgeSet U S K (chosenRequest d.1) hyz
  have hzC := (edgeSet_endpoints_mem_vertexSet
    (selectedErasedCompression U S K (chosenRequest c.1)).path hxzEdge).2
  have hzD := (edgeSet_endpoints_mem_vertexSet
    (selectedErasedCompression U S K (chosenRequest d.1)).path hyzEdge).2
  rcases lt_trichotomy (controlRank U S c.1) (controlRank U S d.1) with
      hlt | heq | hgt
  · left
    refine ⟨hlt, selectedErasedCompression_ownCarrierContact U S K
      (chosenRequest d.1) ⟨hzD, ?_⟩⟩
    exact selectedErasedCompression_vertexSet_inter_subset_apex
      U S K hfaith (chosenRequest c.1) (chosenRequest d.1) hlt
        ⟨hzD, hzC⟩
  · exfalso
    apply hcd
    apply Subtype.ext
    exact (controlRank U S).injective heq
  · right
    refine ⟨hgt, selectedErasedCompression_ownCarrierContact U S K
      (chosenRequest c.1) ⟨hzC, ?_⟩⟩
    exact selectedErasedCompression_vertexSet_inter_subset_apex
      U S K hfaith (chosenRequest d.1) (chosenRequest c.1) hgt
        ⟨hzC, hzD⟩

/-- Two distinct active forward routes with the same tail can collide only
at the exit, or at the represented tail of an edge request, of the later
active control.  The exit alternative can subsequently be excluded from
the terminality of the later erased route; the edge-tail alternative is the
remaining head-stopping incidence case. -/
theorem outgoingConflict_localized
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (hfaith : ProxyPathsFaithful L)
    (c d : ActiveControlRequest U S K)
    (hcd : c ≠ d) {x y z : V}
    (hxy : (x, y) ∈ (selectedErasedCompression U S K
      (chosenRequest c.1)).path.directionEdges .forward)
    (hxz : (x, z) ∈ (selectedErasedCompression U S K
      (chosenRequest d.1)).path.directionEdges .forward) :
    (controlRank U S c.1 < controlRank U S d.1 ∧
        x ∈ {requestExit (chosenRequest d.1)} ∪
          requestTailSet (chosenRequest d.1)) ∨
      (controlRank U S d.1 < controlRank U S c.1 ∧
        x ∈ {requestExit (chosenRequest c.1)} ∪
          requestTailSet (chosenRequest c.1)) := by
  have hxyEdge := forwardEdge_mem_edgeSet U S K (chosenRequest c.1) hxy
  have hxzEdge := forwardEdge_mem_edgeSet U S K (chosenRequest d.1) hxz
  have hxC := (edgeSet_endpoints_mem_vertexSet
    (selectedErasedCompression U S K (chosenRequest c.1)).path hxyEdge).1
  have hxD := (edgeSet_endpoints_mem_vertexSet
    (selectedErasedCompression U S K (chosenRequest d.1)).path hxzEdge).1
  rcases lt_trichotomy (controlRank U S c.1) (controlRank U S d.1) with
      hlt | heq | hgt
  · left
    refine ⟨hlt, selectedErasedCompression_ownCarrierContact U S K
      (chosenRequest d.1) ⟨hxD, ?_⟩⟩
    exact selectedErasedCompression_vertexSet_inter_subset_apex
      U S K hfaith (chosenRequest c.1) (chosenRequest d.1) hlt
        ⟨hxD, hxC⟩
  · exfalso
    apply hcd
    apply Subtype.ext
    exact (controlRank U S).injective heq
  · right
    refine ⟨hgt, selectedErasedCompression_ownCarrierContact U S K
      (chosenRequest c.1) ⟨hxC, ?_⟩⟩
    exact selectedErasedCompression_vertexSet_inter_subset_apex
      U S K hfaith (chosenRequest d.1) (chosenRequest c.1) hgt
        ⟨hxC, hxD⟩

end GroundingErasedForwardConflict
end Erdos599
