/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedBoundarySink
import ErdosProblems.Erdos599.GroundingSelectedForwardOrder
import ErdosProblems.Erdos599.GroundingFragmentResidualOrder

/-!
# First selected departure in a grounded split boundary collision

The pre-stopped relation is the union of residual limiting-ladder edges and
selected forward edges, after deleting toggled residual edges.  Along the
finite first-hit path, either every edge is residual or there is a first
selected forward edge with a named active owner, an entirely residual
prefix, and a pre-stopped suffix to the later boundary point.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open Alternating GroundingErasedDecode GroundingSimultaneousDecode
  PopularAuxiliary.Input PopularGroundingBridge

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev GroundedDepartureIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

/-- Raw selected-forward order at a retained fragment.  This is generic in
the auxiliary input and its controls; the split lane instantiates it below
with the grounded canonical auxiliary. -/
theorem selectedForwardTail_beforeEq_or_mem_CV
    {J : PopularAuxiliary.Input Gamma I} {lambda : Cardinal.{u}}
    (U : Popular.KappaIndexed J.lambda lambda)
    (T : Popular.PopularSeparator U)
    (C : GroundingSelection.Controls T) (r : Request J T.cut)
    (hfaith : ProxyPathsFaithful J)
    (P : J.Fragment) (hP : P ∈ GroundingCut.G0 J T.cut)
    (hblockable : GroundingCut.IsBlockable J T.cut P)
    {b y : V}
    (hby : (b, y) ∈
      (selectedErasedCompression U T C r).path.directionEdges .forward)
    (hbP : b ∈ P.path.support) :
    GroundingCut.BeforeEq P.path b
        (GroundingCut.blockingPoint J T.cut P) ∨
      b ∈ GroundingCut.CV J T.cut := by
  rcases
      GroundingForwardTailClassification.selectedForwardTail_old_or_edge_or_startingProxy
        U T C r hby with hold | hedge | hproxy
  · obtain ⟨d, hbd⟩ := hold
    have hbSupport : (LambdaVertex.old b : J.LV) ∈
        (strongSelectedPath U T C r).support :=
      ((strongSelectedPath U T C r).edgeSet_subset_support_prod hbd).1
    by_cases hbApex : (LambdaVertex.old b : J.LV) = requestAuxVertex r
    · exact Or.inr <| GroundingCut.mem_CV.mpr <|
        hbApex ▸ requestAuxVertex_mem_cut r
    · exact Or.inl <|
        GroundingDecodedContactOrder.strongSelectedPath_fragmentContact_beforeEq_blockingPoint
          T C r P hP hblockable ⟨⟨hbSupport, hbApex⟩, hbP⟩
  · obtain ⟨v, d, hvd⟩ := hedge
    have hedgeSupport : (LambdaVertex.edge b v : J.LV) ∈
        (strongSelectedPath U T C r).support :=
      ((strongSelectedPath U T C r).edgeSet_subset_support_prod hvd).1
    have hedgeNotApex :
        (LambdaVertex.edge b v : J.LV) ≠ requestAuxVertex r := by
      intro hedgeApex
      have hfinish := strongSelectedPath_finish U T C r
      exact (Alternating.FinitePath.source_ne_finish_of_mem_edgeSet
        (strongSelectedPath U T C r) hvd)
          (hedgeApex.trans hfinish.symm)
    exact
      GroundingSelectedBackwardOrder.strongSelectedPath_edgeGadgetTail_beforeEq_or_mem_CV
        U T C r P hP hblockable hedgeSupport hedgeNotApex hbP
  · obtain ⟨i, _d, hstart, _hid, hbi⟩ := hproxy
    exact GroundingSelectedForwardOrder.startingProxyTail_beforeEq_or_mem_CV
      U T C r hfaith P hP hblockable hbP hstart hbi

/-- The tail of an edge in a finite walk occurs before its final vertex. -/
private theorem walkEdgeFst_mem_support_dropLast
    {D : Digraph V} {a b x y : V}
    (p : DirectedPath.Walk D a b) (he : (x, y) ∈ p.edgeSet) :
    x ∈ p.support.dropLast := by
  induction p with
  | nil => simp at he
  | @cons a z b h p ih =>
      simp only [DirectedPath.Walk.edgeSet_cons, Set.mem_union,
        Set.mem_singleton_iff] at he
      rw [DirectedPath.Walk.support_cons,
        List.dropLast_cons_of_ne_nil p.support_ne_nil]
      rcases he with he | he
      · have hxa : x = a := congrArg Prod.fst he
        exact hxa ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih he)

/-- A finite chain in a relation contained in `residual ∪ forward` either
uses residual edges only or displays its first forward edge with relation
prefix and suffix. -/
private theorem reflTransGen_residual_or_exists_forward
    {E residual forward : Set (V × V)} {a b : V}
    (hsub : E ⊆ residual ∪ forward)
    (hab : Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b) :
    Relation.ReflTransGen (fun x y ↦ (x, y) ∈ residual) a b ∨
      ∃ u v,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ residual) a u ∧
        (u, v) ∈ forward ∧
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) v b := by
  induction hab using Relation.ReflTransGen.trans_induction_on with
  | refl => exact Or.inl .refl
  | single hab =>
      rcases hsub hab with hresidual | hforward
      · exact Or.inl (.single hresidual)
      · exact Or.inr ⟨_, _, .refl, hforward, .refl⟩
  | trans hab hbc ihab ihbc =>
      rcases ihab with habResidual | ⟨u, v, hau, huv, hvb⟩
      · rcases ihbc with hbcResidual | ⟨u, v, hbu, huv, hvc⟩
        · exact Or.inl (habResidual.trans hbcResidual)
        · exact Or.inr ⟨u, v, habResidual.trans hbu, huv, hvc⟩
      · exact Or.inr ⟨u, v, hau, huv, hvb.trans hbc⟩

/-- The exact residual/first-selected-forward data carried by a concrete
first-hit path. -/
def SplitGroundedFirstBoundaryDepartureOutcome
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    {O : L.SplitGroundedPreStoppedBoundaryObstruction R}
    (D : L.SplitGroundedFirstBoundaryReduction R O) : Prop :=
    Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ residualLadderEdges
          (GroundedDepartureIndexed (L := L) (hL := hL)
            (hground := hground)) S)
        D.reduced.earlier D.reduced.later ∨
      ∃ (c : ActiveControlRequestAt
          (GroundedDepartureIndexed (L := L) (hL := hL)
            (hground := hground)) S K (∅ : Set V))
          (u v : V),
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ residualLadderEdges
            (GroundedDepartureIndexed (L := L) (hL := hL)
              (hground := hground)) S)
          D.reduced.earlier u ∧
        (u, v) ∈
          (selectedErasedCompression
            (GroundedDepartureIndexed (L := L) (hL := hL)
              (hground := hground)) S K
            (chosenRequest c.1)).path.directionEdges .forward ∧
        (u, v) ∈ D.path.edgeSet ∧
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedDepartureIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅)
          v D.reduced.later

/-- Exact first-forward decomposition of the concrete first-hit path. -/
theorem SplitGroundedFirstBoundaryReduction.residual_or_firstSelectedForward
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    {O : L.SplitGroundedPreStoppedBoundaryObstruction R}
    (D : L.SplitGroundedFirstBoundaryReduction R O) :
    SplitGroundedFirstBoundaryDepartureOutcome D := by
  let E := erasedSelectedSwitchedEdgesAt
    (GroundedDepartureIndexed (L := L) (hL := hL)
      (hground := hground)) S K ∅
  let residual := residualLadderEdges
    (GroundedDepartureIndexed (L := L) (hL := hL)
      (hground := hground)) S
  let forward := erasedSelectedDirectionEdgesAt
    (GroundedDepartureIndexed (L := L) (hL := hL)
      (hground := hground)) S K ∅ .forward
  have hpath : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ E ∩ D.path.edgeSet)
      D.path.start D.path.finish := by
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ D.path.edgeSet)
      (p := fun x y ↦ (x, y) ∈ E ∩ D.path.edgeSet)
    · intro x y hxy
      exact ⟨D.edgeSet_subset hxy, hxy⟩
    · exact _root_.Erdos599.Alternating.Walk.reflTransGen_edgeSet D.path.walk
  have hsub : E ∩ D.path.edgeSet ⊆
      residual ∪ (forward ∩ D.path.edgeSet) := by
    intro e he
    have heE := he.1
    change e ∈ erasedSelectedSwitchedEdgesAt
      (GroundedDepartureIndexed (L := L) (hL := hL)
        (hground := hground)) S K ∅ at heE
    rw [erasedSelectedSwitchedEdgesAt_empty_eq] at heE
    rcases heE with ⟨heResidual, _heNotCut⟩ | heForward
    · exact Or.inl heResidual
    · exact Or.inr ⟨heForward, he.2⟩
  rcases reflTransGen_residual_or_exists_forward hsub hpath with
    hresidual | ⟨u, v, hprefix, huv, hsuffix⟩
  · left
    simpa only [D.start_eq, D.finish_eq] using hresidual
  · right
    have huvForward : (u, v) ∈ forward := huv.1
    simp only [forward, erasedSelectedDirectionEdgesAt,
      Set.mem_iUnion] at huvForward
    obtain ⟨c, huvOwner⟩ := huvForward
    refine ⟨c, u, v, ?_, huvOwner, huv.2, ?_⟩
    · simpa only [residual, D.start_eq] using hprefix
    · have hsuffix' : Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ E) v D.path.finish :=
        Relation.ReflTransGen.mono
          (r := fun x y ↦ (x, y) ∈ E ∩ D.path.edgeSet)
          (p := fun x y ↦ (x, y) ∈ E)
          (fun _ _ h ↦ h.1) _ _ hsuffix
      simpa only [E, D.finish_eq] using hsuffix'

/-- If the first-hit collision starts at a blocking point, the first
selected forward edge cannot begin strictly later on the same retained
fragment: the generic 8.21 order puts that tail weakly before the blocker,
while the residual prefix puts it weakly after.  A distinct `CV` tail would
be an earlier boundary hit. -/
theorem SplitGroundedFirstBoundaryReduction.residual_or_selectedForward_from_blocker
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    {O : L.SplitGroundedPreStoppedBoundaryObstruction R}
    (D : L.SplitGroundedFirstBoundaryReduction R O)
    (P : (L.splitGroundedPopularAuxiliaryInput hL.legal).Fragment)
    (hPG0 : P ∈ GroundingCut.G0
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut)
    (hblockable : GroundingCut.IsBlockable
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut P)
    (hearlier : GroundingCut.blockingPoint
      (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut P =
        D.reduced.earlier) :
    Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ residualLadderEdges
          (GroundedDepartureIndexed (L := L) (hL := hL)
            (hground := hground)) S)
        D.reduced.earlier D.reduced.later ∨
      ∃ (c : ActiveControlRequestAt
          (GroundedDepartureIndexed (L := L) (hL := hL)
            (hground := hground)) S K (∅ : Set V))
          (v : V),
        (D.reduced.earlier, v) ∈
          (selectedErasedCompression
            (GroundedDepartureIndexed (L := L) (hL := hL)
              (hground := hground)) S K
            (chosenRequest c.1)).path.directionEdges .forward ∧
        (D.reduced.earlier, v) ∈ D.path.edgeSet ∧
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (GroundedDepartureIndexed (L := L) (hL := hL)
              (hground := hground)) S K ∅)
          v D.reduced.later := by
  rcases D.residual_or_firstSelectedForward with
    hresidual | ⟨c, u, v, hprefix, huvOwner, huvPath, hsuffix⟩
  · exact Or.inl hresidual
  · right
    have hearlierSupport : D.reduced.earlier ∈ P.path.support := by
      rw [← hearlier]
      exact GroundingCut.blockingPoint_mem_support
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut P hblockable
    obtain ⟨huP, hearlierBefore⟩ :=
      GroundingFragmentResidualOrder.mem_and_beforeEq_of_reflTransGen_residualLadderEdges
        (GroundedDepartureIndexed (L := L) (hL := hL)
          (hground := hground)) S hPG0.1 hearlierSupport hprefix
    have hutail := selectedForwardTail_beforeEq_or_mem_CV
      (GroundedDepartureIndexed (L := L) (hL := hL)
        (hground := hground)) S K (chosenRequest c.1)
      (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL)
      P hPG0 hblockable huvOwner huP
    have huEq : u = D.reduced.earlier := by
      rcases hutail with huBefore | huCV
      · have hearlierEq : D.reduced.earlier = u := by
          apply GroundingCutDecoder.beforeEq_antisymm hearlierBefore
          simpa only [hearlier] using huBefore
        exact hearlierEq.symm
      · by_contra hne
        have huDrop : u ∈ D.path.walk.support.dropLast :=
          walkEdgeFst_mem_support_dropLast D.path.walk huvPath
        apply D.no_boundary_before huDrop
        exact ⟨GroundingCut.CV_subset_BB
          (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut huCV, hne⟩
    subst u
    exact ⟨c, v, huvOwner, huvPath, hsuffix⟩

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFirstBoundaryReduction.residual_or_firstSelectedForward
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedFirstBoundaryReduction.residual_or_selectedForward_from_blocker
