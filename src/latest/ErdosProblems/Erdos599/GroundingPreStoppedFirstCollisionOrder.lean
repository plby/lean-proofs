/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedBoundaryFirstHit
import ErdosProblems.Erdos599.GroundingPreStoppedForwardCollisionOrder
import ErdosProblems.Erdos599.AlternatingDichotomy

/-!
# First selected departure in a normalized boundary collision

For a collision normalized at the first distinct boundary point, a residual
prefix starting at a blocking point cannot reach a different `CV` vertex
before the endpoint.  Hence the first selected forward edge, if one occurs,
leaves exactly at the blocking point.
-/

noncomputable section

open Set
open Erdos599.DirectedPath

namespace Erdos599
namespace DWeb.KappaLadder
namespace Assertion822PreStoppedBoundaryObstruction

open GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The tail of an edge in a finite directed walk occurs before the final
vertex.  This local form keeps the first-hit normalization independent of
the later alternating-path dichotomy module. -/
private theorem walkEdgeFst_mem_support_dropLast
    {D : Digraph V} {a b x y : V}
    (p : Walk D a b) (he : (x, y) ∈ p.edgeSet) :
    x ∈ p.support.dropLast := by
  induction p with
  | nil => simp at he
  | @cons a z b h p ih =>
      simp only [Walk.edgeSet_cons, Set.mem_union,
        Set.mem_singleton_iff] at he
      rw [Walk.support_cons,
        List.dropLast_cons_of_ne_nil p.support_ne_nil]
      rcases he with he | he
      · have hxa : x = a := congrArg Prod.fst he
        exact hxa ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih he)

/-- A normalized blocking collision is residual-only, or its first selected
forward edge has a named active owner and leaves exactly at the blocking
point.  The edge is retained in the concrete first-hit path and its suffix
still reaches the reduced collision endpoint. -/
theorem FirstBoundaryReduction.residual_or_selectedForward_from_blocker
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {o : L.Assertion822PreStoppedBoundaryObstruction hL S R}
    (D : FirstBoundaryReduction o)
    (P : (L.popularAuxiliaryInput hL.legal).Fragment)
    (hPG0 : P ∈ GroundingCut.G0
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (hblockable : GroundingCut.IsBlockable
      (L.popularAuxiliaryInput hL.legal) S.cut P)
    (hearlier : GroundingCut.blockingPoint
      (L.popularAuxiliaryInput hL.legal) S.cut P = D.reduced.earlier) :
    Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ residualLadderEdges
          (L.popularAuxiliaryIndexed hL) S)
        D.reduced.earlier D.reduced.later ∨
      ∃ (c : ActiveControlRequestAt
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) (∅ : Set V))
          (v : V),
        (D.reduced.earlier, v) ∈
          (selectedErasedCompression
            (L.popularAuxiliaryIndexed hL) S
            (L.reservedGroundedControls hL S R)
            (chosenRequest c.1)).path.directionEdges .forward ∧
        (D.reduced.earlier, v) ∈ D.path.edgeSet ∧
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            L.assertion822ReservedPreStoppedEdges hL S R)
          v D.reduced.later := by
  let E := L.assertion822ReservedPreStoppedEdges hL S R
  let residual := residualLadderEdges (L.popularAuxiliaryIndexed hL) S
  let forward := erasedSelectedDirectionEdgesAt
    (L.popularAuxiliaryIndexed hL) S
    (L.reservedGroundedControls hL S R) ∅ .forward
  have hpath : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ E ∩ D.path.edgeSet)
      D.path.start D.path.finish := by
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ D.path.edgeSet)
      (p := fun x y ↦ (x, y) ∈ E ∩ D.path.edgeSet)
    · intro x y hxy
      exact ⟨D.edgeSet_subset hxy, hxy⟩
    · exact _root_.Erdos599.Alternating.Walk.reflTransGen_edgeSet
        D.path.walk
  have hsub : E ∩ D.path.edgeSet ⊆
      residual ∪ (forward ∩ D.path.edgeSet) := by
    intro e he
    have heE := he.1
    change e ∈ erasedSelectedSwitchedEdgesAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) ∅ at heE
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
    have huvPath : (u, v) ∈ D.path.edgeSet := huv.2
    simp only [forward, erasedSelectedDirectionEdgesAt,
      Set.mem_iUnion] at huvForward
    obtain ⟨c, huvOwner⟩ := huvForward
    have hprefix' : Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ residualLadderEdges
          (L.popularAuxiliaryIndexed hL) S)
        D.reduced.earlier u := by
      simpa only [residual, D.start_eq] using hprefix
    have hutail := firstSelectedForwardTail_eq_earlier_or_mem_CV
      D.reduced P hPG0 hblockable hearlier c hprefix' huvOwner
    have huEq : u = D.reduced.earlier := by
      rcases hutail with huEq | huCV
      · exact huEq
      · by_contra hne
        have huDrop : u ∈ D.path.walk.support.dropLast :=
          walkEdgeFst_mem_support_dropLast D.path.walk huvPath
        apply D.no_boundary_before huDrop
        exact ⟨GroundingCut.CV_subset_BB
          (L.popularAuxiliaryInput hL.legal) S.cut huCV, hne⟩
    subst u
    refine ⟨c, v, huvOwner, huvPath, ?_⟩
    have hsuffix' : Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ E) v D.path.finish := by
      exact Relation.ReflTransGen.mono
        (r := fun x y ↦ (x, y) ∈ E ∩ D.path.edgeSet)
        (p := fun x y ↦ (x, y) ∈ E)
        (fun _ _ h ↦ h.1) _ _ hsuffix
    simpa only [E, D.finish_eq] using hsuffix'

end Assertion822PreStoppedBoundaryObstruction
end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.FirstBoundaryReduction.residual_or_selectedForward_from_blocker
