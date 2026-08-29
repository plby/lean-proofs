/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedDecode

/-!
# Cut-edge accounting for the erased grounding switch

This file gives the pointwise membership laws for the repaired Assertion
8.22 relation.  A represented cut edge is absent from the residual ladder.
Thus it is absent from the final directional relation exactly when no
selected forward link adds it.  Conversely, a non-cut ladder edge survives
when it is not deleted, or when a selected forward link adds it.

The statements deliberately expose the route-disjointness obligation.  It
is a geometric fact about the head-stopping decoder, whereas the deductions
from that fact to the final switched relation are purely set-theoretic.
-/

noncomputable section

namespace Erdos599
namespace GroundingCutEdgeRelation

open Set
open GroundingErasedDecode
open PopularGroundingBridge GroundingSimultaneousDecode
open PopularAuxiliary.Input

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-! ## The head-stopping edge-request trace -/

private noncomputable local instance signedEdgeBEq : BEq (SignedEdge V) :=
  ⟨fun s t => @decide (s = t) (Classical.propDecidable _)⟩

private local instance signedEdgeLawfulBEq : LawfulBEq (SignedEdge V) :=
  ⟨by intro s t; simp⟩

private noncomputable local instance lambdaVertexBEq :
    BEq (PopularAuxiliary.Input.LambdaVertex V I) :=
  ⟨fun x y => @decide (x = y) (Classical.propDecidable _)⟩

private local instance lambdaVertexLawfulBEq :
    LawfulBEq (PopularAuxiliary.Input.LambdaVertex V I) :=
  ⟨by intro x y; simp⟩

private theorem count_backward_gadgetSteps
    (L : PopularAuxiliary.Input Gamma I) (a : L.LV) (e : V × V) :
    List.count (SignedEdge.backward e) (L.gadgetSteps a) =
      List.count (.edge e.1 e.2) [a] := by
  rcases e with ⟨u, v⟩
  cases a with
  | old x =>
      rw [List.count_eq_zero.mpr (by simp [PopularAuxiliary.Input.gadgetSteps])]
      rw [List.count_eq_zero.mpr (by simp)]
  | edge x y =>
      by_cases hxy : (x, y) = (u, v)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
        exact (List.count_eq_one_of_mem (List.nodup_singleton _)
          (List.mem_singleton_self _)).trans
            (List.count_eq_one_of_mem (List.nodup_singleton _)
              (List.mem_singleton_self _)).symm
      · have hleft :
            List.count (SignedEdge.backward (u, v))
                (L.gadgetSteps (.edge x y)) = 0 :=
          List.count_eq_zero.mpr (by
            simp only [PopularAuxiliary.Input.gadgetSteps,
              List.mem_singleton]
            intro hs
            exact hxy (congrArg SignedEdge.edge hs).symm)
        have hright :
            List.count (.edge u v : L.LV) [.edge x y] = 0 :=
          List.count_eq_zero.mpr (by
            simp only [List.mem_singleton]
            intro hv
            have huv : u = x ∧ v = y := by simpa using hv
            exact hxy (Prod.ext huv.1.symm huv.2.symm))
        exact hleft.trans hright.symm
  | proxy i =>
      rw [List.count_eq_zero.mpr (by simp [PopularAuxiliary.Input.gadgetSteps])]
      rw [List.count_eq_zero.mpr (by simp)]

private theorem count_backward_connectorSteps
    (L : PopularAuxiliary.Input Gamma I) (a b : L.LV) (e : V × V) :
    List.count (SignedEdge.backward e) (L.connectorSteps a b) = 0 := by
  unfold PopularAuxiliary.Input.connectorSteps
  split <;>
    simp [SignedEdge.forward, SignedEdge.backward]

/-- The number of backward occurrences of an original edge in a decoded
auxiliary walk is the number of occurrences of its edge gadget. -/
theorem count_backward_decodeWalkSteps
    (L : PopularAuxiliary.Input Gamma I) {a b : L.LV}
    (q : DirectedPath.Walk L.lambda.graph a b) (e : V × V) :
    List.count (SignedEdge.backward e) (L.decodeWalkSteps q) =
      List.count (.edge e.1 e.2) q.support := by
  classical
  induction q with
  | @nil a =>
      rw [L.decodeWalkSteps_nil, count_backward_gadgetSteps,
        DirectedPath.Walk.support_nil]
  | @cons a b c hab q ih =>
      rw [L.decodeWalkSteps_cons, List.count_append, List.count_append,
        count_backward_gadgetSteps, count_backward_connectorSteps,
        DirectedPath.Walk.support_cons, ih]
      simp only [List.count_cons, List.count_nil, Nat.zero_add, Nat.add_zero]
      omega

/-- A simple auxiliary path ending at an edge gadget contains the final
backward gadget step exactly once.  Consequently the head-stopping prefix
does not contain that backward step at all. -/
theorem decodeFinitePathToEdgeEntry_backward_not_mem
    (L : PopularAuxiliary.Input Gamma I)
    (p : DirectedPath.FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source) (u v : V)
    (hfinish : p.finish = .edge u v) :
    SignedEdge.backward (u, v) ∉
      (L.decodeFinitePathToEdgeEntry p hstart u v hfinish).steps := by
  classical
  intro hmem
  have hpositive :
      0 < List.count (SignedEdge.backward (u, v))
        (L.decodeFinitePathToEdgeEntry p hstart u v hfinish).steps :=
    List.count_pos_iff.mpr hmem
  have hgadgetMem : (.edge u v : L.LV) ∈ p.walk.support := by
    rw [← hfinish]
    exact p.walk.end_mem_support
  have hgadgetCount :
      List.count (.edge u v : L.LV) p.walk.support = 1 :=
    List.count_eq_one_of_mem p.isPath hgadgetMem
  have htotal := count_backward_decodeWalkSteps L p.walk (u, v)
  have happ := congrArg
    (List.count (SignedEdge.backward (u, v)))
    (L.decodeFinitePathToEdgeEntry_steps_append p hstart u v hfinish)
  have hlast :
      List.count (SignedEdge.backward (u, v))
        [SignedEdge.backward (u, v)] = 1 :=
    List.count_eq_one_of_mem (List.nodup_singleton _)
      (List.mem_singleton_self _)
  rw [List.count_append, hlast, htotal, hgadgetCount] at happ
  omega

/-- For an edge request, the selected request trace is exactly the raw
decoded trace with its final backward traversal of the requested edge
removed.  This is the list-level source convention behind all subsequent
cut-edge accounting. -/
theorem selectedRequestTrace_edge_steps_append
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (e : edgeRequests L S.cut) :
    (selectedRequestTrace U S K (.inr e)).steps ++
        [SignedEdge.backward e.1] =
      L.decodeWalkSteps (strongSelectedPath U S K (.inr e)).walk := by
  unfold selectedRequestTrace
  apply L.decodeFinitePathToEdgeEntry_steps_append

/-- The selected trace for an edge request does not traverse its own
represented edge backward. -/
theorem selectedRequestTrace_edge_backward_not_mem
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (e : edgeRequests L S.cut) :
    SignedEdge.backward e.1 ∉
      (selectedRequestTrace U S K (.inr e)).steps := by
  unfold selectedRequestTrace
  apply decodeFinitePathToEdgeEntry_backward_not_mem

/-- Concrete `CE` specialization: the request canonically represented by a
cut ladder edge omits that edge's backward step. -/
theorem mem_CE_selectedRequestTrace_backward_not_mem
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) {e : V × V}
    (he : e ∈ GroundingCut.CE L S.cut) :
    SignedEdge.backward e ∉
      (selectedRequestTrace U S K
        (.inr (⟨e, he.1⟩ : edgeRequests L S.cut))).steps :=
  selectedRequestTrace_edge_backward_not_mem U S K ⟨e, he.1⟩

/-- A represented cut edge has already been deleted from the residual
ladder relation. -/
theorem mem_CE_not_mem_residualLadderEdges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U) {e : V × V}
    (he : e ∈ GroundingCut.CE L S.cut) :
    e ∉ residualLadderEdges U S := by
  intro heResidual
  exact heResidual.2 he

/-- Exact cut-edge law for the directional repaired relation.  A represented
cut edge cannot survive through the residual branch, so it occurs precisely
when a selected route adds it forward and the old-request exit filter does
not remove that departure. -/
theorem mem_erasedSelectedSwitchedEdges_iff_of_mem_CE
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) {e : V × V}
    (he : e ∈ GroundingCut.CE L S.cut) :
    e ∈ erasedSelectedSwitchedEdges U S K ↔
      e ∈ erasedSelectedDirectionEdges U S K .forward ∧
        e ∉ oldRequestOutgoingForwardCutEdges U S K := by
  have heResidual : e ∉ residualLadderEdges U S :=
    mem_CE_not_mem_residualLadderEdges U S he
  simp only [erasedSelectedSwitchedEdges, Set.mem_union, Set.mem_sdiff,
    heResidual, false_and, false_or]

/-- A represented cut edge is absent exactly when the filtered selected
forward branch does not contain it. -/
theorem not_mem_erasedSelectedSwitchedEdges_iff_of_mem_CE
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) {e : V × V}
    (he : e ∈ GroundingCut.CE L S.cut) :
    e ∉ erasedSelectedSwitchedEdges U S K ↔
      ¬ (e ∈ erasedSelectedDirectionEdges U S K .forward ∧
        e ∉ oldRequestOutgoingForwardCutEdges U S K) :=
  not_congr (mem_erasedSelectedSwitchedEdges_iff_of_mem_CE U S K he)

/-- Direct cut-edge elimination once forward-link disjointness from the
ladder family has been established. -/
theorem mem_CE_not_mem_erasedSelectedSwitchedEdges_of_not_mem_forward
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) {e : V × V}
    (he : e ∈ GroundingCut.CE L S.cut)
    (heForward : e ∉ erasedSelectedDirectionEdges U S K .forward) :
    e ∉ erasedSelectedSwitchedEdges U S K :=
  (not_mem_erasedSelectedSwitchedEdges_iff_of_mem_CE U S K he).2
    (fun h ↦ heForward h.1)

/-- The coarser route-disjointness hypothesis also eliminates a represented
cut edge, since forward route edges are contained in the route union. -/
theorem mem_CE_not_mem_erasedSelectedSwitchedEdges_of_not_mem_route
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) {e : V × V}
    (he : e ∈ GroundingCut.CE L S.cut)
    (heRoute : e ∉ erasedSelectedRouteEdges U S K) :
    e ∉ erasedSelectedSwitchedEdges U S K := by
  apply mem_CE_not_mem_erasedSelectedSwitchedEdges_of_not_mem_forward
    U S K he
  exact fun heForward ↦ heRoute
    (erasedSelectedDirectionEdges_subset_routeEdges U S K .forward heForward)

/-- Exact classification of a non-cut ladder edge.  Such an edge starts in
the residual relation: it survives if it is not deleted, or if the filtered
selected-forward branch adds it. -/
theorem mem_erasedSelectedSwitchedEdges_iff_of_mem_familyEdges_of_not_mem_CE
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) {e : V × V}
    (heFamily : e ∈ L.familyEdges)
    (heCut : e ∉ GroundingCut.CE L S.cut) :
    e ∈ erasedSelectedSwitchedEdges U S K ↔
      e ∉ erasedSelectedToggleEdges U S K ∨
        (e ∈ erasedSelectedDirectionEdges U S K .forward ∧
          e ∉ oldRequestOutgoingForwardCutEdges U S K) := by
  have heResidual : e ∈ residualLadderEdges U S :=
    ⟨heFamily, heCut⟩
  simp only [erasedSelectedSwitchedEdges, Set.mem_union, Set.mem_sdiff,
    heResidual, true_and]

/-- In the absence of overlap with the selected route union, a non-cut
family edge is retained exactly when it is not in the deletion set. -/
theorem mem_erasedSelectedSwitchedEdges_iff_of_nonCut_familyEdge_of_not_mem_route
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) {e : V × V}
    (heFamily : e ∈ L.familyEdges)
    (heCut : e ∉ GroundingCut.CE L S.cut)
    (heRoute : e ∉ erasedSelectedRouteEdges U S K) :
    e ∈ erasedSelectedSwitchedEdges U S K ↔
      e ∉ erasedSelectedToggleEdges U S K := by
  have heForward :
      e ∉ erasedSelectedDirectionEdges U S K .forward :=
    fun h ↦ heRoute
      (erasedSelectedDirectionEdges_subset_routeEdges U S K .forward h)
  rw [mem_erasedSelectedSwitchedEdges_iff_of_mem_familyEdges_of_not_mem_CE
    U S K heFamily heCut]
  simp [heForward]

/-- Convenient retained-edge form of the preceding classification. -/
theorem mem_erasedSelectedSwitchedEdges_of_nonCut_familyEdge
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) {e : V × V}
    (heFamily : e ∈ L.familyEdges)
    (heCut : e ∉ GroundingCut.CE L S.cut)
    (heRoute : e ∉ erasedSelectedRouteEdges U S K)
    (heToggle : e ∉ erasedSelectedToggleEdges U S K) :
    e ∈ erasedSelectedSwitchedEdges U S K :=
  (mem_erasedSelectedSwitchedEdges_iff_of_nonCut_familyEdge_of_not_mem_route
    U S K heFamily heCut heRoute).2 heToggle

end GroundingCutEdgeRelation
end Erdos599
