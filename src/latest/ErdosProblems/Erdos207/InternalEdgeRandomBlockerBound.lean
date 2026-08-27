/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeRandomCoverStage
import ErdosProblems.Erdos207.InternalEdgeDegreeCover
import ErdosProblems.Erdos207.InternalEdgeThreatTransport

/-!
# Concrete blocker bounds for the random internal-edge stage

The random stage was initially stated with a support-uniform blocker bound.
This file discharges that abstract premise from the residual graph degree and
rooted forbidden-configuration estimates used in the KSSS master iteration.
The resulting law retains the terminal coverage certificate and B4.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Residual degrees and a uniform rooted-active cutoff instantiate the
blocker premise of the random internal-edge cover stage. -/
theorem IsIterationTypical.exists_internalOuterEdge_randomGreedyLaw_of_degree_rooted
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : Nat} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V}
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A P0 : TripleSystemOn V}
    {p eta xi : NNReal} {h : Nat}
    (htyp : IsIterationTypical W stage G A p eta xi h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hstage : stage.val <= i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hpacking0 : IsPackingOn P0) (havoid0 : AvoidsForbidden P0 F)
    (hinitial : ∀ T ∈ A, TriangleAvoidsGraph (coveredGraph P0) T)
    (hh : 2 <= h) (r : NNReal) (hr : r <= 1)
    (m a D d R k : Nat) (hD : 0 < D)
    (hm : (m : NNReal) <=
      (1 - xi) * (p ^ 2 * eta * (W.U i.succ).card))
    (ha : ((a + D : Nat) : Real) <=
      ((r ^ 2 : NNReal) : Real) * m / 4)
    (hsmall : ((internalOuterEdges G (W.U i.succ)).card : Real) *
      Real.exp (-(((r ^ 2 : NNReal) : Real) * m) / 4) < 1)
    (hfamily : ∀ C ∈ F, C.card <= k)
    (hscalar : 4 * d + R * k <= a)
    (hdegree : ∀ v : V, G.degree v <= d)
    (hroot : ∀ (Q : TripleSystemOn V) (e : Sym2 V),
      GreedyReachable F P0 Q ->
      Q ⊆ P0 ∪ A ->
      (Q \ P0).card <= (internalOuterEdges G (W.U i.succ)).card ->
      e ∈ internalOuterEdges G (W.U i.succ) ->
      (rootedActiveForbiddenConfigurations F Q e.out.1 e.out.2).card <= R) :
    ∃ omega : Sym2 V -> Bool,
      let E := internalOuterEdges G (W.U i.succ)
      let S : Sym2 V -> Finset V := fun e =>
        iterationExtensionVertices A
          (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
      let hne : ∀ e, e ∈ E.toList -> e.out.1 ≠ e.out.2 := fun e he =>
        out_fst_ne_snd_of_mem_graphEdges
          (internalOuterEdges_subset_graphEdges G (W.U i.succ)
            (by simpa only [Finset.mem_toList] using he))
      let L := internalEdgeGreedyProcessLaw F G (W.U i.succ) omega S
        E.toList hne D P0
      L.SupportedOn (fun z =>
        GreedyReachable F P0 z.chosen ∧ z.chosen ⊆ P0 ∪ A ∧
          (z.chosen \ P0).card <= E.card ∧
          ∀ e ∈ E, (coveredGraph z.chosen).Adj e.out.1 e.out.2) ∧
      ∀ Q : TripleSystemOn V, Disjoint Q P0 ->
        L.probability (fun z => Q ⊆ z.chosen) <=
          (Q.card.factorial : NNReal) * ((D : NNReal)⁻¹ ^ Q.card) := by
  apply htyp.exists_internalOuterEdge_randomGreedyLaw htri i hstage hGsupp
    hpacking0 havoid0 hh r hr m a D hD hm ha hsmall
  intro Q e hreach hsub hnew he hleave
  obtain ⟨hdu, hdv⟩ := internalOuterEdge_new_endpoint_stars_le htri
    (hreach.isPacking hpacking0) hsub hdegree e he
  exact card_blockedThirdVertices_le_four_mul_add_mul
    (hreach.isPacking hpacking0) hinitial hleave hdu hdv
      (hroot Q e hreach hsub hnew he) hfamily hscalar

/-- The rooted-active cutoff throughout the random stage follows from the
initial rooted count and a uniform bound on witnesses using one newly
inserted triangle. -/
theorem IsIterationTypical.exists_internalOuterEdge_randomGreedyLaw_of_initial_rooted
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : Nat} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V}
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A P0 : TripleSystemOn V}
    {p eta xi : NNReal} {h : Nat}
    (htyp : IsIterationTypical W stage G A p eta xi h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hstage : stage.val <= i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hpacking0 : IsPackingOn P0) (havoid0 : AvoidsForbidden P0 F)
    (hinitial : ∀ T ∈ A, TriangleAvoidsGraph (coveredGraph P0) T)
    (hh : 2 <= h) (r : NNReal) (hr : r <= 1)
    (m a D d R0 R k K : Nat) (hD : 0 < D)
    (hm : (m : NNReal) <=
      (1 - xi) * (p ^ 2 * eta * (W.U i.succ).card))
    (ha : ((a + D : Nat) : Real) <=
      ((r ^ 2 : NNReal) : Real) * m / 4)
    (hsmall : ((internalOuterEdges G (W.U i.succ)).card : Real) *
      Real.exp (-(((r ^ 2 : NNReal) : Real) * m) / 4) < 1)
    (hfamily : ∀ C ∈ F, C.card <= k)
    (hblockScalar : 4 * d + R * k <= a)
    (hdegree : ∀ v : V, G.degree v <= d)
    (hroot0 : ∀ e ∈ internalOuterEdges G (W.U i.succ),
      (rootedActiveForbiddenConfigurations
        F P0 e.out.1 e.out.2).card <= R0)
    (husing : ∀ e ∈ internalOuterEdges G (W.U i.succ),
      ∀ T : TripleOn V,
        (rootedThreatWitnessesUsing F e.out.1 e.out.2 T).card <= K)
    (htransportScalar :
      R0 * k + (internalOuterEdges G (W.U i.succ)).card * K <= R) :
    ∃ omega : Sym2 V -> Bool,
      let E := internalOuterEdges G (W.U i.succ)
      let S : Sym2 V -> Finset V := fun e =>
        iterationExtensionVertices A
          (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
      let hne : ∀ e, e ∈ E.toList -> e.out.1 ≠ e.out.2 := fun e he =>
        out_fst_ne_snd_of_mem_graphEdges
          (internalOuterEdges_subset_graphEdges G (W.U i.succ)
            (by simpa only [Finset.mem_toList] using he))
      let L := internalEdgeGreedyProcessLaw F G (W.U i.succ) omega S
        E.toList hne D P0
      L.SupportedOn (fun z =>
        GreedyReachable F P0 z.chosen ∧ z.chosen ⊆ P0 ∪ A ∧
          (z.chosen \ P0).card <= E.card ∧
          ∀ e ∈ E, (coveredGraph z.chosen).Adj e.out.1 e.out.2) ∧
      ∀ Q : TripleSystemOn V, Disjoint Q P0 ->
        L.probability (fun z => Q ⊆ z.chosen) <=
          (Q.card.factorial : NNReal) * ((D : NNReal)⁻¹ ^ Q.card) := by
  apply htyp.exists_internalOuterEdge_randomGreedyLaw_of_degree_rooted
    htri i hstage hGsupp hpacking0 havoid0 hinitial hh r hr
      m a D d R k hD hm ha hsmall hfamily hblockScalar hdegree
  intro Q e hreach _hsub hnew he
  exact card_rootedActive_le_of_initial_and_new_budget hfamily
    (husing e he) hreach.initial_subset (hroot0 e he) hnew
      htransportScalar

end

end Erdos207
