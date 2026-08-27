/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SimultaneousReserveWedgeCandidates

/-!
# Reserve supply for all internal stage edges

The internal-edge part of KSSS Proposition 10.6 first considers stage edges
whose two endpoints lie outside the next vortex set.  This file defines that
finite edge family canonically using the endpoints returned by `Sym2.out` and
instantiates the simultaneous reserve-wedge extraction theorem on it.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Stage edges with both endpoints outside `U`. -/
noncomputable def internalOuterEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) : Finset (Sym2 V) := by
  classical
  exact (graphEdges G).filter fun e ↦ e.out.1 ∉ U ∧ e.out.2 ∉ U

@[simp]
lemma mem_internalOuterEdges_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {e : Sym2 V} :
    e ∈ internalOuterEdges G U ↔
      e ∈ graphEdges G ∧ e.out.1 ∉ U ∧ e.out.2 ∉ U := by
  classical
  simp [internalOuterEdges, and_assoc]

lemma graph_adj_out_of_mem_graphEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {e : Sym2 V} (he : e ∈ graphEdges G) :
    G.Adj e.out.1 e.out.2 := by
  have heSet : e ∈ G.edgeSet := mem_graphEdges_iff.mp he
  rw [← e.out_eq] at heSet
  exact heSet

lemma out_fst_ne_snd_of_mem_graphEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {e : Sym2 V} (he : e ∈ graphEdges G) :
    e.out.1 ≠ e.out.2 :=
  (graph_adj_out_of_mem_graphEdges he).ne

lemma internalOuterEdges_subset_graphEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) :
    internalOuterEdges G U ⊆ graphEdges G := by
  intro e he
  exact (mem_internalOuterEdges_iff.mp he).1

lemma card_internalOuterEdges_le_card_graphEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) :
    (internalOuterEdges G U).card ≤ (graphEdges G).card :=
  card_le_card (internalOuterEdges_subset_graphEdges G U)

/-- One reserve realization simultaneously leaves a large wedge supply for
every actual internal stage edge. -/
theorem IsIterationTypical.exists_reserve_realization_for_internalOuterEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta ξ : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta ξ h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hh : 2 ≤ h) (r : ℝ≥0) (hr : r ≤ 1)
    (m a : ℕ)
    (hm : (m : ℝ≥0) ≤
      (1 - ξ) * (p ^ 2 * eta * (W.U i.succ).card))
    (ha : (a : ℝ) ≤ ((r ^ 2 : ℝ≥0) : ℝ) * m / 4)
    (hsmall : ((internalOuterEdges G (W.U i.succ)).card : ℝ) *
      Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * m) / 4) < 1) :
    ∃ ω : Sym2 V → Bool,
      ∀ e ∈ internalOuterEdges G (W.U i.succ),
        let S := iterationExtensionVertices A
          (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
        a < (activeReserveWedgeVertices G (W.U i.succ) S
          e.out.1 e.out.2 ω).card := by
  let E := internalOuterEdges G (W.U i.succ)
  have hedge : ∀ e ∈ E, e ∈ graphEdges G := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp he).1
  have hadj : ∀ e ∈ E, G.Adj e.out.1 e.out.2 := by
    intro e he
    exact graph_adj_out_of_mem_graphEdges (hedge e he)
  have houter : ∀ e ∈ E,
      e.out.1 ∈ W.U i.castSucc ∧ e.out.2 ∈ W.U i.castSucc := by
    intro e he
    exact hGsupp (hadj e he)
  have hinner : ∀ e ∈ E,
      e.out.1 ∉ W.U i.succ ∧ e.out.2 ∉ W.U i.succ := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp he).2
  simpa only [E] using
    (htyp.exists_reserve_realization_with_internal_supplies htri i hstage E
      (fun e : Sym2 V ↦ e.out.1) (fun e : Sym2 V ↦ e.out.2)
      (fun e he ↦ out_fst_ne_snd_of_mem_graphEdges (hedge e he))
      (fun e he ↦ (houter e he).1) (fun e he ↦ (houter e he).2)
      (fun e he ↦ (hinner e he).1) (fun e he ↦ (hinner e he).2)
      hadj hh r hr m hm (fun _e ↦ a) (fun _e _he ↦ ha) hsmall)

end

end Erdos207
