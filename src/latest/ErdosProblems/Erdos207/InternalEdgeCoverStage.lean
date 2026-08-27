/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeReserve
import ErdosProblems.Erdos207.InternalEdgeGreedyCover

/-!
# The internal-edge cover stage

This file combines the common reserve realization with the deterministic
edge-list induction.  The only remaining input is the KSSS obstruction-count
estimate: every reachable partial packing has at most `a` pair-conflict and
forbidden-completion blockers for the current edge.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Reserve concentration plus a uniform reachable-state obstruction bound
produce a legal packing covering all stage edges outside the next vortex. -/
theorem IsIterationTypical.exists_internalOuterEdge_greedy_cover
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V}
    {G : SimpleGraph V} {A P₀ : TripleSystemOn V}
    {p eta ξ : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta ξ h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hpacking₀ : IsPackingOn P₀) (havoid₀ : AvoidsForbidden P₀ F)
    (hh : 2 ≤ h) (r : ℝ≥0) (hr : r ≤ 1)
    (m a : ℕ)
    (hm : (m : ℝ≥0) ≤
      (1 - ξ) * (p ^ 2 * eta * (W.U i.succ).card))
    (ha : (a : ℝ) ≤ ((r ^ 2 : ℝ≥0) : ℝ) * m / 4)
    (hsmall : ((internalOuterEdges G (W.U i.succ)).card : ℝ) *
      Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * m) / 4) < 1)
    (hblocked : ∀ (Q : TripleSystemOn V) (e : Sym2 V),
      ∀ hreach : GreedyReachable F P₀ Q,
      Q ⊆ P₀ ∪ A →
      (Q \ P₀).card ≤ (internalOuterEdges G (W.U i.succ)).card →
      ∀ he : e ∈ internalOuterEdges G (W.U i.succ),
      ∀ hleave : (leaveGraph Q).Adj e.out.1 e.out.2,
      (edgeBlockedThirdVertices A Q
          (out_fst_ne_snd_of_mem_graphEdges
            (internalOuterEdges_subset_graphEdges G (W.U i.succ) he)) ∪
        forbiddenBlockedThirdVertices F A Q
          (out_fst_ne_snd_of_mem_graphEdges
            (internalOuterEdges_subset_graphEdges G (W.U i.succ) he))).card ≤ a) :
    ∃ ω : Sym2 V → Bool, ∃ Q : TripleSystemOn V,
      GreedyReachable F P₀ Q ∧ Q ⊆ P₀ ∪ A ∧
      ∀ e ∈ internalOuterEdges G (W.U i.succ),
        (coveredGraph Q).Adj e.out.1 e.out.2 := by
  let E := internalOuterEdges G (W.U i.succ)
  let S : Sym2 V → Finset V := fun e ↦
    iterationExtensionVertices A
      (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
  obtain ⟨ω, hω⟩ :=
    htyp.exists_reserve_realization_for_internalOuterEdges htri i hstage
      hGsupp hh r hr m a hm ha hsmall
  have hne : ∀ e, e ∈ E.toList → e.out.1 ≠ e.out.2 := by
    intro e he
    apply out_fst_ne_snd_of_mem_graphEdges
    exact internalOuterEdges_subset_graphEdges G (W.U i.succ) (by simpa [E] using he)
  have hu : ∀ e, e ∈ E.toList → e.out.1 ∉ W.U i.succ := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp (by simpa [E] using he)).2.1
  have hv : ∀ e, e ∈ E.toList → e.out.2 ∉ W.U i.succ := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp (by simpa [E] using he)).2.2
  have hSU : ∀ e, e ∈ E.toList → S e ⊆ W.U i.succ := by
    intro e _he
    exact iterationExtensionVertices_subset A
      (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
  have hA : ∀ e, ∀ he : e ∈ E.toList, ∀ w, ∀ hw : w ∈ S e,
      let w' : ThirdVertex e.out.1 e.out.2 :=
        ⟨w, fun h ↦ hu e he (h ▸ hSU e he hw),
          fun h ↦ hv e he (h ▸ hSU e he hw)⟩
      thirdVertexTriple (hne e he) w' ∈ A := by
    intro e he w hw
    exact iterationExtensionVertices_edge_thirdVertexTriple_mem
      (hne e he) (hu e he) (hv e he) hw
  have hsurplus : ∀ (Q : TripleSystemOn V) (e : Sym2 V),
      ∀ hreach : GreedyReachable F P₀ Q, Q ⊆ P₀ ∪ A →
      (Q \ P₀).card ≤ E.toList.length →
      ∀ he : e ∈ E.toList,
      (leaveGraph Q).Adj e.out.1 e.out.2 →
      (edgeBlockedThirdVertices A Q (hne e he) ∪
        forbiddenBlockedThirdVertices F A Q (hne e he)).card <
        (activeReserveWedgeVertices G (W.U i.succ) (S e)
          e.out.1 e.out.2 ω).card := by
    intro Q e hreach hsub hcard he heLeave
    have heE : e ∈ internalOuterEdges G (W.U i.succ) := by
      simpa [E] using he
    have hcardE : (Q \ P₀).card ≤
        (internalOuterEdges G (W.U i.succ)).card := by
      simpa [E] using hcard
    have hblock := hblocked Q e hreach hsub hcardE heE heLeave
    have hsupply := hω e heE
    dsimp only [S] at hsupply
    exact hblock.trans_lt hsupply
  obtain ⟨Q, hreach, hsub, _hcard, hcover⟩ :=
    exists_greedyReachable_cover_edgeList F A P₀ G (W.U i.succ) ω
      E.toList S hpacking₀ havoid₀ hne hu hv hSU hA hsurplus
  refine ⟨ω, Q, hreach, hsub, ?_⟩
  intro e he
  exact hcover e (by simpa [E] using he)

end

end Erdos207
