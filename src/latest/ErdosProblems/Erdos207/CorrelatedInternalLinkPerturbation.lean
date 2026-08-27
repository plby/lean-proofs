/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CorrelatedInternalConditioning
import ErdosProblems.Erdos207.ReserveOverlapPowerBudgets

/-! # Actual correlated internal outcomes retain the preliminary spoke-loss event -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem correlatedRawInternal_supported_spoke_losses
    {Omega Xi V : Type*} [Fintype Xi] [DecidableEq Xi] [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (i : Fin ell) (F : ForbiddenFamilyOn V)
    (G : Omega → SimpleGraph V) (A old : Omega → TripleSystemOn V)
    (pre : Omega → Xi → TripleSystemOn V) (bits : Omega → Sym2 V → Bool)
    (threshold : ℕ) (hthreshold : 0 < threshold) (Kpre : Omega → FiniteLaw Xi) (omega : Omega)
    (hG : G omega ≤ leaveGraph (old omega))
    (hpre : (Kpre omega).SupportedOn fun xi ↦ pre omega xi ⊆ A omega ∧
      IsPackingOn (old omega ∪ pre omega xi) ∧ Disjoint (old omega) (pre omega xi) ∧
      AvoidsForbidden (old omega ∪ pre omega xi) F) (d : ℕ) :
    ((Kpre omega).jointBind (correlatedRawInternalKernel W i F G A old pre bits threshold omega)).SupportedOn
      fun z ↦ PreliminaryResidualDegreeGood (reserveProtectedOuterGraph (G omega) (W.U i.succ)
        (reserveEdges (G omega) (W.U i.succ) (bits omega))) (W.U i.succ) (pre omega z.1) d →
        ∀ center, center ∉ W.U i.succ →
          (protectedResidualSpokeVertices (G omega) (W.U i.succ)
            (reserveEdges (G omega) (W.U i.succ) (bits omega)) (pre omega z.1) center).card ≤ d ∧
          (((coveredGraph (correlatedRawInternalAdded old pre omega z.1 z.2)).neighborFinset center) ∩
            W.U i.succ).card ≤ 2*d := by
  intro z hz hdegree center hc
  have hS := correlatedRawInternalKernel_supported_structure W i F G A old pre bits
    threshold hthreshold Kpre omega hG hpre z hz
  have hpack := hS.2.1.mono (subset_union_right :
    preliminaryInternalCombinedAdded (pre omega) (correlatedRawInternalAdded old pre omega) z ⊆ _)
  have hdiff : preliminaryInternalCombinedAdded (pre omega) (correlatedRawInternalAdded old pre omega) z \
      pre omega z.1 = correlatedRawInternalAdded old pre omega z.1 z.2 := by
    exact union_sdiff_cancel_left hS.2.2.2.1
  refine ⟨hdegree.protected_spokes hc, ?_⟩
  have hbound := hdegree.internal_covered_neighbors
    (reserveEdges_subset_crossingEdges (G omega) (W.U i.succ) (bits omega)) hpack hS.2.2.2.2.2 hc
  have heq : ((coveredGraph
      (preliminaryInternalCombinedAdded (pre omega) (correlatedRawInternalAdded old pre omega) z \
        pre omega z.1)).neighborFinset center ∩ W.U i.succ) =
      ((coveredGraph (correlatedRawInternalAdded old pre omega z.1 z.2)).neighborFinset center ∩
        W.U i.succ) := by
    ext x
    simp only [mem_inter, SimpleGraph.mem_neighborFinset]
    rw [hdiff]
  exact heq ▸ hbound

theorem conditioned_correlatedRawInternal_degree_failure_le
    {Omega Xi V : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype Xi] [DecidableEq Xi]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Omega) (W : Vortex V ell) (i : Fin ell) (F : ForbiddenFamilyOn V)
    (G : Omega → SimpleGraph V) (A old : Omega → TripleSystemOn V)
    (pre : Omega → Xi → TripleSystemOn V) (bits : Omega → Sym2 V → Bool)
    (Kpre : Omega → FiniteLaw Xi) (threshold d s : ℕ)
    (survival point constant preError rate error : ℝ≥0) (herror : error < 1)
    (hmixed : ∀ omega, 0 < L.mass omega → IsGraphMixedProductBound (Kpre omega) (pre omega)
      (reserveProtectedOuterGraph (G omega) (W.U i.succ)
        (reserveEdges (G omega) (W.U i.succ) (bits omega))) survival point constant preError)
    (hsupp : ∀ omega, 0 < L.mass omega → GraphSupportedOn (G omega) (W.U i.castSucc : Set V))
    (hRate : constant*survival ≤ rate) (hs : 2*s ≤ d+1) :
    let Kint := correlatedRawInternalKernel W i F G A old pre bits threshold
    let joint := L.jointBind (fun omega ↦ (Kpre omega).jointBind (Kint omega))
    let Success := fun z : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦ z.2.2.failed = false
    ∀ hpos : 0 < joint.probability Success, 1-error ≤ joint.probability Success →
      (joint.conditionOn Success hpos).probability (fun z ↦ ¬ PreliminaryResidualDegreeGood
        (reserveProtectedOuterGraph (G z.1) (W.U i.succ)
          (reserveEdges (G z.1) (W.U i.succ) (bits z.1))) (W.U i.succ) (pre z.1 z.2.1) d) ≤
        sourcePreliminaryDegreeFailure (Fintype.card V) (W.U i.castSucc).card d s rate constant preError /
          (1-error) := by
  dsimp only
  intro hpos hden
  let Kint := correlatedRawInternalKernel W i F G A old pre bits threshold
  let joint := L.jointBind (fun omega ↦ (Kpre omega).jointBind (Kint omega))
  let Success := fun z : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦ z.2.2.failed = false
  let Bad := fun z : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦ ¬ PreliminaryResidualDegreeGood
    (reserveProtectedOuterGraph (G z.1) (W.U i.succ)
      (reserveEdges (G z.1) (W.U i.succ) (bits z.1))) (W.U i.succ) (pre z.1 z.2.1) d
  have hbefore : joint.probability Bad ≤
      sourcePreliminaryDegreeFailure (Fintype.card V) (W.U i.castSucc).card d s rate constant preError := by
    apply L.jointBind_jointBind_probability_snd_fst_le_on_support Kpre Kint
      (fun omega xi ↦ ¬ PreliminaryResidualDegreeGood
        (reserveProtectedOuterGraph (G omega) (W.U i.succ)
          (reserveEdges (G omega) (W.U i.succ) (bits omega))) (W.U i.succ) (pre omega xi) d)
    intro omega hm
    exact (hmixed omega hm).protected_preliminary_degree_failure_le (hsupp omega hm) hRate le_rfl s d hs
  exact (joint.conditionOn_probability_le Success Bad hpos).trans
    ((div_le_div_of_nonneg_right hbefore zero_le).trans
      (div_le_div_of_nonneg_left zero_le (tsub_pos_iff_lt.mpr herror) hden))

end

end Erdos207
