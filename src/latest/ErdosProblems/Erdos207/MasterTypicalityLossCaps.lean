/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.MasterExtensionLoss
import ErdosProblems.Erdos207.MasterLinkDegreeLoss
import ErdosProblems.Erdos207.MasterLinkStarConditioning
import ErdosProblems.Erdos207.RootedThreatExtraction

/-!
# Simultaneous caps imply the master typicality-loss event

This file packages the deterministic end of the T1--T3 argument.  Vertex
star caps control both degree losses and the graph-removal part of extension
loss.  Rooted-active-configuration caps control the remaining forbidden
part.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Pointwise T1--T3 implication used under the joint master law. -/
theorem masterTypicalityLossEvent_of_star_and_rooted_caps
    {V : Type*} [Fintype V] [DecidableEq V] {ell : Nat}
    {W : Vortex V ell} {k next : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V}
    {A I D R M : TripleSystemOn V}
    {p eta xi xi' : NNReal} {h a r q : Nat}
    (caps : V -> Nat)
    (hold : IsMasterStagePointwiseGood W k F G A I D p eta xi h)
    (hstep : IsMasterCoverStep F G (W.U next) A I D (R ∪ M))
    (hstar : LinkStarCapsGood caps M)
    (hroot : RootedActiveCapsGood F (I ∪ (D ∪ (R ∪ M))) r)
    (hFcard : ∀ S ∈ F, S.card ≤ q)
    (huniformStar : ∀ v : V,
      2 * ((triplesThrough R v).card + caps v) ≤ a)
    (hdegreeBudgetSame : ∀ i : Fin ell, next.val ≤ i.val →
      ∀ v ∈ W.U i.castSucc,
        (2 : NNReal) * ((triplesThrough R v).card + caps v) ≤
          (xi' - xi) * (p * (W.U i.castSucc).card))
    (hdegreeBudgetNext : ∀ i : Fin ell, next.val ≤ i.val →
      ∀ v ∈ W.U i.castSucc,
        (2 : NNReal) * ((triplesThrough R v).card + caps v) ≤
          (xi' - xi) * (p * (W.U i.succ).card))
    (hextensionBudget : ∀ i : Fin ell, next.val ≤ i.val →
      ∀ iStar : Fin (ell + 1),
        (iStar = i.castSucc ∨ iStar = i.succ) →
      ∀ Q : SimpleGraph V,
        Q ≤ updatedStageGraph G (W.U next) (R ∪ M) →
        GraphSupportedOn Q (W.U i.castSucc : Set V) →
        (graphSupportFinset Q).card ≤ h →
      ((graphSupportFinset Q).card : NNReal) +
          (graphSupportFinset Q).card * a +
            (graphEdges Q).card * (r * q) ≤
        (xi' - xi) *
          (p ^ (graphSupportFinset Q).card *
            eta ^ (graphEdges Q).card * (W.U iStar).card)) :
    MasterTypicalityLossEvent W next F G A I D (R ∪ M)
      p eta xi xi' h := by
  have hpackingRM : IsPackingOn (R ∪ M) := by
    apply hstep.packing.mono
    intro T hT
    rcases mem_union.mp hT with hTR | hTM
    · exact mem_union_right I <| mem_union_right D <|
        mem_union_left M hTR
    · exact mem_union_right I <| mem_union_right D <|
        mem_union_right R hTM
  refine ⟨?_, ?_, ?_⟩
  · intro i hni v hv
    have hnexti : next ≤ i.castSucc := Fin.mk_le_mk.mpr hni
    exact nnreal_card_removedNeighbors_le_of_starCap
      G (W.U next) (W.U i.castSucc) R M v
      (W.antitone next i.castSucc hnexti hv)
      (W.antitone next i.castSucc hnexti)
      hpackingRM (caps v)
      ((xi' - xi) * (p * (W.U i.castSucc).card))
      (hstar v) (hdegreeBudgetSame i hni v hv)
  · intro i hni v hv
    have hnextCast : next ≤ i.castSucc := Fin.mk_le_mk.mpr hni
    have hnextSucc : next ≤ i.succ :=
      hnextCast.trans (Fin.castSucc_le_succ i)
    exact nnreal_card_removedNeighbors_le_of_starCap
      G (W.U next) (W.U i.succ) R M v
      (W.antitone next i.castSucc hnextCast hv)
      (W.antitone next i.succ hnextSucc)
      hpackingRM (caps v)
      ((xi' - xi) * (p * (W.U i.succ).card))
      (hstar v) (hdegreeBudgetNext i hni v hv)
  · intro i hni iStar hiStar Q hQ hQsupport hQcard
    have hnextStar : next ≤ iStar := by
      rcases hiStar with rfl | rfl
      · exact Fin.mk_le_mk.mpr hni
      · exact (Fin.mk_le_mk.mpr hni).trans (Fin.castSucc_le_succ i)
    apply extensionLoss_nnreal_le_of_caps hQ
      (W.antitone next iStar hnextStar)
      hold.2.2.2.2.2.1 hold.2.2.2.2.1 hstep.packing hstep.avoids
      (a := a) (r := r) (q := q)
    · intro v hvSupport
      have hvNext : v ∈ W.U next := by
        obtain ⟨w, hvw⟩ := mem_graphSupportFinset_iff.mp hvSupport
        exact (updatedStageGraph_supported G (W.U next) (R ∪ M)
          (hQ hvw)).1
      have hremoved := card_removedNeighbors_le_two_mul_starCounts
        G (W.U next) (W.U iStar) R M v
        hvNext
        (W.antitone next iStar hnextStar) hpackingRM
      exact hremoved.trans <| by
        calc
          2 * ((triplesThrough R v).card +
              (ambientTriplesThrough v ∩ M).card) ≤
              2 * ((triplesThrough R v).card + caps v) := by
            gcongr
            exact Nat.le_of_lt (hstar v)
          _ ≤ a := huniformStar v
    · exact hFcard
    · intro e he
      exact hroot e.out.1 e.out.2
        (out_fst_ne_snd_of_mem_graphEdges he)
    · exact hextensionBudget i hni iStar hiStar Q hQ hQsupport hQcard

end

end Erdos207
