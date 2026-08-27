/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.MasterLinkStarConditioning
import ErdosProblems.Erdos207.ReserveAwareMasterIterationTypicalUpdate

/-!
# Reserve-aware master update with T1--T2 derived from star conditioning

This theorem conditions the simultaneous link kernel on uniform triangle-star
caps.  The C4 binomial tail gives the conditioned kernel and the deterministic
degree-loss lemma discharges both degree clauses of next-stage typicality.
Only the genuinely rooted extension-loss estimate (T3) remains as a
post-conditioning input.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

theorem exists_masterIterationGood_of_starCappedLinkKernel_numeric
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {ell : Nat} {law : FiniteLaw Omega}
    {linkLaw : Omega -> FiniteLaw (TripleSystemOn V)}
    {W : Vortex V ell} {k next : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {U : Finset V}
    {G : Omega -> SimpleGraph V}
    {A I D R : Omega -> TripleSystemOn V}
    {reserve : Omega -> Finset (Sym2 V)}
    {center : Omega -> ({x : V // x ∉ U} ↪ V)}
    {K : (omega : Omega) -> {x : V // x ∉ U} -> BipartiteLink V}
    {p reserveDensity C b alpha epsilon C' b' eta xi xi' : NNReal}
    {h : Nat}
    (caps : Omega -> V -> Nat)
    (hU : U = W.U next)
    (hreserve : IsReserveStronglyWellDistributed law W k I
      (fun omega => D omega ∪ R omega) reserve p reserveDensity C b)
    (hcenter : ∀ omega o, (K omega o).center = center omega o)
    (hout : ∀ omega o, center omega o ∉ U)
    (hleft : ∀ omega o, (K omega o).left ⊆ U)
    (hright : ∀ omega o, (K omega o).right ⊆ U)
    (hspokes : ∀ omega o, (K omega o).SpokesIn (reserve omega))
    (hlink : ∀ omega, (linkLaw omega).SupportedOn fun M =>
      IsSimultaneousLinkCover F (A omega)
          (I omega ∪ (D omega ∪ R omega)) (K omega) M ∧
        IsSimultaneousLinkFamily (K omega) M)
    (hC4 : ∀ omega Q,
      (linkLaw omega).probability (fun M => Q ⊆ M) <= alpha ^ Q.card)
    (htail : ∀ omega, ∑ v : V,
      ((ambientTriplesThrough v).powersetCard (caps omega v)).card *
        alpha ^ caps omega v <= epsilon)
    (hepsilon : epsilon < 1)
    (hnonempty : ∀ i, (W.U i).Nonempty)
    (hkn : k <= next) (hCC' : C <= C') (hC' : 1 <= C')
    (herrorFactor : (alpha / (1 - epsilon)) * C ^ 2 <= 1)
    (hbb' : b <= b')
    (hnew : ∀ T : TripleOn V,
      (alpha / (1 - epsilon)) * C ^ 2 * reserveDensity ^ 2 <=
        p / ((W.U (W.truncatedLevel next T)).card : NNReal))
    (hold : law.SupportedOn fun omega =>
      IsMasterStagePointwiseGood W k F (G omega) (A omega)
        (I omega) (D omega) p eta xi h)
    (hstate : law.SupportedOn fun omega =>
      IsIntermediateLinkState (G omega) U (A omega) (I omega) (D omega)
        (R omega) (K omega))
    (hxixi' : xi <= xi')
    (hdegreeBudgetSame : ∀ omega (i : Fin ell), next.val <= i.val ->
      ∀ v ∈ W.U i.castSucc,
        (2 : NNReal) * ((triplesThrough (R omega) v).card + caps omega v) <=
          (xi' - xi) * (p * (W.U i.castSucc).card))
    (hdegreeBudgetNext : ∀ omega (i : Fin ell), next.val <= i.val ->
      ∀ v ∈ W.U i.castSucc,
        (2 : NNReal) * ((triplesThrough (R omega) v).card + caps omega v) <=
          (xi' - xi) * (p * (W.U i.succ).card)) :
    ∃ hGood : ∀ omega,
        0 < (linkLaw omega).probability
          (LinkStarCapsGood (caps omega)),
      let cappedLaw : Omega -> FiniteLaw (TripleSystemOn V) := fun omega =>
        starCappedLinkLaw (linkLaw omega) (caps omega) (hGood omega)
      (HasEvenStageGraphs (law.jointBind cappedLaw)
        (fun z => updatedStageGraph (G z.1) U (R z.1 ∪ z.2)) ->
       (∀ omega M,
          0 < (cappedLaw omega).mass M ->
          IsMasterStagePointwiseGood W k F (G omega) (A omega)
            (I omega) (D omega) p eta xi h ->
          ∀ i : Fin ell, next.val <= i.val ->
          ∀ iStar : Fin (ell + 1),
            (iStar = i.castSucc ∨ iStar = i.succ) ->
          ∀ Q : SimpleGraph V,
            Q <= updatedStageGraph (G omega) U (R omega ∪ M) ->
            GraphSupportedOn Q (W.U i.castSucc : Set V) ->
            (graphSupportFinset Q).card <= h ->
          (((iterationExtensionVertices (A omega) Q (W.U iStar)) \
              iterationExtensionVertices
                (updatedStageAvailable F U (A omega) (I omega) (D omega)
                  (R omega ∪ M)) Q (W.U iStar)).card : NNReal) <=
            (xi' - xi) *
              (p ^ (graphSupportFinset Q).card *
                eta ^ (graphEdges Q).card * (W.U iStar).card)) ->
       IsMasterIterationGood (law.jointBind cappedLaw) W next F
        (fun z => updatedStageGraph (G z.1) U (R z.1 ∪ z.2))
        (fun z => updatedStageAvailable F U (A z.1) (I z.1) (D z.1)
          (R z.1 ∪ z.2))
        (fun z => I z.1) (fun z => D z.1 ∪ (R z.1 ∪ z.2))
        p eta xi' (2 * C') b' h) ∧
      (∀ omega, 1 - epsilon <=
        (linkLaw omega).probability (LinkStarCapsGood (caps omega))) := by
  let P : Omega -> TripleSystemOn V -> Prop := fun omega M =>
    IsSimultaneousLinkCover F (A omega)
        (I omega ∪ (D omega ∪ R omega)) (K omega) M ∧
      IsSimultaneousLinkFamily (K omega) M
  obtain ⟨hGood, hcapped, hC4capped, hlower⟩ :=
    exists_starCappedLinkKernel linkLaw caps P alpha epsilon hlink hC4
      htail hepsilon
  refine ⟨hGood, ?_, hlower⟩
  dsimp only
  let cappedLaw : Omega -> FiniteLaw (TripleSystemOn V) := fun omega =>
    starCappedLinkLaw (linkLaw omega) (caps omega) (hGood omega)
  intro heven hextension
  apply masterIterationGood_of_reserveAwareKernel_numeric_of_losses
    hU hreserve hcenter hout hleft hright hspokes
    (linkLaw := cappedLaw) (alpha := alpha / (1 - epsilon))
    (C' := C') (b' := b') (xi' := xi')
  · intro omega M hmass
    exact (hcapped omega M hmass).1
  · exact hC4capped
  · exact hnonempty
  · exact hkn
  · exact hCC'
  · exact hC'
  · exact herrorFactor
  · exact hbb'
  · exact hnew
  · exact heven
  · exact hold
  · exact hstate
  · exact hxixi'
  · intro omega M hmass _holdGood i hni v hv
    have hdata := hcapped omega M hmass
    have hpackingAll := hdata.1.1.2.2.1
    have hpacking : IsPackingOn (R omega ∪ M) := by
      apply hpackingAll.mono
      intro T hT
      rcases mem_union.mp hT with hTR | hTM
      · exact mem_union_left M <| mem_union_right (I omega) <|
          mem_union_right (D omega) hTR
      · exact mem_union_right (I omega ∪ (D omega ∪ R omega)) hTM
    have hnexti : next <= i.castSucc := by
      exact Fin.mk_le_mk.mpr hni
    exact nnreal_card_removedNeighbors_le_of_starCap
      (G omega) U (W.U i.castSucc) (R omega) M v
      (by simpa only [hU] using W.antitone next i.castSucc hnexti hv)
      (by simpa only [hU] using W.antitone next i.castSucc hnexti)
      hpacking (cap := caps omega v)
      (budget := (xi' - xi) * (p * (W.U i.castSucc).card))
      ((hdata.2 v)) (hdegreeBudgetSame omega i hni v hv)
  · intro omega M hmass _holdGood i hni v hv
    have hdata := hcapped omega M hmass
    have hpackingAll := hdata.1.1.2.2.1
    have hpacking : IsPackingOn (R omega ∪ M) := by
      apply hpackingAll.mono
      intro T hT
      rcases mem_union.mp hT with hTR | hTM
      · exact mem_union_left M <| mem_union_right (I omega) <|
          mem_union_right (D omega) hTR
      · exact mem_union_right (I omega ∪ (D omega ∪ R omega)) hTM
    have hnextCast : next <= i.castSucc := by
      exact Fin.mk_le_mk.mpr hni
    have hnextSucc : next <= i.succ := by
      apply le_trans hnextCast
      exact Fin.castSucc_le_succ i
    exact nnreal_card_removedNeighbors_le_of_starCap
      (G omega) U (W.U i.succ) (R omega) M v
      (by simpa only [hU] using W.antitone next i.castSucc hnextCast hv)
      (by simpa only [hU] using W.antitone next i.succ hnextSucc)
      hpacking (cap := caps omega v)
      (budget := (xi' - xi) * (p * (W.U i.succ).card))
      (hdata.2 v) (hdegreeBudgetNext omega i hni v hv)
  · exact hextension

end

end Erdos207
