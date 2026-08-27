/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveAwareMasterIterationProbabilityUpdate
import ErdosProblems.Erdos207.MasterTypicalityLossProbability

/-!
# Reserve-aware master update from explicit star and rooted caps

This is the probability-level one-step endpoint.  The C4 estimate supplies
the selected-star tail, the caller supplies the rooted-active tail, and the
deterministic cap theorem supplies all three typicality loss clauses.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

theorem masterIterationGood_of_reserveAwareKernel_caps
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
    {p reserveDensity C b alpha C' b' eta xi xi' : NNReal}
    {h a r q : Nat}
    (caps : Omega -> V -> Nat)
    (epsilonStar epsilonRoot : NNReal)
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
        alpha ^ caps omega v <= epsilonStar)
    (hrootBad : (law.jointBind linkLaw).probability (fun z =>
      ¬ RootedActiveCapsGood F
        (I z.1 ∪ (D z.1 ∪ (R z.1 ∪ z.2))) r) <= epsilonRoot)
    (hnonempty : ∀ i, (W.U i).Nonempty)
    (hkn : k <= next) (hCC' : C <= C') (hC' : 1 <= C')
    (herrorFactor : alpha * C ^ 2 <= 1) (hbb' : b <= b')
    (hnew : ∀ T : TripleOn V,
      alpha * C ^ 2 * reserveDensity ^ 2 <=
        p / ((W.U (W.truncatedLevel next T)).card : NNReal))
    (heven : HasEvenStageGraphs (law.jointBind linkLaw)
      (fun z => updatedStageGraph (G z.1) U (R z.1 ∪ z.2)))
    (hold : law.SupportedOn fun omega =>
      IsMasterStagePointwiseGood W k F (G omega) (A omega)
        (I omega) (D omega) p eta xi h)
    (hstate : law.SupportedOn fun omega =>
      IsIntermediateLinkState (G omega) U (A omega) (I omega) (D omega)
        (R omega) (K omega))
    (hxixi' : xi <= xi')
    (hepsilon : epsilonStar + epsilonRoot <= xi')
    (hFcard : ∀ S ∈ F, S.card ≤ q)
    (huniformStar : ∀ omega v,
      2 * ((triplesThrough (R omega) v).card + caps omega v) ≤ a)
    (hdegreeBudgetSame : ∀ omega (i : Fin ell), next.val ≤ i.val →
      ∀ v ∈ W.U i.castSucc,
        (2 : NNReal) *
            ((triplesThrough (R omega) v).card + caps omega v) ≤
          (xi' - xi) * (p * (W.U i.castSucc).card))
    (hdegreeBudgetNext : ∀ omega (i : Fin ell), next.val ≤ i.val →
      ∀ v ∈ W.U i.castSucc,
        (2 : NNReal) *
            ((triplesThrough (R omega) v).card + caps omega v) ≤
          (xi' - xi) * (p * (W.U i.succ).card))
    (hextensionBudget : ∀ omega M (i : Fin ell), next.val ≤ i.val →
      ∀ iStar : Fin (ell + 1),
        (iStar = i.castSucc ∨ iStar = i.succ) →
      ∀ Q : SimpleGraph V,
        Q ≤ updatedStageGraph (G omega) (W.U next) (R omega ∪ M) →
        GraphSupportedOn Q (W.U i.castSucc : Set V) →
        (graphSupportFinset Q).card ≤ h →
      ((graphSupportFinset Q).card : NNReal) +
          (graphSupportFinset Q).card * a +
            (graphEdges Q).card * (r * q) ≤
        (xi' - xi) *
          (p ^ (graphSupportFinset Q).card *
            eta ^ (graphEdges Q).card * (W.U iStar).card)) :
    IsMasterIterationGood (law.jointBind linkLaw) W next F
      (fun z => updatedStageGraph (G z.1) U (R z.1 ∪ z.2))
      (fun z => updatedStageAvailable F U (A z.1) (I z.1) (D z.1)
        (R z.1 ∪ z.2))
      (fun z => I z.1) (fun z => D z.1 ∪ (R z.1 ∪ z.2))
      p eta xi' (2 * C') b' h := by
  let J := law.jointBind linkLaw
  have holdJoint : J.SupportedOn fun z =>
      IsMasterStagePointwiseGood W k F (G z.1) (A z.1)
        (I z.1) (D z.1) p eta xi h := by
    have hbind := hold.jointBind (K := linkLaw)
      (Q := fun _omega _M => True)
      (fun _omega _hold => by intro _M _hmass; trivial)
    exact fun z hz => (hbind z hz).1
  have hstep : J.SupportedOn fun z =>
      IsMasterCoverStep F (G z.1) U (A z.1) (I z.1) (D z.1)
        (R z.1 ∪ z.2) :=
    hstate.jointBind_masterCoverStep
      (fun omega M hmass => (hlink omega M hmass).1)
  have hstarBad : J.probability (fun z =>
      ¬ LinkStarCapsGood (caps z.1) z.2) <= epsilonStar :=
    probability_jointBind_not_linkStarCapsGood_le law linkLaw caps
      alpha epsilonStar hC4 htail
  have hloss0 : 1 - (epsilonStar + epsilonRoot) <=
      J.probability (fun z =>
        MasterTypicalityLossEvent W next F (G z.1) (A z.1)
          (I z.1) (D z.1) (R z.1 ∪ z.2) p eta xi xi' h) := by
    subst U
    exact probability_masterTypicalityLossEvent_of_caps J W k next F
      (fun z => G z.1) (fun z => A z.1) (fun z => I z.1)
      (fun z => D z.1) (fun z => R z.1) (fun z => z.2)
      p eta xi xi' h a r q (fun z => caps z.1)
      epsilonStar epsilonRoot holdJoint hstep hstarBad hrootBad hFcard
      (fun z => huniformStar z.1)
      (fun z => hdegreeBudgetSame z.1)
      (fun z => hdegreeBudgetNext z.1)
      (fun z => hextensionBudget z.1 z.2)
  have hloss : 1 - xi' <= J.probability (fun z =>
      MasterTypicalityLossEvent W next F (G z.1) (A z.1)
        (I z.1) (D z.1) (R z.1 ∪ z.2) p eta xi xi' h) := by
    exact (tsub_le_tsub_left hepsilon 1).trans hloss0
  exact masterIterationGood_of_reserveAwareKernel_probability
    hU hreserve hcenter hout hleft hright hspokes hlink hC4 hnonempty
    hkn hCC' hC' herrorFactor hbb' hnew heven hold hstate hxixi' hloss

end

end Erdos207
