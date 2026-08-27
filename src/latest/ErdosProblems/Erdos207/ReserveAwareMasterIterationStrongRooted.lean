/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveAwareMasterIterationCapsUpdate
import ErdosProblems.Erdos207.StrongRootedThreatProbability

/-!
# Rooted-active tails for a reserve-aware master step

The reserve-aware simultaneous-link update produces a strongly
well-distributed law for the enlarged selected system.  Substituting that
law into the rooted-configuration moment estimate removes the separately
postulated rooted-cap failure probability from the probabilistic part of a
master step.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The rooted-active cap failure probability after a reserve-aware
simultaneous-link step, expressed entirely in terms of the rooted extension
coefficient and the strong-distribution parameters. -/
theorem probability_reserveAwareKernel_not_rootedActiveCapsGood_le
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {ell : Nat} {law : FiniteLaw Omega}
    {linkLaw : Omega -> FiniteLaw (TripleSystemOn V)}
    {W : Vortex V ell} {k next : Fin (ell + 1)}
    {U : Finset V}
    {I D R : Omega -> TripleSystemOn V}
    {reserve : Omega -> Finset (Sym2 V)}
    {center : Omega -> ({x : V // x ∉ U} ↪ V)}
    {K : (omega : Omega) -> {x : V // x ∉ U} -> BipartiteLink V}
    {p reserveDensity C b alpha C' b' : NNReal}
    (hreserve : IsReserveStronglyWellDistributed law W k I
      (fun omega => D omega ∪ R omega) reserve p reserveDensity C b)
    (hcenter : ∀ omega o, (K omega o).center = center omega o)
    (hout : ∀ omega o, center omega o ∉ U)
    (hleft : ∀ omega o, (K omega o).left ⊆ U)
    (hright : ∀ omega o, (K omega o).right ⊆ U)
    (hspokes : ∀ omega o, (K omega o).SpokesIn (reserve omega))
    (hstruct : ∀ omega, (linkLaw omega).SupportedOn fun M =>
      IsSimultaneousLinkFamily (K omega) M ∧ IsPackingOn M)
    (hC4 : ∀ omega Q,
      (linkLaw omega).probability (fun M => Q ⊆ M) <= alpha ^ Q.card)
    (hnonempty : ∀ i, (W.U i).Nonempty)
    (hkn : k <= next) (hCC' : C <= C') (hC' : 1 <= C')
    (herrorFactor : alpha * C ^ 2 <= 1) (hbb' : b <= b')
    (hnew : ∀ T : TripleOn V,
      alpha * C ^ 2 * reserveDensity ^ 2 <=
        p / ((W.U (W.truncatedLevel next T)).card : NNReal))
    (F : ForbiddenFamilyOn V) (r : Nat) {q s : Nat}
    (hFcard : ∀ S ∈ F, S.card <= q)
    (hb : ∀ T : TripleSystemOn V, T.card <= s * (q - 1) ->
      b' <= setWeight (masterUnionTriangleWeight W next p) T)
    (kappa : NNReal)
    (hkappa : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 =>
          rootedThreatRemainder z)
        (masterUnionTriangleWeight W next p) kappa) :
    (law.jointBind linkLaw).probability (fun z =>
      ¬ RootedActiveCapsGood F
        (I z.1 ∪ (D z.1 ∪ (R z.1 ∪ z.2))) r) <=
      strongRootedTail V (2 * C') kappa r q s := by
  have hstrong :=
    stronglyWellDistributed_of_reserveAwareSimultaneousLinkKernel_numeric
      hreserve hcenter hout hleft hright hspokes hstruct hC4 hnonempty
        hkn hCC' hC' herrorFactor hbb' hnew
  exact hstrong.probability_not_rootedActiveCapsGood_le F r
    (by
      calc
        1 <= (2 : NNReal) := by norm_num
        _ <= 2 * C' := by
          simpa only [one_mul, mul_comm] using
            mul_le_mul_left hC' (2 : NNReal))
    hFcard hb kappa hkappa

/-- A complete probability-level reserve-aware master step.  Both cap
failures are now bounded from the kernel's C4 estimate and the updated
strong-distribution law; the remaining assumptions are deterministic scalar
budgets and the structural master-step certificates. -/
theorem masterIterationGood_of_reserveAwareKernel_strongRootedCaps
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
    {h a r q s : Nat}
    (caps : Omega -> V -> Nat)
    (epsilonStar : NNReal)
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
    (hFcard : ∀ S ∈ F, S.card <= q)
    (hbroot : ∀ T : TripleSystemOn V, T.card <= s * (q - 1) ->
      b' <= setWeight (masterUnionTriangleWeight W next p) T)
    (kappa : NNReal)
    (hkappa : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 =>
          rootedThreatRemainder z)
        (masterUnionTriangleWeight W next p) kappa)
    (hepsilon : epsilonStar +
      strongRootedTail V (2 * C') kappa r q s <= xi')
    (huniformStar : ∀ omega v,
      2 * ((triplesThrough (R omega) v).card + caps omega v) <= a)
    (hdegreeBudgetSame : ∀ omega (i : Fin ell), next.val <= i.val ->
      ∀ v ∈ W.U i.castSucc,
        (2 : NNReal) *
            ((triplesThrough (R omega) v).card + caps omega v) <=
          (xi' - xi) * (p * (W.U i.castSucc).card))
    (hdegreeBudgetNext : ∀ omega (i : Fin ell), next.val <= i.val ->
      ∀ v ∈ W.U i.castSucc,
        (2 : NNReal) *
            ((triplesThrough (R omega) v).card + caps omega v) <=
          (xi' - xi) * (p * (W.U i.succ).card))
    (hextensionBudget : ∀ omega M (i : Fin ell), next.val <= i.val ->
      ∀ iStar : Fin (ell + 1),
        (iStar = i.castSucc ∨ iStar = i.succ) ->
      ∀ Q : SimpleGraph V,
        Q <= updatedStageGraph (G omega) (W.U next) (R omega ∪ M) ->
        GraphSupportedOn Q (W.U i.castSucc : Set V) ->
        (graphSupportFinset Q).card <= h ->
      ((graphSupportFinset Q).card : NNReal) +
          (graphSupportFinset Q).card * a +
            (graphEdges Q).card * (r * q) <=
        (xi' - xi) *
          (p ^ (graphSupportFinset Q).card *
            eta ^ (graphEdges Q).card * (W.U iStar).card)) :
    IsMasterIterationGood (law.jointBind linkLaw) W next F
      (fun z => updatedStageGraph (G z.1) U (R z.1 ∪ z.2))
      (fun z => updatedStageAvailable F U (A z.1) (I z.1) (D z.1)
        (R z.1 ∪ z.2))
      (fun z => I z.1) (fun z => D z.1 ∪ (R z.1 ∪ z.2))
      p eta xi' (2 * C') b' h := by
  have hstruct : ∀ omega, (linkLaw omega).SupportedOn fun M =>
      IsSimultaneousLinkFamily (K omega) M ∧ IsPackingOn M := by
    intro omega M hmass
    have hM := hlink omega M hmass
    exact ⟨hM.2, hM.1.isPacking⟩
  have hrootBad : (law.jointBind linkLaw).probability (fun z =>
      ¬ RootedActiveCapsGood F
        (I z.1 ∪ (D z.1 ∪ (R z.1 ∪ z.2))) r) <=
      strongRootedTail V (2 * C') kappa r q s := by
    exact probability_reserveAwareKernel_not_rootedActiveCapsGood_le
      hreserve hcenter hout hleft hright hspokes hstruct hC4 hnonempty
        hkn hCC' hC' herrorFactor hbb' hnew F r hFcard hbroot kappa hkappa
  exact masterIterationGood_of_reserveAwareKernel_caps caps epsilonStar
    (strongRootedTail V (2 * C') kappa r q s) hU hreserve hcenter hout
    hleft hright hspokes hlink hC4 htail hrootBad hnonempty hkn hCC' hC'
    herrorFactor hbb' hnew heven hold hstate hxixi' hepsilon hFcard
    huniformStar hdegreeBudgetSame hdegreeBudgetNext hextensionBudget

end

end Erdos207
