/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveAwareMasterIterationStrongRooted
import ErdosProblems.Erdos207.SupportedLinkCoverKernel

/-!
# Reserve-aware master iteration from a support-restricted cover kernel

The robust matching theorem produces a simultaneous-cover law only at old
states of positive mass.  Outside that support the kernel may be totalized by
the deterministic empty law.  Strong-distribution accounting needs the
structural and C4 conclusions on every fiber, whereas the deterministic
master-cover conclusion is needed only on the support of the joint law.

This file records precisely that support-sensitive form of the one-step
master theorem.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- An old-state certificate and simultaneous-cover support for the joint law
give the deterministic master-cover certificate on joint support. -/
theorem FiniteLaw.SupportedOn.jointBind_masterCoverStep_of_jointLink
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {law : FiniteLaw Omega}
    {linkLaw : Omega -> FiniteLaw (TripleSystemOn V)}
    {F : ForbiddenFamilyOn V} {U : Finset V}
    {G : Omega -> SimpleGraph V}
    {A I D R : Omega -> TripleSystemOn V}
    {K : (omega : Omega) -> {x : V // x ∉ U} -> BipartiteLink V}
    (hstate : law.SupportedOn fun omega =>
      IsIntermediateLinkState (G omega) U (A omega) (I omega) (D omega)
        (R omega) (K omega))
    (hlink : (law.jointBind linkLaw).SupportedOn fun z =>
      IsSimultaneousLinkCover F (A z.1)
        (I z.1 ∪ (D z.1 ∪ R z.1)) (K z.1) z.2) :
    (law.jointBind linkLaw).SupportedOn fun z =>
      IsMasterCoverStep F (G z.1) U (A z.1) (I z.1) (D z.1)
        (R z.1 ∪ z.2) := by
  have hstateJoint := hstate.jointBind (K := linkLaw)
    (Q := fun _omega _M => True)
    (fun _omega _hstate => by intro _M _hmass; trivial)
  intro z hz
  have hzstate := (hstateJoint z hz).1
  have hzlink := hlink z hz
  let : DecidableRel (G z.1).Adj := Classical.decRel (G z.1).Adj
  exact hzlink.isMasterCoverStep hzstate.1 hzstate.2.1 hzstate.2.2

/-- Probability-level reserve-aware master update when cover validity is
available exactly on the support of the joint law. -/
theorem masterIterationGood_of_reserveAwareKernel_probability_supported
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
    {p reserveDensity C b alpha C' b' eta xi xi' : NNReal} {h : Nat}
    (hU : U = W.U next)
    (hreserve : IsReserveStronglyWellDistributed law W k I
      (fun omega => D omega ∪ R omega) reserve p reserveDensity C b)
    (hcenter : ∀ omega o, (K omega o).center = center omega o)
    (hout : ∀ omega o, center omega o ∉ U)
    (hleft : ∀ omega o, (K omega o).left ⊆ U)
    (hright : ∀ omega o, (K omega o).right ⊆ U)
    (hspokes : ∀ omega o, (K omega o).SpokesIn (reserve omega))
    (hstruct : ∀ omega, (linkLaw omega).SupportedOn fun M =>
      IsSimultaneousLinkFamily (K omega) M ∧ IsPackingOn M)
    (hlink : (law.jointBind linkLaw).SupportedOn fun z =>
      IsSimultaneousLinkCover F (A z.1)
          (I z.1 ∪ (D z.1 ∪ R z.1)) (K z.1) z.2 ∧
        IsSimultaneousLinkFamily (K z.1) z.2)
    (hC4 : ∀ omega Q,
      (linkLaw omega).probability (fun M => Q ⊆ M) <= alpha ^ Q.card)
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
    (hloss : 1 - xi' <= (law.jointBind linkLaw).probability (fun z =>
      MasterTypicalityLossEvent W next F (G z.1) (A z.1)
        (I z.1) (D z.1) (R z.1 ∪ z.2) p eta xi xi' h)) :
    IsMasterIterationGood (law.jointBind linkLaw) W next F
      (fun z => updatedStageGraph (G z.1) U (R z.1 ∪ z.2))
      (fun z => updatedStageAvailable F U (A z.1) (I z.1) (D z.1)
        (R z.1 ∪ z.2))
      (fun z => I z.1) (fun z => D z.1 ∪ (R z.1 ∪ z.2))
      p eta xi' (2 * C') b' h := by
  have hstrong : IsStronglyWellDistributed (law.jointBind linkLaw) W next
      (fun z => I z.1) (fun z => D z.1 ∪ (R z.1 ∪ z.2))
      p (2 * C') b' := by
    have hbase := hreserve.jointBind_simultaneousLink_of_numeric hcenter hout
      hleft hright hspokes hstruct hC4 hnonempty hkn hCC' hC' le_rfl
        herrorFactor hbb' hnew
    have hInitial : jointInitial I =
        (fun z : Omega × TripleSystemOn V => I z.1) := rfl
    have hLater :
        jointLater (fun omega => D omega ∪ R omega) (fun _omega M => M) =
          (fun z : Omega × TripleSystemOn V =>
            D z.1 ∪ (R z.1 ∪ z.2)) := by
      funext z
      simp only [jointLater, union_assoc]
    rw [hInitial, hLater] at hbase
    exact hbase
  have holdJoint : (law.jointBind linkLaw).SupportedOn fun z =>
      IsMasterStagePointwiseGood W k F (G z.1) (A z.1)
        (I z.1) (D z.1) p eta xi h := by
    have hbind := hold.jointBind (K := linkLaw)
      (Q := fun _omega _M => True)
      (fun _omega _hold => by intro _M _hmass; trivial)
    exact fun z hz => (hbind z hz).1
  have hstep : (law.jointBind linkLaw).SupportedOn fun z =>
      IsMasterCoverStep F (G z.1) U (A z.1) (I z.1) (D z.1)
        (R z.1 ∪ z.2) :=
    hstate.jointBind_masterCoverStep_of_jointLink
      (fun z hz => (hlink z hz).1)
  have holdTypical : (law.jointBind linkLaw).SupportedOn fun z =>
      IsIterationTypical W k (G z.1) (A z.1) p eta xi h := by
    intro z hz
    exact (holdJoint z hz).2.2.2.1
  have htypProbability : 1 - xi' <=
      (law.jointBind linkLaw).probability (fun z =>
        IsIterationTypical W next
          (updatedStageGraph (G z.1) (W.U next) (R z.1 ∪ z.2))
          (updatedStageAvailable F (W.U next) (A z.1) (I z.1) (D z.1)
            (R z.1 ∪ z.2)) p eta xi' h) :=
    hloss.trans <|
      (law.jointBind linkLaw).probability_masterTypicalityLossEvent_le_updatedTypical
        W k next F (fun z => G z.1) (fun z => A z.1)
          (fun z => I z.1) (fun z => D z.1)
          (fun z => R z.1 ∪ z.2) p eta xi xi' h hkn
          hxixi' holdTypical
  subst U
  apply masterIterationGood_of_probability_update heven hstrong holdJoint
    (by simpa using hstep) htypProbability

/-- Cap form of the support-sensitive reserve-aware master update. -/
theorem masterIterationGood_of_reserveAwareKernel_caps_supported
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
    (hstruct : ∀ omega, (linkLaw omega).SupportedOn fun M =>
      IsSimultaneousLinkFamily (K omega) M ∧ IsPackingOn M)
    (hlink : (law.jointBind linkLaw).SupportedOn fun z =>
      IsSimultaneousLinkCover F (A z.1)
          (I z.1 ∪ (D z.1 ∪ R z.1)) (K z.1) z.2 ∧
        IsSimultaneousLinkFamily (K z.1) z.2)
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
    hstate.jointBind_masterCoverStep_of_jointLink
      (fun z hz => (hlink z hz).1)
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
  exact masterIterationGood_of_reserveAwareKernel_probability_supported
    hU hreserve hcenter hout hleft hright hspokes hstruct hlink hC4
    hnonempty hkn hCC' hC' herrorFactor hbb' hnew heven hold hstate
    hxixi' hloss

/-- Complete support-sensitive master step with rooted-cap probability
derived from the updated strong-distribution law. -/
theorem masterIterationGood_of_reserveAwareKernel_strongRootedCaps_supported
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
    (hstruct : ∀ omega, (linkLaw omega).SupportedOn fun M =>
      IsSimultaneousLinkFamily (K omega) M ∧ IsPackingOn M)
    (hlink : (law.jointBind linkLaw).SupportedOn fun z =>
      IsSimultaneousLinkCover F (A z.1)
          (I z.1 ∪ (D z.1 ∪ R z.1)) (K z.1) z.2 ∧
        IsSimultaneousLinkFamily (K z.1) z.2)
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
  have hrootBad : (law.jointBind linkLaw).probability (fun z =>
      ¬ RootedActiveCapsGood F
        (I z.1 ∪ (D z.1 ∪ (R z.1 ∪ z.2))) r) <=
      strongRootedTail V (2 * C') kappa r q s := by
    exact probability_reserveAwareKernel_not_rootedActiveCapsGood_le
      hreserve hcenter hout hleft hright hspokes hstruct hC4 hnonempty
        hkn hCC' hC' herrorFactor hbb' hnew F r hFcard hbroot kappa hkappa
  exact masterIterationGood_of_reserveAwareKernel_caps_supported caps
    epsilonStar (strongRootedTail V (2 * C') kappa r q s) hU hreserve
    hcenter hout hleft hright hspokes hstruct hlink hC4 htail hrootBad
    hnonempty hkn hCC' hC' herrorFactor hbb' hnew heven hold hstate
    hxixi' hepsilon hFcard huniformStar hdegreeBudgetSame hdegreeBudgetNext
    hextensionBudget

end

end Erdos207
