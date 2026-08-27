/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveAwareMasterIterationUpdate
import ErdosProblems.Erdos207.MasterTypicalityUpdate

/-!
# Probability-level reserve-aware master update

The reserve/link calculation gives the new strong-distribution law on the
whole support.  Next-stage typicality is supplied at its natural KSSS
probability level by the common T1--T3 loss event.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem masterIterationGood_of_reserveAwareKernel_probability
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
    (hlink : ∀ omega, (linkLaw omega).SupportedOn fun M =>
      IsSimultaneousLinkCover F (A omega)
          (I omega ∪ (D omega ∪ R omega)) (K omega) M ∧
        IsSimultaneousLinkFamily (K omega) M)
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
  have hstruct : ∀ omega, (linkLaw omega).SupportedOn fun M =>
      IsSimultaneousLinkFamily (K omega) M ∧ IsPackingOn M := by
    intro omega M hmass
    have hM := hlink omega M hmass
    exact ⟨hM.2, hM.1.2.2.1.mono subset_union_right⟩
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
    hstate.jointBind_masterCoverStep
      (fun omega M hmass => (hlink omega M hmass).1)
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

end

end Erdos207
