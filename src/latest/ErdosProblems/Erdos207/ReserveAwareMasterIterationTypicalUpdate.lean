/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveAwareMasterIterationUpdate
import ErdosProblems.Erdos207.MasterTypicalityUpdate

/-!
# Reserve-aware master update from explicit typicality losses

The preceding master theorem accepted next-stage typicality as a support
hypothesis.  This version derives it from the two concrete loss estimates
that correspond to KSSS T1--T3.  Consequently its remaining probabilistic
inputs expose exactly what must be bounded for every supported link outcome.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem masterIterationGood_of_reserveAwareKernel_numeric_of_losses
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {ell : ℕ} {law : FiniteLaw Omega}
    {linkLaw : Omega → FiniteLaw (TripleSystemOn V)}
    {W : Vortex V ell} {k next : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {U : Finset V}
    {G : Omega → SimpleGraph V}
    {A I D R : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {center : Omega → ({x : V // x ∉ U} ↪ V)}
    {K : (omega : Omega) → {x : V // x ∉ U} → BipartiteLink V}
    {p reserveDensity C b alpha C' b' eta xi xi' : ℝ≥0} {h : ℕ}
    (hU : U = W.U next)
    (hreserve : IsReserveStronglyWellDistributed law W k I
      (fun omega ↦ D omega ∪ R omega) reserve p reserveDensity C b)
    (hcenter : ∀ omega o, (K omega o).center = center omega o)
    (hout : ∀ omega o, center omega o ∉ U)
    (hleft : ∀ omega o, (K omega o).left ⊆ U)
    (hright : ∀ omega o, (K omega o).right ⊆ U)
    (hspokes : ∀ omega o, (K omega o).SpokesIn (reserve omega))
    (hlink : ∀ omega, (linkLaw omega).SupportedOn fun M ↦
      IsSimultaneousLinkCover F (A omega)
          (I omega ∪ (D omega ∪ R omega)) (K omega) M ∧
        IsSimultaneousLinkFamily (K omega) M)
    (hC4 : ∀ omega Q,
      (linkLaw omega).probability (fun M ↦ Q ⊆ M) ≤ alpha ^ Q.card)
    (hnonempty : ∀ i, (W.U i).Nonempty)
    (hkn : k ≤ next) (hCC' : C ≤ C') (hC' : 1 ≤ C')
    (herrorFactor : alpha * C ^ 2 ≤ 1) (hbb' : b ≤ b')
    (hnew : ∀ T : TripleOn V,
      alpha * C ^ 2 * reserveDensity ^ 2 ≤
        p / ((W.U (W.truncatedLevel next T)).card : ℝ≥0))
    (heven : HasEvenStageGraphs (law.jointBind linkLaw)
      (fun z ↦ updatedStageGraph (G z.1) U (R z.1 ∪ z.2)))
    (hold : law.SupportedOn fun omega ↦
      IsMasterStagePointwiseGood W k F (G omega) (A omega)
        (I omega) (D omega) p eta xi h)
    (hstate : law.SupportedOn fun omega ↦
      IsIntermediateLinkState (G omega) U (A omega) (I omega) (D omega)
        (R omega) (K omega))
    (hxixi' : xi ≤ xi')
    (hdegreeSame : ∀ omega M,
      0 < (linkLaw omega).mass M →
      IsMasterStagePointwiseGood W k F (G omega) (A omega)
        (I omega) (D omega) p eta xi h →
      ∀ i : Fin ell, next.val ≤ i.val →
      ∀ v ∈ W.U i.castSucc,
      (((neighborsIn (G omega) (W.U i.castSucc) v) \
          neighborsIn (updatedStageGraph (G omega) U (R omega ∪ M))
            (W.U i.castSucc) v).card : ℝ≥0) ≤
        (xi' - xi) * (p * (W.U i.castSucc).card))
    (hdegreeNext : ∀ omega M,
      0 < (linkLaw omega).mass M →
      IsMasterStagePointwiseGood W k F (G omega) (A omega)
        (I omega) (D omega) p eta xi h →
      ∀ i : Fin ell, next.val ≤ i.val →
      ∀ v ∈ W.U i.castSucc,
      (((neighborsIn (G omega) (W.U i.succ) v) \
          neighborsIn (updatedStageGraph (G omega) U (R omega ∪ M))
            (W.U i.succ) v).card : ℝ≥0) ≤
        (xi' - xi) * (p * (W.U i.succ).card))
    (hextension : ∀ omega M,
      0 < (linkLaw omega).mass M →
      IsMasterStagePointwiseGood W k F (G omega) (A omega)
        (I omega) (D omega) p eta xi h →
      ∀ i : Fin ell, next.val ≤ i.val →
      ∀ iStar : Fin (ell + 1),
        (iStar = i.castSucc ∨ iStar = i.succ) →
      ∀ Q : SimpleGraph V,
        Q ≤ updatedStageGraph (G omega) U (R omega ∪ M) →
        GraphSupportedOn Q (W.U i.castSucc : Set V) →
        (graphSupportFinset Q).card ≤ h →
      (((iterationExtensionVertices (A omega) Q (W.U iStar)) \
          iterationExtensionVertices
            (updatedStageAvailable F U (A omega) (I omega) (D omega)
              (R omega ∪ M)) Q (W.U iStar)).card : ℝ≥0) ≤
        (xi' - xi) *
          (p ^ (graphSupportFinset Q).card *
            eta ^ (graphEdges Q).card * (W.U iStar).card)) :
    IsMasterIterationGood (law.jointBind linkLaw) W next F
      (fun z ↦ updatedStageGraph (G z.1) U (R z.1 ∪ z.2))
      (fun z ↦ updatedStageAvailable F U (A z.1) (I z.1) (D z.1)
        (R z.1 ∪ z.2))
      (fun z ↦ I z.1) (fun z ↦ D z.1 ∪ (R z.1 ∪ z.2))
      p eta xi' (2 * C') b' h := by
  have hmass : (law.jointBind linkLaw).SupportedOn fun z ↦
      IsMasterStagePointwiseGood W k F (G z.1) (A z.1)
          (I z.1) (D z.1) p eta xi h ∧
        0 < (linkLaw z.1).mass z.2 := by
    exact hold.jointBind
      (K := linkLaw)
      (Q := fun omega M ↦ 0 < (linkLaw omega).mass M)
      (fun _omega _hold ↦ by
        intro _M hM
        exact hM)
  have htyp : (law.jointBind linkLaw).SupportedOn fun z ↦
      IsIterationTypical W next
        (updatedStageGraph (G z.1) U (R z.1 ∪ z.2))
        (updatedStageAvailable F U (A z.1) (I z.1) (D z.1)
          (R z.1 ∪ z.2)) p eta xi' h := by
    intro z hz
    have hzdata := hmass z hz
    have holdtyp := hzdata.1.2.2.2.1
    rw [hU]
    apply holdtyp.updatedStage_of_loss hkn hxixi'
    · simpa only [hU] using
        hdegreeSame z.1 z.2 hzdata.2 hzdata.1
    · simpa only [hU] using
        hdegreeNext z.1 z.2 hzdata.2 hzdata.1
    · simpa only [hU] using
        hextension z.1 z.2 hzdata.2 hzdata.1
  apply masterIterationGood_of_reserveAwareSimultaneousLinkKernel_numeric
    hU hreserve hcenter hout hleft hright hspokes hlink hC4 hnonempty
      hkn hCC' hC' herrorFactor hbb' hnew heven hold hstate htyp

end

end Erdos207
