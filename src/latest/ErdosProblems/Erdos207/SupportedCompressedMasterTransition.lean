/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CompressedReserveAwareMasterStep
import ErdosProblems.Erdos207.TypicalRobustLinkReadiness

/-!
# A supported robust-link transition to a compressed master law

Readiness of the robust simultaneous-link law is only needed on positive-mass
intermediate states.  The supported kernel supplies harmless empty fallback
fibers, its global C4 estimate, and structural reserve accounting.  This file
feeds those facts directly into the compressed reserve-aware master step.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Supportwise robust-link readiness supplies the complete compressed
master transition. -/
theorem compressedMasterStep_of_supportedRobustLinkReadiness
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {ell : Nat} {law : FiniteLaw Omega}
    {W : Vortex V ell} {weightStage pointStage next : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {U : Finset V}
    {G : Omega → SimpleGraph V}
    {A I D R initial later : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {K : (omega : Omega) → {x : V // x ∉ U} → BipartiteLink V}
    {Gzero : SimpleGraph V} {ambient : TripleSystemOn V}
    {p reserveDensity C b alpha C' b' eta xi xi' : NNReal}
    {h a r q s : Nat}
    (caps : Omega → V → Nat)
    (epsilonStar : NNReal)
    (hU : U = W.U next)
    (hreserve : IsReserveStronglyWellDistributed law W weightStage initial later
      reserve p reserveDensity C b)
    (hclassification : law.SupportedOn fun omega =>
      Disjoint (initial omega) (later omega) ∧
        initial omega ∪ later omega =
          I omega ∪ (D omega ∪ R omega))
    (hcenter : ∀ omega o,
      (K omega o).center = outsideVertexEmbedding U o)
    (hout : ∀ (_omega : Omega) o, outsideVertexEmbedding U o ∉ U)
    (hleft : ∀ omega o, (K omega o).left ⊆ U)
    (hright : ∀ omega o, (K omega o).right ⊆ U)
    (hspokes : ∀ omega o, (K omega o).SpokesIn (reserve omega))
    (hready : law.SupportedOn fun omega =>
      HasSimultaneousLinkCoverFamilyLaw F (A omega)
        (I omega ∪ (D omega ∪ R omega)) (K omega) alpha)
    (htail : ∀ omega, ∑ v : V,
      ((ambientTriplesThrough v).powersetCard (caps omega v)).card *
        alpha ^ caps omega v <= epsilonStar)
    (hnonempty : ∀ i, (W.U i).Nonempty)
    (hweightNext : weightStage <= next)
    (hCC' : C <= C') (hC' : 1 <= C')
    (herrorFactor : alpha * C ^ 2 <= 1) (hbb' : b <= b')
    (hnew : ∀ T : TripleOn V,
      alpha * C ^ 2 * reserveDensity ^ 2 <=
        p / ((W.U (W.truncatedLevel next T)).card : NNReal))
    (heven : HasEvenStageGraphs
      (law.jointBind (supportedSimultaneousLinkCoverKernel F A
        (fun omega => I omega ∪ (D omega ∪ R omega)) K alpha))
      (fun z => updatedStageGraph (G z.1) U (R z.1 ∪ z.2)))
    (hold : law.SupportedOn fun omega =>
      IsMasterStagePointwiseGood W pointStage F (G omega) (A omega)
        (I omega) (D omega) p eta xi h)
    (hpointNext : pointStage <= next)
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
            eta ^ (graphEdges Q).card * (W.U iStar).card))
    (havailable : law.SupportedOn fun omega => A omega ⊆ ambient)
    (hselected : law.SupportedOn fun omega =>
      I omega ∪ D omega ⊆ ambient)
    (hcover : law.SupportedOn fun omega =>
      CoversOriginalGraph Gzero (G omega) (I omega) (D omega))
    (hsub : law.SupportedOn fun omega => G omega ≤ Gzero) :
    let linkLaw := supportedSimultaneousLinkCoverKernel F A
      (fun omega => I omega ∪ (D omega ∪ R omega)) K alpha
    IsCompressedMasterLaw
      ((law.jointBind linkLaw).map (packMasterState
        (fun z => updatedStageGraph (G z.1) (W.U next)
          (R z.1 ∪ z.2))
        (fun z => updatedStageAvailable F (W.U next)
          (A z.1) (I z.1) (D z.1) (R z.1 ∪ z.2))
        (fun z => initial z.1)
        (fun z => later z.1 ∪ z.2)))
      W next F Gzero ambient p eta xi' (2 * C') b' h := by
  dsimp only
  let P : Omega → TripleSystemOn V := fun omega =>
    I omega ∪ (D omega ∪ R omega)
  let linkLaw := supportedSimultaneousLinkCoverKernel F A P K alpha
  have hstruct : ∀ omega, (linkLaw omega).SupportedOn fun M =>
      IsSimultaneousLinkFamily (K omega) M ∧ IsPackingOn M := by
    intro omega
    exact supportedSimultaneousLinkCoverKernel_structural F A P K alpha omega
  have hlink : (law.jointBind linkLaw).SupportedOn fun z =>
      IsSimultaneousLinkCover F (A z.1) (P z.1) (K z.1) z.2 ∧
        IsSimultaneousLinkFamily (K z.1) z.2 := by
    exact hready.jointBind_supportedSimultaneousLinkCoverKernel
      F A P K alpha
  have hC4 : ∀ omega Q,
      (linkLaw omega).probability (fun M => Q ⊆ M) <= alpha ^ Q.card := by
    intro omega Q
    exact supportedSimultaneousLinkCoverKernel_C4 F A P K alpha omega Q
  let J := law.jointBind linkLaw
  have hstrongBase := hreserve.jointBind_simultaneousLink_of_numeric
    hcenter hout hleft hright hspokes hstruct hC4 hnonempty hweightNext hCC' hC'
      le_rfl herrorFactor hbb' hnew
  have hstrong : IsStronglyWellDistributed J W next
      (fun z => initial z.1) (fun z => later z.1 ∪ z.2)
      p (2 * C') b' := by
    change IsStronglyWellDistributed J W next
      (fun z => initial z.1) (fun z => later z.1 ∪ z.2)
      p (2 * C') b' at hstrongBase
    exact hstrongBase
  have hrootClassified : J.probability (fun z =>
      ¬ RootedActiveCapsGood F
        (initial z.1 ∪ (later z.1 ∪ z.2)) r) <=
      strongRootedTail V (2 * C') kappa r q s := by
    exact hstrong.probability_not_rootedActiveCapsGood_le F r
      (by
        calc
          1 <= (2 : NNReal) := by norm_num
          _ <= 2 * C' := by
            simpa only [one_mul, mul_comm] using
              mul_le_mul_left hC' (2 : NNReal))
      hFcard hbroot kappa hkappa
  have hclassificationJoint : J.SupportedOn fun z =>
      Disjoint (initial z.1) (later z.1) ∧
        initial z.1 ∪ later z.1 =
          I z.1 ∪ (D z.1 ∪ R z.1) := by
    have hbind := hclassification.jointBind (K := linkLaw)
      (Q := fun _omega _M => True)
      (fun _omega _hclassification => by intro _M _hmass; trivial)
    exact fun z hz => (hbind z hz).1
  have hrootBad : J.probability (fun z =>
      ¬ RootedActiveCapsGood F
        (I z.1 ∪ (D z.1 ∪ (R z.1 ∪ z.2))) r) <=
      strongRootedTail V (2 * C') kappa r q s := by
    exact (J.probability_mono_of_supported hclassificationJoint
      (fun z hz hbad => by
        have hunion : initial z.1 ∪ (later z.1 ∪ z.2) =
            I z.1 ∪ (D z.1 ∪ (R z.1 ∪ z.2)) := by
          simpa only [union_assoc] using
            congrArg (fun S : TripleSystemOn V => S ∪ z.2) hz.2
        simpa only [hunion] using hbad)).trans hrootClassified
  have holdJoint : J.SupportedOn fun z =>
      IsMasterStagePointwiseGood W pointStage F (G z.1) (A z.1)
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
  have hloss0 : 1 - (epsilonStar +
      strongRootedTail V (2 * C') kappa r q s) <=
      J.probability (fun z =>
        MasterTypicalityLossEvent W next F (G z.1) (A z.1)
          (I z.1) (D z.1) (R z.1 ∪ z.2) p eta xi xi' h) := by
    exact probability_masterTypicalityLossEvent_of_caps J W pointStage next F
      (fun z => G z.1) (fun z => A z.1) (fun z => I z.1)
      (fun z => D z.1) (fun z => R z.1) (fun z => z.2)
      p eta xi xi' h a r q (fun z => caps z.1)
      epsilonStar (strongRootedTail V (2 * C') kappa r q s)
      holdJoint (by simpa only [hU] using hstep) hstarBad hrootBad hFcard
      (fun z => huniformStar z.1)
      (fun z => hdegreeBudgetSame z.1)
      (fun z => hdegreeBudgetNext z.1)
      (fun z => hextensionBudget z.1 z.2)
  have hloss : 1 - xi' <= J.probability (fun z =>
      MasterTypicalityLossEvent W next F (G z.1) (A z.1)
        (I z.1) (D z.1) (R z.1 ∪ z.2) p eta xi xi' h) :=
    (tsub_le_tsub_left hepsilon 1).trans hloss0
  have holdTypical : J.SupportedOn fun z =>
      IsIterationTypical W pointStage (G z.1) (A z.1) p eta xi h := by
    intro z hz
    exact (holdJoint z hz).2.2.2.1
  have htypProbability : 1 - xi' <= J.probability (fun z =>
      IsIterationTypical W next
        (updatedStageGraph (G z.1) (W.U next) (R z.1 ∪ z.2))
        (updatedStageAvailable F (W.U next) (A z.1)
          (I z.1) (D z.1) (R z.1 ∪ z.2)) p eta xi' h) :=
    hloss.trans <|
      J.probability_masterTypicalityLossEvent_le_updatedTypical
        W pointStage next F (fun z => G z.1) (fun z => A z.1)
          (fun z => I z.1) (fun z => D z.1)
          (fun z => R z.1 ∪ z.2) p eta xi xi' h hpointNext
          hxixi' holdTypical
  have hsupportAll : J.SupportedOn fun z =>
      IsMasterStagePointwiseGood W pointStage F (G z.1) (A z.1)
          (I z.1) (D z.1) p eta xi h ∧
        IsMasterCoverStep F (G z.1) U (A z.1) (I z.1) (D z.1)
          (R z.1 ∪ z.2) ∧
        (Disjoint (initial z.1) (later z.1) ∧
          initial z.1 ∪ later z.1 =
            I z.1 ∪ (D z.1 ∪ R z.1)) ∧
        (IsSimultaneousLinkCover F (A z.1)
            (I z.1 ∪ (D z.1 ∪ R z.1)) (K z.1) z.2 ∧
          IsSimultaneousLinkFamily (K z.1) z.2) := by
    intro z hz
    exact ⟨holdJoint z hz, hstep z hz, hclassificationJoint z hz,
      hlink z hz⟩
  have hpointProbability : 1 - xi' <= J.probability (fun z =>
      IsMasterStagePointwiseGood W next F
        (updatedStageGraph (G z.1) U (R z.1 ∪ z.2))
        (updatedStageAvailable F U (A z.1)
          (I z.1) (D z.1) (R z.1 ∪ z.2))
        (initial z.1) (later z.1 ∪ z.2) p eta xi' h) := by
    have htypU : 1 - xi' <= J.probability (fun z =>
        IsIterationTypical W next
          (updatedStageGraph (G z.1) U (R z.1 ∪ z.2))
          (updatedStageAvailable F U (A z.1)
            (I z.1) (D z.1) (R z.1 ∪ z.2)) p eta xi' h) := by
      simpa only [hU] using htypProbability
    refine htypU.trans ?_
    apply J.probability_mono_of_supported hsupportAll
    intro z hz htypNext
    have hstructGood := hz.1.updated (by simpa only [hU] using hz.2.1)
      (by simpa only [hU] using htypNext)
    have hdisjoint : Disjoint (initial z.1) (later z.1 ∪ z.2) := by
      rw [Finset.disjoint_left]
      intro T hTI hTlater
      rcases mem_union.mp hTlater with hTL | hTM
      · exact Finset.disjoint_left.mp hz.2.2.1.1 hTI hTL
      · have hTP : T ∈ I z.1 ∪ (D z.1 ∪ R z.1) := by
          rw [← hz.2.2.1.2]
          exact mem_union_left (later z.1) hTI
        exact Finset.disjoint_left.mp hz.2.2.2.1.2.1 hTP hTM
    have hunion : initial z.1 ∪ (later z.1 ∪ z.2) =
        I z.1 ∪ (D z.1 ∪ (R z.1 ∪ z.2)) := by
      simpa only [union_assoc] using
        congrArg (fun S : TripleSystemOn V => S ∪ z.2) hz.2.2.1.2
    have hstructGood' : IsMasterStagePointwiseGood W next F
        (updatedStageGraph (G z.1) U (R z.1 ∪ z.2))
        (updatedStageAvailable F U (A z.1)
          (I z.1) (D z.1) (R z.1 ∪ z.2))
        (I z.1) (D z.1 ∪ (R z.1 ∪ z.2)) p eta xi' h := by
      simpa only [hU] using hstructGood
    exact IsMasterStagePointwiseGood.reclassify hstructGood'
      hdisjoint hunion
  have hgood : IsMasterIterationGood J W next F
      (fun z => updatedStageGraph (G z.1) U (R z.1 ∪ z.2))
      (fun z => updatedStageAvailable F U (A z.1)
        (I z.1) (D z.1) (R z.1 ∪ z.2))
      (fun z => initial z.1) (fun z => later z.1 ∪ z.2)
      p eta xi' (2 * C') b' h := ⟨heven, hstrong, hpointProbability⟩
  have havailableJoint : J.SupportedOn fun z => A z.1 ⊆ ambient := by
    have hbind := havailable.jointBind (K := linkLaw)
      (Q := fun _omega _M => True)
      (fun _omega _havailable => by intro _M _hmass; trivial)
    exact fun z hz => (hbind z hz).1
  have hselectedJoint : J.SupportedOn fun z =>
      I z.1 ∪ D z.1 ⊆ ambient := by
    have hbind := hselected.jointBind (K := linkLaw)
      (Q := fun _omega _M => True)
      (fun _omega _hselected => by intro _M _hmass; trivial)
    exact fun z hz => (hbind z hz).1
  have hcoverJoint : J.SupportedOn fun z =>
      CoversOriginalGraph Gzero (G z.1) (I z.1) (D z.1) := by
    have hbind := hcover.jointBind (K := linkLaw)
      (Q := fun _omega _M => True)
      (fun _omega _hcover => by intro _M _hmass; trivial)
    exact fun z hz => (hbind z hz).1
  have hnewAvailable : J.SupportedOn fun z =>
      updatedStageAvailable F U (A z.1) (I z.1) (D z.1)
          (R z.1 ∪ z.2) ⊆ ambient := by
    intro z hz
    exact (updatedStageAvailable_subset F U (A z.1) (I z.1) (D z.1)
      (R z.1 ∪ z.2)).trans (havailableJoint z hz)
  have hnewSelected : J.SupportedOn fun z =>
      initial z.1 ∪ (later z.1 ∪ z.2) ⊆ ambient := by
    intro z hz
    have hunion : initial z.1 ∪ (later z.1 ∪ z.2) =
        I z.1 ∪ (D z.1 ∪ (R z.1 ∪ z.2)) := by
      simpa only [union_assoc] using congrArg
        (fun S : TripleSystemOn V => S ∪ z.2)
        (hclassificationJoint z hz).2
    rw [hunion]
    intro T hT
    rcases mem_union.mp hT with hTI | hTDRM
    · exact hselectedJoint z hz (mem_union_left (D z.1) hTI)
    · rcases mem_union.mp hTDRM with hTD | hTRM
      · exact hselectedJoint z hz (mem_union_right (I z.1) hTD)
      · exact havailableJoint z hz ((hstep z hz).selected hTRM)
  have hnewCover : J.SupportedOn fun z =>
      CoversOriginalGraph Gzero
        (updatedStageGraph (G z.1) U (R z.1 ∪ z.2))
        (initial z.1) (later z.1 ∪ z.2) := by
    intro z hz
    have hstructCover := (hcoverJoint z hz).updated (hstep z hz)
    have hunion : initial z.1 ∪ (later z.1 ∪ z.2) =
        I z.1 ∪ (D z.1 ∪ (R z.1 ∪ z.2)) := by
      simpa only [union_assoc] using congrArg
        (fun S : TripleSystemOn V => S ∪ z.2)
        (hclassificationJoint z hz).2
    simpa only [CoversOriginalGraph, hunion] using hstructCover
  have hnewSupport : J.SupportedOn fun z =>
      GraphSupportedOn
        (updatedStageGraph (G z.1) U (R z.1 ∪ z.2))
        (W.U next : Set V) := by
    intro z _hz
    simpa only [hU] using
      updatedStageGraph_supported (G z.1) U (R z.1 ∪ z.2)
  have hsubJoint : J.SupportedOn fun z => G z.1 ≤ Gzero := by
    have hbind := hsub.jointBind (K := linkLaw)
      (Q := fun _omega _M => True)
      (fun _omega _hsub => by intro _M _hmass; trivial)
    exact fun z hz => (hbind z hz).1
  have hnewSub : J.SupportedOn fun z =>
      updatedStageGraph (G z.1) U (R z.1 ∪ z.2) ≤ Gzero := by
    intro z hz
    exact (updatedStageGraph_le (G z.1) U (R z.1 ∪ z.2)).trans
      (hsubJoint z hz)
  simpa only [J, linkLaw, hU] using
    hgood.compress hnewAvailable hnewSelected hnewCover hnewSub hnewSupport

end

end Erdos207
