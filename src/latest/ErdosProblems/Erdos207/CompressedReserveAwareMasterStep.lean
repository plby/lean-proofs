/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.MasterLawCompression
import ErdosProblems.Erdos207.SupportedReserveAwareMasterIteration

/-!
# A compressed reserve-aware master step

This file packages the support-sensitive reserve/link update together with
the fixed-state compression used between consecutive vortex levels.  The
probabilistic step may have a dependent product sample space; its output is
immediately pushed forward to `MasterStateOn V` while retaining the ambient
selection, cumulative coverage, and graph-support invariants.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- The complete support-sensitive reserve-aware step, followed by
compression to the fixed master state space. -/
theorem compressedMasterStep_of_reserveAwareKernel_strongRootedCaps_supported
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {ell : Nat} {law : FiniteLaw Omega}
    {linkLaw : Omega → FiniteLaw (TripleSystemOn V)}
    {W : Vortex V ell} {k next : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {U : Finset V}
    {G : Omega → SimpleGraph V}
    {A I D R : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {center : Omega → ({x : V // x ∉ U} ↪ V)}
    {K : (omega : Omega) → {x : V // x ∉ U} → BipartiteLink V}
    {Gzero : SimpleGraph V} {ambient : TripleSystemOn V}
    {p reserveDensity C b alpha C' b' eta xi xi' : NNReal}
    {h a r q s : Nat}
    (caps : Omega → V → Nat)
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
            eta ^ (graphEdges Q).card * (W.U iStar).card))
    (havailable : law.SupportedOn fun omega => A omega ⊆ ambient)
    (hselected : law.SupportedOn fun omega =>
      I omega ∪ D omega ⊆ ambient)
    (hcover : law.SupportedOn fun omega =>
      CoversOriginalGraph Gzero (G omega) (I omega) (D omega))
    (hsub : law.SupportedOn fun omega => G omega ≤ Gzero) :
    IsCompressedMasterLaw
      ((law.jointBind linkLaw).map (packMasterState
        (fun z => updatedStageGraph (G z.1) (W.U next)
          (R z.1 ∪ z.2))
        (fun z => updatedStageAvailable F (W.U next)
          (A z.1) (I z.1) (D z.1) (R z.1 ∪ z.2))
        (fun z => I z.1)
        (fun z => D z.1 ∪ (R z.1 ∪ z.2))))
      W next F Gzero ambient p eta xi' (2 * C') b' h := by
  have hgood :=
    masterIterationGood_of_reserveAwareKernel_strongRootedCaps_supported
      caps epsilonStar hU hreserve hcenter hout hleft hright hspokes
      hstruct hlink hC4 htail hnonempty hkn hCC' hC' herrorFactor hbb'
      hnew heven hold hstate hxixi' hFcard hbroot kappa hkappa hepsilon
      huniformStar hdegreeBudgetSame hdegreeBudgetNext hextensionBudget
  have hstep : (law.jointBind linkLaw).SupportedOn fun z =>
      IsMasterCoverStep F (G z.1) U (A z.1) (I z.1) (D z.1)
        (R z.1 ∪ z.2) :=
    hstate.jointBind_masterCoverStep_of_jointLink
      (fun z hz => (hlink z hz).1)
  subst U
  exact compressMasterUpdate hgood hstep havailable hselected hcover hsub

end

end Erdos207
