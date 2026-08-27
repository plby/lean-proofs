/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RelativeReserveProtectedNewSparseResidualLinks
import ErdosProblems.Erdos207.LocalizedSupportedCompressedTypicalStarTransition

/-!
# Sparse-reserve compressed transition

This transition uses degree and codegree estimates proved on the actual
residual-neighbor set.  In particular it does not subtract the macroscopic
preliminary cover from an ambient typical-link degree.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

def relativeReserveProtectedSparseSupportedLinks
    {Omega V : Type*} [Fintype V] [DecidableEq V] {ell n : ℕ}
    (W : Vortex V ell) (i : Fin ell)
    (G : Omega → SimpleGraph V) (A I D : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool)
    (dLink dCross DLink CLink : ℕ)
    (z : RelativeReserveProtectedCorrelatedSample Omega V n) :
    {x : V // x ∉ W.U i.succ} → BipartiteLink V :=
  supportedReserveTypicalResidualLinks
    (fun z ↦ G z.1) (W.U i.succ)
    (relativeReserveProtectedRootedReserve W i G bits I D)
    (fun z ↦ A z.1) (fun z ↦ I z.1) (fun z ↦ D z.1)
    (fun z ↦ relativeReserveProtectedTotal I D z.1 z.2)
    dLink (DLink + dCross) (CLink + dCross) z

def relativeReserveProtectedSparseSupportedLinksGlobal
    {Omega V : Type*} [Fintype V] [DecidableEq V] {ell n : ℕ}
    (W : Vortex V ell) (i : Fin ell)
    (G : Omega → SimpleGraph V) (A I D : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool)
    (dLink dCross DLink CLink : ℕ)
    (z : RelativeReserveProtectedCorrelatedSample Omega V n) :=
  supportedReserveTypicalResidualLinks_global
    (fun z ↦ G z.1) (W.U i.succ)
    (relativeReserveProtectedRootedReserve W i G bits I D)
    (fun z ↦ A z.1) (fun z ↦ I z.1) (fun z ↦ D z.1)
    (fun z ↦ relativeReserveProtectedTotal I D z.1 z.2)
    dLink (DLink + dCross) (CLink + dCross) z

theorem exists_laterCompressedMasterLaw_of_relativeReserveProtectedSparse
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell n : ℕ}
    {law : FiniteLaw (RelativeReserveProtectedCorrelatedSample Omega V n)}
    {W : Vortex V ell} {weightStage pointStage : Fin (ell + 1)}
    (i : Fin ell) (hweightStage : weightStage ≤ i.succ)
    (hpointStage : pointStage ≤ i.succ)
    {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool}
    {dInc Dint Rroot : ℕ} {preCaps : V → ℕ}
    {dCross mLink DLink CLink : ℕ}
    {p reserveDensity C b eta xi xi' : ℝ≥0} {h : ℕ}
    (hout : RelativeReserveProtectedNewSparseRootedOutput law W weightStage F i
      G A I D bits dInc Dint Rroot preCaps dCross mLink DLink CLink
      p reserveDensity C b)
    {Gzero : SimpleGraph V} {ambient : TripleSystemOn V}
    (m dLink : ℕ) (hm : m + dInc ≤ mLink)
    (hbisection : ∀ z, 0 < law.mass z →
      ∀ o : {x : V // x ∉ W.U i.succ},
      ((@residualNeighbors V _ _ (G z.1)
          (Classical.decRel (G z.1).Adj)
          (relativeReserveProtectedTotal I D z.1 z.2) o.1).card : ℝ≥0) *
        (2 * (2 : ℝ≥0) ^ dLink * (3 / 4 : ℝ≥0) ^
          (m - 2 * dLink)) < 1)
    (Delta groupSize density candidate cutoff degreeCutoff rootCutoff
      familyCutoff : ℕ)
    (hdensityLe : density ≤ dLink)
    (hmixing : ∀ z, 0 < law.mass z →
      ∀ o : {x : V // x ∉ W.U i.succ},
      let K := relativeReserveProtectedSparseSupportedLinks W i G A I D bits
        dLink dCross DLink CLink z
      0 < (K o).right.card → ∀ s : ℕ,
        cutoff < s → s ≤ (K o).right.card →
          (K o).right.card * ((DLink + dCross) +
              (CLink + dCross) * s) <
            s * (dLink - density) ^ 2)
    (hdegreeScalar : Delta * groupSize + groupSize ≤ dLink - cutoff)
    (hd : 2 ≤ dLink) (hdensityScalar : 3 * candidate ≤ density)
    (hcandidateScalar : Delta * groupSize + groupSize ≤ candidate)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (kappaLink : ℝ≥0) (momentOrder : ℕ)
    (hfamily : ∀ S ∈ F, S.card ≤ familyCutoff)
    (hkappaLink : ∀ z, 0 < law.mass z → ∀ e : DistinctPair V,
      HasExtensionBound
        (fun w : RootedThreatWitness V F e.1.1 e.1.2 ↦
          relativeRootedThreatRemainder
            (I z.1 ∪ (D z.1 ∪
              relativeReserveProtectedTotal I D z.1 z.2)) w)
        (fun _ ↦ sigma) kappaLink)
    (caps : RelativeReserveProtectedCorrelatedSample Omega V n → V → ℕ)
    (hsmall : ∀ z, 0 < law.mass z →
      let K := relativeReserveProtectedSparseSupportedLinks W i G A I D bits
        dLink dCross DLink CLink z
      (Fintype.card
          (SimultaneousHallGroupIndex
            {x : V // x ∉ W.U i.succ} V K Delta) : ℝ≥0) *
          (1 - sigma) ^ groupSize +
        (Fintype.card (DistinctPair V) : ℝ≥0) *
          ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) *
              kappaLink) ^ momentOrder) /
            (rootCutoff + 1 : ℝ≥0) ^ momentOrder) +
        ∑ v : V,
          ((ambientTriplesThrough v).powersetCard (caps z v)).card *
            sigma ^ caps z v < 1)
    (hdegreeBudget : ∀ z, 0 < law.mass z → ∀ v : V,
      2 * ((triplesThrough
        (relativeReserveProtectedTotal I D z.1 z.2) v).card + caps z v) ≤
        degreeCutoff)
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta)
    (alpha : ℝ≥0)
    (hnormalizer : ∀ z, 0 < law.mass z →
      let K := relativeReserveProtectedSparseSupportedLinks W i G A I D bits
        dLink dCross DLink CLink z
      sigma /
          (FiniteLaw.independentBits
            (fun _ : SimultaneousLinkPair
                {x : V // x ∉ W.U i.succ} V K ↦ sigma)
            (fun _ ↦ hsigma)).probability
              (IsSimultaneousRobustLinkStarGood F
                (I z.1 ∪ (D z.1 ∪
                  relativeReserveProtectedTotal I D z.1 z.2))
                (W.U i.succ) (outsideVertexEmbedding (W.U i.succ)) K
                (fun o ↦
                  (relativeReserveProtectedSparseSupportedLinksGlobal W i
                    G A I D bits dLink dCross DLink CLink z).1 o)
                (fun o ↦ o.2)
                (fun o ↦
                  (relativeReserveProtectedSparseSupportedLinksGlobal W i
                    G A I D bits dLink dCross DLink CLink z).2.2.1 o)
                (fun o ↦
                  (relativeReserveProtectedSparseSupportedLinksGlobal W i
                    G A I D bits dLink dCross DLink CLink z).2.2.2.1 o)
                (fun o ↦ linkAvailableRelation (K o) (A z.1))
                Delta rootCutoff (caps z)) ≤ alpha)
    (epsilonStar C' b' : ℝ≥0)
    (htail : ∀ z, ∑ v : V,
      ((ambientTriplesThrough v).powersetCard (caps z v)).card *
        alpha ^ caps z v ≤ epsilonStar)
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (hCC' : C ≤ C') (hC' : 1 ≤ C')
    (herrorFactor : alpha * C ^ 2 ≤ 1) (hbb' : b ≤ b')
    (hnew : ∀ T : TripleOn V,
      alpha * C ^ 2 * reserveDensity ^ 2 ≤
        p / ((W.U (W.truncatedLevel i.succ T)).card : ℝ≥0))
    (hevenOld : HasEvenStageGraphs law (fun z ↦ G z.1))
    (hpoint : law.SupportedOn fun z ↦
      IsMasterStagePointwiseGood W pointStage F (G z.1) (A z.1)
        (I z.1) (D z.1) p eta xi h)
    (hxixi' : xi ≤ xi')
    (q : ℕ) (hFcard : ∀ S ∈ F, S.card ≤ q)
    (hbroot : ∀ T : TripleSystemOn V, T.card ≤ q - 1 →
      b' ≤ setWeight (masterUnionTriangleWeight W i.succ p) T)
    (kappaMaster : ℝ≥0)
    (hkappaMaster : ∀ e : DistinctPair V,
      extensionWeight
          (fun z : LocalizedRootedThreatWitness V F e.1.1 e.1.2
            (W.U i.succ) ↦ localizedRootedThreatRemainder z)
          (masterUnionTriangleWeight W i.succ p) ∅ ≤ kappaMaster)
    (r a : ℕ)
    (hepsilon : epsilonStar +
      strongLocalizedRootedFirstTail V (2 * C') kappaMaster r q ≤ xi')
    (huniformStar : ∀ z v,
      2 * ((triplesThrough
        (relativeReserveProtectedTotal I D z.1 z.2) v).card + caps z v) ≤ a)
    (hdegreeBudgetSame : ∀ z (j : Fin ell), i.succ.val ≤ j.val →
      ∀ v ∈ W.U j.castSucc,
        (2 : ℝ≥0) *
            ((triplesThrough
              (relativeReserveProtectedTotal I D z.1 z.2) v).card +
                caps z v) ≤
          (xi' - xi) * (p * (W.U j.castSucc).card))
    (hdegreeBudgetNext : ∀ z (j : Fin ell), i.succ.val ≤ j.val →
      ∀ v ∈ W.U j.castSucc,
        (2 : ℝ≥0) *
            ((triplesThrough
              (relativeReserveProtectedTotal I D z.1 z.2) v).card +
                caps z v) ≤
          (xi' - xi) * (p * (W.U j.succ).card))
    (hextensionBudget :
      ∀ (z : RelativeReserveProtectedCorrelatedSample Omega V n)
        (M : TripleSystemOn V) (j : Fin ell), i.succ.val ≤ j.val →
      ∀ jStar : Fin (ell + 1),
        (jStar = j.castSucc ∨ jStar = j.succ) →
      ∀ Q : SimpleGraph V,
        Q ≤ updatedStageGraph (G z.1) (W.U i.succ)
          (relativeReserveProtectedTotal I D z.1 z.2 ∪ M) →
        GraphSupportedOn Q (W.U j.castSucc : Set V) →
        (graphSupportFinset Q).card ≤ h →
      ((graphSupportFinset Q).card : ℝ≥0) +
          (graphSupportFinset Q).card * a +
            (graphEdges Q).card * (r * q) ≤
        (xi' - xi) *
          (p ^ (graphSupportFinset Q).card *
            eta ^ (graphEdges Q).card * (W.U jStar).card))
    (havailable : law.SupportedOn fun z ↦ A z.1 ⊆ ambient)
    (hselected : law.SupportedOn fun z ↦ I z.1 ∪ D z.1 ⊆ ambient)
    (hcover : law.SupportedOn fun z ↦
      CoversOriginalGraph Gzero (G z.1) (I z.1) (D z.1))
    (hsub : law.SupportedOn fun z ↦ G z.1 ≤ Gzero) :
    ∃ law' : FiniteLaw (MasterStateOn V),
      IsCompressedMasterLaw law' W i.succ F Gzero ambient
        p eta xi' (2 * C') b' h := by
  let U := W.U i.succ
  let Gf : RelativeReserveProtectedCorrelatedSample Omega V n →
      SimpleGraph V := fun z ↦ G z.1
  let Af : RelativeReserveProtectedCorrelatedSample Omega V n →
      TripleSystemOn V := fun z ↦ A z.1
  let If : RelativeReserveProtectedCorrelatedSample Omega V n →
      TripleSystemOn V := fun z ↦ I z.1
  let Df : RelativeReserveProtectedCorrelatedSample Omega V n →
      TripleSystemOn V := fun z ↦ D z.1
  let Rf : RelativeReserveProtectedCorrelatedSample Omega V n →
      TripleSystemOn V := fun z ↦
    relativeReserveProtectedTotal I D z.1 z.2
  let later : RelativeReserveProtectedCorrelatedSample Omega V n →
      TripleSystemOn V := fun z ↦ D z.1 ∪ Rf z
  let reserve : RelativeReserveProtectedCorrelatedSample Omega V n →
      Finset (Sym2 V) := relativeReserveProtectedRootedReserve W i G bits I D
  let K := supportedReserveTypicalResidualLinks Gf U reserve Af If Df Rf
    dLink (DLink + dCross) (CLink + dCross)
  have hclassification : law.SupportedOn fun z ↦
      Disjoint (If z) (later z) ∧
        If z ∪ later z = If z ∪ (Df z ∪ Rf z) := by
    intro z hz
    exact ⟨hout.disjoint z hz, rfl⟩
  have htri : law.SupportedOn fun z ↦
      ConsistsOfTriangles (Gf z) (Af z) := fun z hz ↦
    (hout.structural z hz).1
  have hold : law.SupportedOn fun z ↦
      Gf z ≤ leaveGraph (If z ∪ Df z) := fun z hz ↦
    (hout.structural z hz).2.1
  have hpacking : law.SupportedOn fun z ↦
      IsPackingOn (If z ∪ (Df z ∪ Rf z)) := fun z hz ↦
    (hout.structural z hz).2.2.1
  have havoid : law.SupportedOn fun z ↦
      AvoidsForbidden (If z ∪ (Df z ∪ Rf z)) F := fun z hz ↦
    (hout.structural z hz).2.2.2.1
  have hreadyOld : law.SupportedOn fun z ↦
      HasReserveSupportedTypicalResidualLinks (Gf z) U (reserve z)
        (Af z) (If z) (Df z) (Rf z)
        dLink (DLink + dCross) (CLink + dCross) := by
    simpa only [Gf, U, reserve, Af, If, Df, Rf,
      HasReserveSupportedTypicalResidualLinks] using
        hout.exists_typicalResidualLinks m dLink hm hbisection
  have hprops := hreadyOld.supportedReserveTypicalResidualLinks
    Gf U reserve Af If Df Rf dLink (DLink + dCross) (CLink + dCross)
  have hcenter : ∀ z o, (K z o).center = outsideVertexEmbedding U o :=
    fun z o ↦ (supportedReserveTypicalResidualLinks_global Gf U reserve
      Af If Df Rf dLink (DLink + dCross) (CLink + dCross) z).1 o
  have houtside : ∀ (_z : RelativeReserveProtectedCorrelatedSample Omega V n)
      o, outsideVertexEmbedding U o ∉ U := fun _z o ↦ o.2
  have hleft : ∀ z o, (K z o).left ⊆ U := fun z o ↦
    (supportedReserveTypicalResidualLinks_global Gf U reserve Af If Df Rf
      dLink (DLink + dCross) (CLink + dCross) z).2.2.1 o
  have hright : ∀ z o, (K z o).right ⊆ U := fun z o ↦
    (supportedReserveTypicalResidualLinks_global Gf U reserve Af If Df Rf
      dLink (DLink + dCross) (CLink + dCross) z).2.2.2.1 o
  have hspokes : ∀ z o, (K z o).SpokesIn (reserve z) := fun z o ↦
    (supportedReserveTypicalResidualLinks_global Gf U reserve Af If Df Rf
      dLink (DLink + dCross) (CLink + dCross) z).2.2.2.2.1 o
  have hbounds : law.SupportedOn fun z ↦ ∀ o,
      HasLinkDegreeCodegreeBounds (Af z) (K z o)
        dLink (DLink + dCross) (CLink + dCross) := fun z hz ↦
    (hprops z hz).2.2.2.2.2.2
  have hready : law.SupportedOn fun z ↦
      HasSimultaneousLinkCoverFamilyLaw F (Af z)
        (If z ∪ (Df z ∪ Rf z)) (K z) alpha := by
    exact
      FiniteLaw.SupportedOn.hasSimultaneousLinkCoverFamilyLaw_of_typical_structural_starCapped
        F Gf Af If Df Rf U K caps (fun z hz ↦ (hprops z hz).1)
        hcenter houtside hleft hright htri hold dLink
        (DLink + dCross) (CLink + dCross) hbounds
        Delta groupSize density candidate cutoff degreeCutoff rootCutoff
        familyCutoff hdensityLe (by simpa only [K, U, Gf, Af, If, Df,
          Rf, reserve, relativeReserveProtectedSparseSupportedLinks] using
            hmixing)
        hdegreeScalar hd hdensityScalar hcandidateScalar sigma hsigma
        kappaLink momentOrder hfamily (by simpa only [If, Df, Rf] using
          hkappaLink)
        (by
          intro z hz
          dsimp only [K, U, Gf, Af, If, Df, Rf, reserve,
            relativeReserveProtectedSparseSupportedLinks] at ⊢
          convert hsmall z hz using 1 <;> rfl)
        hpacking havoid (by simpa only [Rf] using hdegreeBudget)
        hdeletionScalar alpha (by
          intro z hz
          dsimp only [K, U, Gf, Af, If, Df, Rf, reserve,
            relativeReserveProtectedSparseSupportedLinks] at ⊢
          convert hnormalizer z hz using 1 <;> rfl)
  let linkLaw := supportedSimultaneousLinkCoverKernel F Af
    (fun z ↦ If z ∪ (Df z ∪ Rf z)) K alpha
  have hlink : (law.jointBind linkLaw).SupportedOn fun z ↦
      IsSimultaneousLinkCover F (Af z.1)
          (If z.1 ∪ (Df z.1 ∪ Rf z.1)) (K z.1) z.2 ∧
        IsSimultaneousLinkFamily (K z.1) z.2 := by
    exact hready.jointBind_supportedSimultaneousLinkCoverKernel
      F Af (fun z ↦ If z ∪ (Df z ∪ Rf z)) K alpha
  have heven : HasEvenStageGraphs (law.jointBind linkLaw)
      (fun z ↦ updatedStageGraph (Gf z.1) U (Rf z.1 ∪ z.2)) := by
    intro z hz
    have hmasses :=
      (FiniteLaw.jointBind_mass_pos_iff law linkLaw z.1 z.2).mp hz
    have hstate := (hprops z.1 hmasses.1).1
    letI : DecidableRel (Gf z.1).Adj := Classical.decRel (Gf z.1).Adj
    have hstep : IsMasterCoverStep F (Gf z.1) U (Af z.1)
        (If z.1) (Df z.1) (Rf z.1 ∪ z.2) :=
      (hlink z hz).1.isMasterCoverStep
        hstate.1 hstate.2.1 hstate.2.2
    exact hstep.updated_even (hevenOld z.1 hmasses.1)
      (htri z.1 hmasses.1)
  refine ⟨(law.jointBind linkLaw).map (packMasterState
    (fun z ↦ updatedStageGraph (Gf z.1) U (Rf z.1 ∪ z.2))
    (fun z ↦ updatedStageAvailable F U
      (Af z.1) (If z.1) (Df z.1) (Rf z.1 ∪ z.2))
    (fun z ↦ If z.1) (fun z ↦ later z.1 ∪ z.2)), ?_⟩
  exact compressedMasterStep_of_supportedRobustLinkReadiness_localizedRoot
    (weightStage := weightStage) (pointStage := pointStage)
    caps epsilonStar (by rfl) hout.strong hclassification
    hcenter houtside hleft hright hspokes hready htail hnonempty hweightStage
    hCC' hC' herrorFactor hbb' hnew
    (by simpa only [linkLaw, Gf, Af, If, Df, Rf, U] using heven)
    (by simpa only [Gf, Af, If, Df] using hpoint)
    hpointStage
    (fun z hz ↦ (hprops z hz).1) hxixi' hFcard hbroot
    kappaMaster hkappaMaster hepsilon
    (by simpa only [Rf] using huniformStar)
    (by simpa only [Rf] using hdegreeBudgetSame)
    (by simpa only [Rf] using hdegreeBudgetNext)
    (by simpa only [Gf, Rf, U] using hextensionBudget)
    (by simpa only [Af] using havailable)
    (by simpa only [If, Df] using hselected)
    (by simpa only [Gf, If, Df] using hcover)
    (by simpa only [Gf] using hsub)

end

end Erdos207
