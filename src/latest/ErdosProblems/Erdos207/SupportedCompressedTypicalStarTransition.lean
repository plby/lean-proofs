/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SupportedCompressedMasterTransition
import ErdosProblems.Erdos207.SupportedTypicalResidualLinks
import ErdosProblems.Erdos207.TypicalRobustLinkStarReadiness

/-!
# A localized star-capped typical transition

This is the quantitatively sharp nonterminal transition.  In contrast to the
coarser transition, the residual-link loss is measured only inside the next
vortex set and the robust link sampler is conditioned on prescribed vertex
star caps.  Thus neither the old full-stage-degree loss nor a full-stage
degree cutoff is needed.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- A typical intermediate law with localized loss and star caps gives the
next compressed master law. -/
theorem exists_compressedMasterLaw_of_supportedIntermediateTypicalStarCapped
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw Omega} {W : Vortex V ell}
    {level weightStage pointStage : Fin (ell + 1)} (i : Fin ell)
    (hlevel : level.val ≤ i.val)
    (hweightStage : weightStage ≤ i.succ)
    (hpointStage : pointStage ≤ i.succ)
    {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V}
    {A I D R initial later : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {Kold : (omega : Omega) →
      {x : V // x ∉ W.U i.succ} → BipartiteLink V}
    {Gzero : SimpleGraph V} {ambient : TripleSystemOn V}
    {p reserveDensity C b eta xi xi' : ℝ≥0} {h : ℕ}
    (hreserve : IsReserveStronglyWellDistributed law W weightStage initial later
      reserve p reserveDensity C b)
    (hclassification : law.SupportedOn fun omega ↦
      Disjoint (initial omega) (later omega) ∧
        initial omega ∪ later omega =
          I omega ∪ (D omega ∪ R omega))
    (htyp : law.SupportedOn fun omega ↦
      IsIterationTypical W level (G omega) (A omega) p eta xi h)
    (htri : law.SupportedOn fun omega ↦
      ConsistsOfTriangles (G omega) (A omega))
    (hold : law.SupportedOn fun omega ↦
      G omega ≤ leaveGraph (I omega ∪ D omega))
    (hGsupp : law.SupportedOn fun omega ↦
      GraphSupportedOn (G omega) (W.U i.castSucc : Set V))
    (hstateOld : law.SupportedOn fun omega ↦
      IsIntermediateLinkState (G omega) (W.U i.succ) (A omega)
          (I omega) (D omega) (R omega) (Kold omega) ∧
        (∀ o, (Kold omega o).center =
          outsideVertexEmbedding (W.U i.succ) o) ∧
        (∀ o, outsideVertexEmbedding (W.U i.succ) o ∉ W.U i.succ) ∧
        (∀ o, (Kold omega o).left ⊆ W.U i.succ) ∧
        (∀ o, (Kold omega o).right ⊆ W.U i.succ) ∧
        (∀ o, (Kold omega o).SpokesIn (reserve omega)))
    (hpacking : law.SupportedOn fun omega ↦
      IsPackingOn (I omega ∪ (D omega ∪ R omega)))
    (havoid : law.SupportedOn fun omega ↦
      AvoidsForbidden (I omega ∪ (D omega ∪ R omega)) F)
    (m d degreeMax codegree loss : ℕ)
    (hcovered : law.SupportedOn fun omega ↦
      ∀ o : {x : V // x ∉ W.U i.succ},
        ((coveredGraph (R omega)).neighborFinset o.1 ∩
          W.U i.succ).card ≤ loss)
    (hh : 3 ≤ h)
    (hlower : (m + loss + 1 : ℝ≥0) ≤
      (1 - xi) * (p ^ 2 * eta * (W.U i.succ).card))
    (hupper : (1 + xi) *
      (p ^ 2 * eta * (W.U i.succ).card) ≤ (degreeMax : ℝ≥0))
    (hcodegree : (1 + xi) *
      (p ^ 3 * eta ^ 2 * (W.U i.succ).card) ≤ (codegree : ℝ≥0))
    (hbisection : ∀ omega, 0 < law.mass omega →
      ∀ o : {x : V // x ∉ W.U i.succ},
      ((@residualNeighbors V _ _ (G omega)
          (Classical.decRel (G omega).Adj) (R omega) o.1).card : ℝ≥0) *
        (2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)) < 1)
    (Delta groupSize density candidate cutoff degreeCutoff rootCutoff
      familyCutoff : ℕ)
    (hdensityLe : density ≤ d)
    (hmixing : ∀ omega, 0 < law.mass omega →
      ∀ o : {x : V // x ∉ W.U i.succ},
      let K := supportedReserveTypicalResidualLinks G (W.U i.succ)
        reserve A I D R d degreeMax codegree omega
      0 < (K o).right.card → ∀ s : ℕ,
        cutoff < s → s ≤ (K o).right.card →
          (K o).right.card * (degreeMax + codegree * s) <
            s * (d - density) ^ 2)
    (hdegreeScalar : Delta * groupSize + groupSize ≤ d - cutoff)
    (hd : 2 ≤ d) (hdensityScalar : 3 * candidate ≤ density)
    (hcandidateScalar : Delta * groupSize + groupSize ≤ candidate)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (kappaLink : ℝ≥0) (momentOrder : ℕ)
    (hfamily : ∀ S ∈ F, S.card ≤ familyCutoff)
    (hkappaLink : ∀ omega, 0 < law.mass omega →
      ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 ↦
          relativeRootedThreatRemainder
            (I omega ∪ (D omega ∪ R omega)) z)
        (fun _ ↦ sigma) kappaLink)
    (caps : Omega → V → ℕ)
    (hsmall : ∀ omega, 0 < law.mass omega →
      let K := supportedReserveTypicalResidualLinks G (W.U i.succ)
        reserve A I D R d degreeMax codegree omega
      (Fintype.card
          (SimultaneousHallGroupIndex
            {x : V // x ∉ W.U i.succ} V K Delta) : ℝ≥0) *
          (1 - sigma) ^ groupSize +
        (Fintype.card (DistinctPair V) : ℝ≥0) *
          ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) *
              kappaLink) ^ momentOrder) /
            (rootCutoff + 1 : ℝ≥0) ^ momentOrder) +
        ∑ v : V,
          ((ambientTriplesThrough v).powersetCard (caps omega v)).card *
            sigma ^ caps omega v < 1)
    (hdegreeBudget : ∀ omega, 0 < law.mass omega → ∀ v : V,
      2 * ((triplesThrough (R omega) v).card + caps omega v) ≤
        degreeCutoff)
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta)
    (alpha : ℝ≥0)
    (hnormalizer : ∀ omega, 0 < law.mass omega →
      let K := supportedReserveTypicalResidualLinks G (W.U i.succ)
        reserve A I D R d degreeMax codegree omega
      sigma /
          (FiniteLaw.independentBits
            (fun _ : SimultaneousLinkPair
                {x : V // x ∉ W.U i.succ} V K ↦ sigma)
            (fun _ ↦ hsigma)).probability
              (IsSimultaneousRobustLinkStarGood F
                (I omega ∪ (D omega ∪ R omega)) (W.U i.succ)
                (outsideVertexEmbedding (W.U i.succ)) K
                (fun o ↦
                  (supportedReserveTypicalResidualLinks_global G
                    (W.U i.succ) reserve A I D R d degreeMax codegree
                    omega).1 o)
                (fun o ↦ o.2)
                (fun o ↦
                  (supportedReserveTypicalResidualLinks_global G
                    (W.U i.succ) reserve A I D R d degreeMax codegree
                    omega).2.2.1 o)
                (fun o ↦
                  (supportedReserveTypicalResidualLinks_global G
                    (W.U i.succ) reserve A I D R d degreeMax codegree
                    omega).2.2.2.1 o)
                (fun o ↦ linkAvailableRelation (K o) (A omega))
                Delta rootCutoff (caps omega)) ≤ alpha)
    (epsilonStar C' b' : ℝ≥0)
    (htail : ∀ omega, ∑ v : V,
      ((ambientTriplesThrough v).powersetCard (caps omega v)).card *
        alpha ^ caps omega v ≤ epsilonStar)
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (hCC' : C ≤ C') (hC' : 1 ≤ C')
    (herrorFactor : alpha * C ^ 2 ≤ 1) (hbb' : b ≤ b')
    (hnew : ∀ T : TripleOn V,
      alpha * C ^ 2 * reserveDensity ^ 2 ≤
        p / ((W.U (W.truncatedLevel i.succ T)).card : ℝ≥0))
    (hevenOld : HasEvenStageGraphs law G)
    (hpoint : law.SupportedOn fun omega ↦
      IsMasterStagePointwiseGood W pointStage F (G omega) (A omega)
        (I omega) (D omega) p eta xi h)
    (hxixi' : xi ≤ xi')
    (q s : ℕ) (hFcard : ∀ S ∈ F, S.card ≤ q)
    (hbroot : ∀ T : TripleSystemOn V, T.card ≤ s * (q - 1) →
      b' ≤ setWeight (masterUnionTriangleWeight W i.succ p) T)
    (kappaMaster : ℝ≥0)
    (hkappaMaster : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 ↦
          rootedThreatRemainder z)
        (masterUnionTriangleWeight W i.succ p) kappaMaster)
    (r a : ℕ)
    (hepsilon : epsilonStar +
      strongRootedTail V (2 * C') kappaMaster r q s ≤ xi')
    (huniformStar : ∀ omega v,
      2 * ((triplesThrough (R omega) v).card + caps omega v) ≤ a)
    (hdegreeBudgetSame : ∀ omega (j : Fin ell), i.succ.val ≤ j.val →
      ∀ v ∈ W.U j.castSucc,
        (2 : ℝ≥0) *
            ((triplesThrough (R omega) v).card + caps omega v) ≤
          (xi' - xi) * (p * (W.U j.castSucc).card))
    (hdegreeBudgetNext : ∀ omega (j : Fin ell), i.succ.val ≤ j.val →
      ∀ v ∈ W.U j.castSucc,
        (2 : ℝ≥0) *
            ((triplesThrough (R omega) v).card + caps omega v) ≤
          (xi' - xi) * (p * (W.U j.succ).card))
    (hextensionBudget : ∀ omega M (j : Fin ell),
      i.succ.val ≤ j.val →
      ∀ jStar : Fin (ell + 1),
        (jStar = j.castSucc ∨ jStar = j.succ) →
      ∀ Q : SimpleGraph V,
        Q ≤ updatedStageGraph (G omega) (W.U i.succ) (R omega ∪ M) →
        GraphSupportedOn Q (W.U j.castSucc : Set V) →
        (graphSupportFinset Q).card ≤ h →
      ((graphSupportFinset Q).card : ℝ≥0) +
          (graphSupportFinset Q).card * a +
            (graphEdges Q).card * (r * q) ≤
        (xi' - xi) *
          (p ^ (graphSupportFinset Q).card *
            eta ^ (graphEdges Q).card * (W.U jStar).card))
    (havailable : law.SupportedOn fun omega ↦ A omega ⊆ ambient)
    (hselected : law.SupportedOn fun omega ↦
      I omega ∪ D omega ⊆ ambient)
    (hcover : law.SupportedOn fun omega ↦
      CoversOriginalGraph Gzero (G omega) (I omega) (D omega))
    (hsub : law.SupportedOn fun omega ↦ G omega ≤ Gzero) :
    ∃ law' : FiniteLaw (MasterStateOn V),
      IsCompressedMasterLaw law' W i.succ F Gzero ambient
        p eta xi' (2 * C') b' h := by
  let U := W.U i.succ
  let K := supportedReserveTypicalResidualLinks G U reserve A I D R
    d degreeMax codegree
  have hreadyOld := htyp.reserveSupportedTypicalResidualLinks_of_typical_localized
    i hlevel U (by rfl) reserve Kold htri hGsupp hstateOld
      m d degreeMax codegree loss (by simpa only [U] using hcovered)
      hh hlower hupper hcodegree
      (by simpa only [U] using hbisection)
  have hprops := hreadyOld.supportedReserveTypicalResidualLinks
    G U reserve A I D R d degreeMax codegree
  have hcenter : ∀ omega o, (K omega o).center =
      outsideVertexEmbedding U o := fun omega o ↦
    (supportedReserveTypicalResidualLinks_global
      G U reserve A I D R d degreeMax codegree omega).1 o
  have hout : ∀ (_omega : Omega) o,
      outsideVertexEmbedding U o ∉ U := fun _omega o ↦ o.2
  have hleft : ∀ omega o, (K omega o).left ⊆ U := fun omega o ↦
    (supportedReserveTypicalResidualLinks_global
      G U reserve A I D R d degreeMax codegree omega).2.2.1 o
  have hright : ∀ omega o, (K omega o).right ⊆ U := fun omega o ↦
    (supportedReserveTypicalResidualLinks_global
      G U reserve A I D R d degreeMax codegree omega).2.2.2.1 o
  have hspokes : ∀ omega o, (K omega o).SpokesIn (reserve omega) :=
    fun omega o ↦ (supportedReserveTypicalResidualLinks_global
      G U reserve A I D R d degreeMax codegree omega).2.2.2.2.1 o
  have hbounds : law.SupportedOn fun omega ↦ ∀ o,
      HasLinkDegreeCodegreeBounds (A omega) (K omega o)
        d degreeMax codegree := fun omega hmass ↦
    (hprops omega hmass).2.2.2.2.2.2
  have hready : law.SupportedOn fun omega ↦
      HasSimultaneousLinkCoverFamilyLaw F (A omega)
        (I omega ∪ (D omega ∪ R omega)) (K omega) alpha := by
    exact
      FiniteLaw.SupportedOn.hasSimultaneousLinkCoverFamilyLaw_of_typical_structural_starCapped
        F G A I D R U K caps (fun omega hmass ↦ (hprops omega hmass).1)
        hcenter hout hleft hright htri hold d degreeMax codegree hbounds
        Delta groupSize density candidate cutoff degreeCutoff rootCutoff
        familyCutoff hdensityLe (by simpa only [K, U] using hmixing)
        hdegreeScalar hd hdensityScalar hcandidateScalar sigma hsigma
        kappaLink momentOrder hfamily hkappaLink
        (by simpa only [K, U] using hsmall) hpacking havoid hdegreeBudget
        hdeletionScalar alpha (by simpa only [K, U] using hnormalizer)
  let linkLaw := supportedSimultaneousLinkCoverKernel F A
    (fun omega ↦ I omega ∪ (D omega ∪ R omega)) K alpha
  have hlink : (law.jointBind linkLaw).SupportedOn fun z ↦
      IsSimultaneousLinkCover F (A z.1)
          (I z.1 ∪ (D z.1 ∪ R z.1)) (K z.1) z.2 ∧
        IsSimultaneousLinkFamily (K z.1) z.2 := by
    exact hready.jointBind_supportedSimultaneousLinkCoverKernel
      F A (fun omega ↦ I omega ∪ (D omega ∪ R omega)) K alpha
  have heven : HasEvenStageGraphs (law.jointBind linkLaw)
      (fun z ↦ updatedStageGraph (G z.1) U (R z.1 ∪ z.2)) := by
    intro z hz
    have hmasses :=
      (FiniteLaw.jointBind_mass_pos_iff law linkLaw z.1 z.2).mp hz
    have hstate := (hprops z.1 hmasses.1).1
    letI : DecidableRel (G z.1).Adj := Classical.decRel (G z.1).Adj
    have hstep : IsMasterCoverStep F (G z.1) U (A z.1)
        (I z.1) (D z.1) (R z.1 ∪ z.2) :=
      (hlink z hz).1.isMasterCoverStep
        hstate.1 hstate.2.1 hstate.2.2
    exact hstep.updated_even (hevenOld z.1 hmasses.1)
      (htri z.1 hmasses.1)
  refine ⟨(law.jointBind linkLaw).map (packMasterState
    (fun z ↦ updatedStageGraph (G z.1) U (R z.1 ∪ z.2))
    (fun z ↦ updatedStageAvailable F U
      (A z.1) (I z.1) (D z.1) (R z.1 ∪ z.2))
    (fun z ↦ initial z.1) (fun z ↦ later z.1 ∪ z.2)), ?_⟩
  exact compressedMasterStep_of_supportedRobustLinkReadiness
    (weightStage := weightStage) (pointStage := pointStage)
    caps epsilonStar (by rfl) hreserve hclassification
    hcenter hout hleft hright hspokes
    hready htail hnonempty hweightStage hCC' hC' herrorFactor hbb' hnew
    (by simpa only [linkLaw, K, U] using heven) hpoint hpointStage
    (fun omega hmass ↦ (hprops omega hmass).1) hxixi' hFcard hbroot
    kappaMaster hkappaMaster hepsilon huniformStar hdegreeBudgetSame
    hdegreeBudgetNext hextensionBudget havailable hselected hcover hsub

end

end Erdos207
