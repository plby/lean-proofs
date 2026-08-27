/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RelativeReserveProtectedSparseRooted
import ErdosProblems.Erdos207.RelativeReserveProtectedNewSparseRooted

/-!
# Inherited master support after sparse rooted conditioning

The sparse rooted stage conditions the correlated law twice.  This file
records that all master-state support properties are inherited by the final
conditioned law.  Keeping these facts in one package avoids repeating the
same `jointBind_fst` and `conditionOn` transport at every vortex level.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- A sparse rooted output together with the old pointwise master facts that
the subsequent compressed transition still needs. -/
structure RelativeReserveProtectedSparseMasterOutput
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell n : ℕ}
    (law : FiniteLaw (RelativeReserveProtectedCorrelatedSample Omega V n))
    (W : Vortex V ell) (weightStage pointStage : Fin (ell + 1))
    (F : ForbiddenFamilyOn V) (i : Fin ell)
    (G : Omega → SimpleGraph V) (A I D : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (d Dint R : ℕ)
    (caps : V → ℕ) (dCross mLink DLink CLink : ℕ)
    (pOld eta xi p reserveDensity C b : ℝ≥0) (h : ℕ)
    (Gzero : SimpleGraph V) (ambient : TripleSystemOn V) : Prop where
  sparse : RelativeReserveProtectedSparseRootedOutput law W weightStage F i
    G A I D bits d Dint R caps dCross mLink DLink CLink
    p reserveDensity C b
  pointwise : law.SupportedOn fun z ↦
    IsMasterStagePointwiseGood W pointStage F (G z.1) (A z.1)
      (I z.1) (D z.1) pOld eta xi h
  even : HasEvenStageGraphs law (fun z ↦ G z.1)
  available : law.SupportedOn fun z ↦ A z.1 ⊆ ambient
  selected : law.SupportedOn fun z ↦ I z.1 ∪ D z.1 ⊆ ambient
  cover : law.SupportedOn fun z ↦
    CoversOriginalGraph Gzero (G z.1) (I z.1) (D z.1)
  sub : law.SupportedOn fun z ↦ G z.1 ≤ Gzero

/-- Sparse rooted conditioning preserves all support properties inherited
from the old compressed master state. -/
theorem RelativeReserveProtectedCorrelatedFacts.conditionOn_sparseRootedResidualLinks_with_masterSupport
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell}
    {pointStage weightStage : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool}
    {n Kpair Kglobal Kinc Delta delta Icut Dcut d a Dint cutoff R : ℕ}
    {pOld reserveDensityOld COld bOld p reserveDensity C b : ℝ≥0}
    (i : Fin ell)
    (hfacts : RelativeReserveProtectedCorrelatedFacts L W pointStage
      weightStage F i (W.U i.succ) G A I D bits I D n Kpair Kglobal
      Kinc Delta delta Icut Dcut d Dint R pOld reserveDensityOld COld
      bOld p reserveDensity C b)
    {alphaPre etaPre : ℝ≥0}
    (P : RelativeReserveProtectedPreliminaryFacts L F (W.U i.succ)
      G A I D bits n Kpair Kglobal Kinc Delta delta Icut Dcut d a Dint
      cutoff alphaPre etaPre)
    {etaMaster xi : ℝ≥0} {h : ℕ}
    (hpoint : L.SupportedOn fun omega ↦
      IsMasterStagePointwiseGood W pointStage F (G omega) (A omega)
        (I omega) (D omega) pOld etaMaster xi h)
    (heven : L.SupportedOn fun omega ↦
      ∀ v : V, Even ((neighborsIn (G omega) univ v).card))
    {q : ℕ}
    (hC : 1 ≤ 2 * C)
    (hfamily : ∀ S ∈ F, S.card ≤ q)
    (hbroot : ∀ T : TripleSystemOn V, T.card ≤ q - 1 →
      b ≤ setWeight (masterUnionTriangleWeight W weightStage p) T)
    (kappa : ℝ≥0)
    (hkappa : ∀ e : DistinctPair V,
      extensionWeight
          (fun z : LocalizedRootedThreatWitness V F e.1.1 e.1.2
            (W.U i.succ) ↦ localizedRootedThreatRemainder z)
          (masterUnionTriangleWeight W weightStage p) ∅ ≤ kappa)
    (caps : V → ℕ) (epsilonPre : ℝ≥0)
    (htailPre : ∑ v : V,
      ((ambientTriplesThrough v).powersetCard (caps v)).card *
        alphaPre ^ caps v ≤ epsilonPre)
    (dCross : ℕ) (epsilonCross : ℝ≥0)
    (htailCross : ∀ omega, 0 < L.mass omega →
      ∑ center : V,
        ((outerIncidentEdges
          (reserveProtectedOuterGraph (G omega) (W.U i.succ)
            (reserveEdges (G omega) (W.U i.succ) (bits omega)))
          (W.U i.succ) center).powersetCard (dCross + 1)).card *
            etaPre ^ (dCross + 1) ≤ epsilonCross)
    (mLink DLink CLink : ℕ)
    (hsampledLinks : L.SupportedOn fun omega ↦
      ReserveSampledLinkBoundsGood (G omega) (A omega) (W.U i.succ)
        mLink DLink CLink (bits omega))
    (hbudget : epsilonPre +
      strongLocalizedRootedFirstTail V (2 * C) kappa R q + epsilonCross < 1)
    {Gzero : SimpleGraph V} {ambient : TripleSystemOn V}
    (havailable : L.SupportedOn fun omega ↦ A omega ⊆ ambient)
    (hselected : L.SupportedOn fun omega ↦ I omega ∪ D omega ⊆ ambient)
    (hcover : L.SupportedOn fun omega ↦
      CoversOriginalGraph Gzero (G omega) (I omega) (D omega))
    (hsub : L.SupportedOn fun omega ↦ G omega ≤ Gzero) :
    let K := relativeReserveProtectedCorrelatedKernel W i F (W.U i.succ)
      G A I D bits n Kpair Kglobal Kinc Delta delta Icut Dcut d Dint
    let J := L.jointBind K
    let RootGood := relativeReserveProtectedRootGood W i F I D R
    let RestGood := fun z ↦
      relativeReserveProtectedPreliminaryCapsGood caps I D z ∧
        relativeReserveProtectedResidualOuterIncidenceGood W i G bits I D
          dCross z
    ∃ hrootPos : 0 < J.probability RootGood,
      ∃ hrestPos : 0 <
          (J.conditionOn RootGood hrootPos).probability RestGood,
        RelativeReserveProtectedSparseMasterOutput
          ((J.conditionOn RootGood hrootPos).conditionOn RestGood hrestPos)
          W weightStage pointStage F i G A I D bits d Dint R caps dCross
          mLink DLink CLink pOld etaMaster xi p reserveDensity
          (((2 * C) /
              (1 - strongLocalizedRootedFirstTail V (2 * C) kappa R q)) /
            (1 - (epsilonPre +
              strongLocalizedRootedFirstTail V (2 * C) kappa R q + epsilonCross)))
          b h Gzero ambient := by
  classical
  dsimp only
  let K := relativeReserveProtectedCorrelatedKernel W i F (W.U i.succ)
    G A I D bits n Kpair Kglobal Kinc Delta delta Icut Dcut d Dint
  let J := L.jointBind K
  let RootGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
    relativeReserveProtectedRootGood W i F I D R
  let RestGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
    fun z ↦ relativeReserveProtectedPreliminaryCapsGood caps I D z ∧
      relativeReserveProtectedResidualOuterIncidenceGood W i G bits I D
        dCross z
  obtain ⟨hrootPos, hrestPos, hsparse⟩ :=
    hfacts.conditionOn_sparseRootedResidualLinks i P hpoint heven hC
      hfamily hbroot kappa hkappa caps epsilonPre htailPre dCross
      epsilonCross htailCross mLink DLink CLink hsampledLinks hbudget
  refine ⟨hrootPos, hrestPos, hsparse, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hpoint.jointBind_fst.conditionOn hrootPos).conditionOn hrestPos
  · exact (heven.jointBind_fst.conditionOn hrootPos).conditionOn hrestPos
  · exact (havailable.jointBind_fst.conditionOn hrootPos).conditionOn hrestPos
  · exact (hselected.jointBind_fst.conditionOn hrootPos).conditionOn hrestPos
  · exact (hcover.jointBind_fst.conditionOn hrootPos).conditionOn hrestPos
  · exact (hsub.jointBind_fst.conditionOn hrootPos).conditionOn hrestPos

/-- The corrected sparse rooted output, together with every support property
inherited from the compressed master law.  The rooted cap counts only
configurations activated by the present preliminary/internal increment. -/
structure RelativeReserveProtectedNewSparseMasterOutput
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell n : ℕ}
    (law : FiniteLaw (RelativeReserveProtectedCorrelatedSample Omega V n))
    (W : Vortex V ell) (weightStage pointStage : Fin (ell + 1))
    (F : ForbiddenFamilyOn V) (i : Fin ell)
    (G : Omega → SimpleGraph V) (A I D : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (d Dint R : ℕ)
    (caps : V → ℕ) (dCross mLink DLink CLink : ℕ)
    (pOld eta xi p reserveDensity C b : ℝ≥0) (h : ℕ)
    (Gzero : SimpleGraph V) (ambient : TripleSystemOn V) : Prop where
  sparse : RelativeReserveProtectedNewSparseRootedOutput law W weightStage F i
    G A I D bits d Dint R caps dCross mLink DLink CLink
    p reserveDensity C b
  pointwise : law.SupportedOn fun z ↦
    IsMasterStagePointwiseGood W pointStage F (G z.1) (A z.1)
      (I z.1) (D z.1) pOld eta xi h
  even : HasEvenStageGraphs law (fun z ↦ G z.1)
  available : law.SupportedOn fun z ↦ A z.1 ⊆ ambient
  selected : law.SupportedOn fun z ↦ I z.1 ∪ D z.1 ⊆ ambient
  cover : law.SupportedOn fun z ↦
    CoversOriginalGraph Gzero (G z.1) (I z.1) (D z.1)
  sub : law.SupportedOn fun z ↦ G z.1 ≤ Gzero

/-- Newly-active sparse rooted conditioning preserves all support properties
of the old compressed master state. -/
theorem RelativeReserveProtectedNewCorrelatedFacts.conditionOn_newSparseRootedResidualLinks_with_masterSupport
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell}
    {pointStage weightStage : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool}
    {n Kpair Kglobal Kinc Delta delta Icut Dcut d a Dint cutoff R : ℕ}
    {alphaPre etaPre : ℝ≥0}
    {pOld reserveDensityOld COld bOld p reserveDensity C b : ℝ≥0}
    (i : Fin ell)
    (hfacts : RelativeReserveProtectedNewCorrelatedFacts L W pointStage
      weightStage F i (W.U i.succ) G A I D bits I D n Kpair Kglobal
      Kinc Delta delta Icut Dcut d Dint R alphaPre etaPre pOld
      reserveDensityOld COld bOld p reserveDensity C b)
    (P : RelativeReserveProtectedPreliminaryFacts L F (W.U i.succ)
      G A I D bits n Kpair Kglobal Kinc Delta delta Icut Dcut d a Dint
      cutoff alphaPre etaPre)
    {etaMaster xi : ℝ≥0} {h : ℕ}
    (hpoint : L.SupportedOn fun omega ↦
      IsMasterStagePointwiseGood W pointStage F (G omega) (A omega)
        (I omega) (D omega) pOld etaMaster xi h)
    (heven : L.SupportedOn fun omega ↦
      ∀ v : V, Even ((neighborsIn (G omega) univ v).card))
    {q s : ℕ} (hfamily : ∀ S ∈ F, S.card ≤ q)
    (kappa : ℝ≥0)
    (hkappa : ∀ omega, 0 < L.mass omega → ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : LocalizedNewRootedThreatWitness V F
            (I omega ∪ D omega) e.1.1 e.1.2 (W.U i.succ) ↦
          localizedNewRootedThreatRemainder z)
        (fun _ ↦ alphaPre + etaPre * (Dint : ℝ≥0)⁻¹) kappa)
    (caps : V → ℕ) (epsilonPre : ℝ≥0)
    (htailPre : ∑ v : V,
      ((ambientTriplesThrough v).powersetCard (caps v)).card *
        alphaPre ^ caps v ≤ epsilonPre)
    (dCross : ℕ) (epsilonCross : ℝ≥0)
    (htailCross : ∀ omega, 0 < L.mass omega →
      ∑ center : V,
        ((outerIncidentEdges
          (reserveProtectedOuterGraph (G omega) (W.U i.succ)
            (reserveEdges (G omega) (W.U i.succ) (bits omega)))
          (W.U i.succ) center).powersetCard (dCross + 1)).card *
            etaPre ^ (dCross + 1) ≤ epsilonCross)
    (mLink DLink CLink : ℕ)
    (hsampledLinks : L.SupportedOn fun omega ↦
      ReserveSampledLinkBoundsGood (G omega) (A omega) (W.U i.succ)
        mLink DLink CLink (bits omega))
    (hbudget : epsilonPre +
      newLocalizedRootedTail V 1 kappa R q s + epsilonCross < 1)
    {Gzero : SimpleGraph V} {ambient : TripleSystemOn V}
    (havailable : L.SupportedOn fun omega ↦ A omega ⊆ ambient)
    (hselected : L.SupportedOn fun omega ↦ I omega ∪ D omega ⊆ ambient)
    (hcover : L.SupportedOn fun omega ↦
      CoversOriginalGraph Gzero (G omega) (I omega) (D omega))
    (hsub : L.SupportedOn fun omega ↦ G omega ≤ Gzero) :
    let K := relativeReserveProtectedCorrelatedKernel W i F (W.U i.succ)
      G A I D bits n Kpair Kglobal Kinc Delta delta Icut Dcut d Dint
    let J := L.jointBind K
    let RootGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
      relativeReserveProtectedNewRootGood F I D A (W.U i.succ) R
    let RestGood := fun z ↦
      relativeReserveProtectedPreliminaryCapsGood caps I D z ∧
        relativeReserveProtectedResidualOuterIncidenceGood W i G bits I D
          dCross z
    ∃ hrootPos : 0 < J.probability RootGood,
      ∃ hrestPos : 0 <
          (J.conditionOn RootGood hrootPos).probability RestGood,
        RelativeReserveProtectedNewSparseMasterOutput
          ((J.conditionOn RootGood hrootPos).conditionOn RestGood hrestPos)
          W weightStage pointStage F i G A I D bits d Dint R caps dCross
          mLink DLink CLink pOld etaMaster xi p reserveDensity
          (((2 * C) /
              (1 - newLocalizedRootedTail V 1 kappa R q s)) /
            (1 - (epsilonPre +
              newLocalizedRootedTail V 1 kappa R q s + epsilonCross)))
          b h Gzero ambient := by
  classical
  dsimp only
  let K := relativeReserveProtectedCorrelatedKernel W i F (W.U i.succ)
    G A I D bits n Kpair Kglobal Kinc Delta delta Icut Dcut d Dint
  let J := L.jointBind K
  let RootGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
    relativeReserveProtectedNewRootGood F I D A (W.U i.succ) R
  let RestGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
    fun z ↦ relativeReserveProtectedPreliminaryCapsGood caps I D z ∧
      relativeReserveProtectedResidualOuterIncidenceGood W i G bits I D
        dCross z
  obtain ⟨hrootPos, hrestPos, hsparse⟩ :=
    hfacts.conditionOn_newSparseRootedResidualLinks i P hpoint heven
      hfamily kappa hkappa caps epsilonPre htailPre dCross epsilonCross
      htailCross mLink DLink CLink hsampledLinks hbudget
  refine ⟨hrootPos, hrestPos, hsparse, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hpoint.jointBind_fst.conditionOn hrootPos).conditionOn hrestPos
  · exact (heven.jointBind_fst.conditionOn hrootPos).conditionOn hrestPos
  · exact (havailable.jointBind_fst.conditionOn hrootPos).conditionOn hrestPos
  · exact (hselected.jointBind_fst.conditionOn hrootPos).conditionOn hrestPos
  · exact (hcover.jointBind_fst.conditionOn hrootPos).conditionOn hrestPos
  · exact (hsub.jointBind_fst.conditionOn hrootPos).conditionOn hrestPos

end

end Erdos207
