/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RelativeReserveProtectedNewCorrelatedStage
import ErdosProblems.Erdos207.RelativeNewCorrelatedRootedResidualLinks
import ErdosProblems.Erdos207.RelativeReserveProtectedCorrelatedRooted

/-!
# Corrected rooted conditioning for a relative correlated stage

The rooted event records only configurations activated by the current
preliminary/internal increment.  Its baseline is the packing `I ∪ D`
present before either subphase begins.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def relativeReserveProtectedNewRootGood
    {Omega V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (F : ForbiddenFamilyOn V) (I D A : Omega → TripleSystemOn V)
    (U : Finset V) (R : ℕ)
    (z : RelativeReserveProtectedCorrelatedSample Omega V n) : Prop :=
  NewRootedActiveCapsGoodIn F (I z.1 ∪ D z.1)
    ((I z.1 ∪ D z.1) ∪
      relativeReserveProtectedTotal I D z.1 z.2) (A z.1) U R

structure RelativeReserveProtectedNewRootedOutput
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell n : ℕ}
    (law : FiniteLaw (RelativeReserveProtectedCorrelatedSample Omega V n))
    (W : Vortex V ell) (next : Fin (ell + 1))
    (F : ForbiddenFamilyOn V) (i : Fin ell)
    (G : Omega → SimpleGraph V) (A I D : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (d Dint R : ℕ)
    (p reserveDensity C b : ℝ≥0) : Prop where
  strong : IsReserveStronglyWellDistributed law W next
    (fun z ↦ I z.1) (fun z ↦ D z.1 ∪
      relativeReserveProtectedTotal I D z.1 z.2)
    (relativeReserveProtectedRootedReserve W i G bits I D)
    p reserveDensity C b
  links : law.SupportedOn fun z ↦
    IsIntermediateLinkState (G z.1) (W.U i.succ) (A z.1)
        (I z.1) (D z.1) (relativeReserveProtectedTotal I D z.1 z.2)
        (relativeReserveProtectedRootedLinks W i F G A I D bits z) ∧
      (∀ o, (relativeReserveProtectedRootedLinks W i F G A I D bits z o).center =
        outsideVertexEmbedding (W.U i.succ) o) ∧
      (∀ o, outsideVertexEmbedding (W.U i.succ) o ∉ W.U i.succ) ∧
      (∀ o, (relativeReserveProtectedRootedLinks W i F G A I D bits z o).left ⊆
        W.U i.succ) ∧
      (∀ o, (relativeReserveProtectedRootedLinks W i F G A I D bits z o).right ⊆
        W.U i.succ) ∧
      (∀ o, (relativeReserveProtectedRootedLinks W i F G A I D bits z o).SpokesIn
        (relativeReserveProtectedRootedReserve W i G bits I D z))
  structural : law.SupportedOn fun z ↦
    ConsistsOfTriangles (G z.1) (A z.1) ∧
      G z.1 ≤ leaveGraph (I z.1 ∪ D z.1) ∧
      IsPackingOn (I z.1 ∪ (D z.1 ∪
        relativeReserveProtectedTotal I D z.1 z.2)) ∧
      AvoidsForbidden (I z.1 ∪ (D z.1 ∪
        relativeReserveProtectedTotal I D z.1 z.2)) F ∧
      NewRootedActiveCapsGoodIn F (I z.1 ∪ D z.1) z.2.2.chosen
        (A z.1) (W.U i.succ) R ∧
      (∀ T ∈ A z.1, ¬ CompletesForbidden F (I z.1 ∪ D z.1) T)
  outcome : law.SupportedOn fun z ↦
    LocalizedNewRawResidualInternalOutcomeGood W i F
      (fun z : Omega × FiniteLaw.TimedState (GreedyStateOn V) n ↦ G z.1)
      (relativeReserveProtectedAint A I D)
      (fun z ↦ I z.1 ∪ D z.1)
      (relativeReserveProtectedP0 I D)
      (fun z ↦ bits z.1) Dint R (z.1, z.2.1) z.2.2
  preliminaryCard : law.SupportedOn fun z ↦
    (relativeReserveProtectedPreliminaryAdded I D z.1 z.2.1).card ≤ n
  preliminaryAtMostOne : law.SupportedOn fun z ↦
    TrianglesMeetAtMostOne (W.U i.succ)
      (relativeReserveProtectedPreliminaryAdded I D z.1 z.2.1)
  incidence : law.SupportedOn fun z ↦ ∀ v : V, (scheduledEdgesAt
    (preliminaryResidualInternalEdges (G z.1) (W.U i.succ)
      (relativeReserveProtectedP0 I D (z.1, z.2.1))) v).card ≤ d
  accumulate : law.SupportedOn fun z ↦
    I z.1 ∪ (D z.1 ∪ relativeReserveProtectedTotal I D z.1 z.2) =
      z.2.2.chosen
  selected : law.SupportedOn fun z ↦
    relativeReserveProtectedTotal I D z.1 z.2 ⊆ A z.1
  disjoint : law.SupportedOn fun z ↦
    Disjoint (I z.1)
      (D z.1 ∪ relativeReserveProtectedTotal I D z.1 z.2)

structure RelativeReserveProtectedNewCappedRootedOutput
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell n : ℕ}
    (law : FiniteLaw (RelativeReserveProtectedCorrelatedSample Omega V n))
    (W : Vortex V ell) (next : Fin (ell + 1))
    (F : ForbiddenFamilyOn V) (i : Fin ell)
    (G : Omega → SimpleGraph V) (A I D : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (d Dint R : ℕ)
    (caps : V → ℕ) (p reserveDensity C b : ℝ≥0) : Prop
    extends RelativeReserveProtectedNewRootedOutput law W next F i G A I D
      bits d Dint R p reserveDensity C b where
  preliminaryCaps : law.SupportedOn fun z ↦
    LinkStarCapsGood caps
      (relativeReserveProtectedPreliminaryAdded I D z.1 z.2.1)

theorem RelativeReserveProtectedNewCorrelatedFacts.conditionOn_newRootedResidualLinks
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell}
    {level next : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool}
    {n Kpair Kglobal Kinc Delta delta Icut Dcut d Dint R : ℕ}
    {alphaPre etaPre : ℝ≥0}
    {pOld reserveDensityOld COld bOld p reserveDensity C b : ℝ≥0}
    (i : Fin ell)
    (hfacts : RelativeReserveProtectedNewCorrelatedFacts L W level next F i
      (W.U i.succ) G A I D bits I D n Kpair Kglobal Kinc Delta delta
      Icut Dcut d Dint R alphaPre etaPre
      pOld reserveDensityOld COld bOld p reserveDensity C b)
    {etaMaster xi : ℝ≥0} {h : ℕ}
    (hpoint : L.SupportedOn fun omega ↦
      IsMasterStagePointwiseGood W level F (G omega) (A omega)
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
    (htail : newLocalizedRootedTail V 1 kappa R q s < 1) :
    let K := relativeReserveProtectedCorrelatedKernel W i F (W.U i.succ)
      G A I D bits n Kpair Kglobal Kinc Delta delta Icut Dcut d Dint
    let J := L.jointBind K
    let RootGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
      relativeReserveProtectedNewRootGood F I D A (W.U i.succ) R
    ∃ hpos : 0 < J.probability RootGood,
      RelativeReserveProtectedNewRootedOutput
        (J.conditionOn RootGood hpos) W next F i G A I D bits d Dint R
        p reserveDensity ((2 * C) / (1 -
          newLocalizedRootedTail V 1 kappa R q s)) b ∧
      1 - newLocalizedRootedTail V 1 kappa R q s ≤
        J.probability RootGood := by
  dsimp only
  let K := relativeReserveProtectedCorrelatedKernel W i F (W.U i.succ)
    G A I D bits n Kpair Kglobal Kinc Delta delta Icut Dcut d Dint
  let J := L.jointBind K
  let total : RelativeReserveProtectedCorrelatedSample Omega V n →
      TripleSystemOn V := fun z ↦
    relativeReserveProtectedTotal I D z.1 z.2
  let Pold : Omega → TripleSystemOn V := fun omega ↦ I omega ∪ D omega
  let RootGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
    relativeReserveProtectedNewRootGood F I D A (W.U i.succ) R
  have hbad : J.probability (fun z ↦ ¬ RootGood z) ≤
      newLocalizedRootedTail V 1 kappa R q s := by
    simpa only [J, K, RootGood, relativeReserveProtectedNewRootGood,
      Pold, total] using
      L.jointBind_probability_not_newRootedActiveCapsGoodIn_le
        K (fun omega z ↦ relativeReserveProtectedTotal I D omega z)
        F Pold A (W.U i.succ)
        (fun _ ↦ alphaPre + etaPre * (Dint : ℝ≥0)⁻¹)
        1 kappa R hfamily hkappa
        (fun omega hmass Q _hQcard ↦ by
          simpa only [setWeight, prod_const, one_mul] using
            hfacts.combinedC4 omega hmass Q)
  have hlower : 1 - newLocalizedRootedTail V 1 kappa R q s ≤
      J.probability RootGood := by
    rw [J.probability_not RootGood] at hbad
    exact tsub_le_iff_tsub_le.mp hbad
  have hpos : 0 < J.probability RootGood :=
    (tsub_pos_iff_lt.mpr htail).trans_le hlower
  let Lc := J.conditionOn RootGood hpos
  have hden : 0 < 1 - newLocalizedRootedTail V 1 kappa R q s :=
    tsub_pos_iff_lt.mpr htail
  have hfactor : (2 * C) / J.probability RootGood ≤
      (2 * C) / (1 - newLocalizedRootedTail V 1 kappa R q s) :=
    div_le_div_of_nonneg_left zero_le hden hlower
  have hstrong0 := (hfacts.strong.conditionOn RootGood hpos).mono_factor hfactor
  have hstrong : IsReserveStronglyWellDistributed Lc W next
      (jointInitial I) (jointLater D (relativeReserveProtectedTotal I D))
      (fun z ↦ preliminaryAugmentedReserve (G z.1) (W.U i.succ)
        (reserveEdges (G z.1) (W.U i.succ) (bits z.1))
        (relativeReserveProtectedTotal I D z.1 z.2))
      p reserveDensity ((2 * C) /
        (1 - newLocalizedRootedTail V 1 kappa R q s)) b := by
    simpa only [Lc, J, K, RootGood] using hstrong0
  have hroot := J.conditionOn_supported RootGood hpos
  have houtcome := hfacts.newOutcome.conditionOn hpos
  have hpreliminaryCard := hfacts.preliminaryCard.conditionOn hpos
  have hpreliminaryAtMostOne := hfacts.preliminaryAtMostOne.conditionOn hpos
  have hincidence := hfacts.incidence.conditionOn hpos
  have haccumulate := hfacts.accumulate.conditionOn hpos
  have hselected := hfacts.selected.conditionOn hpos
  have hdisjoint := hfacts.disjoint.conditionOn hpos
  have hpacking := hfacts.packing.conditionOn hpos
  have havoids := hfacts.avoids.conditionOn hpos
  have hpointC := hpoint.jointBind_fst (kernel := K) |>.conditionOn hpos
  have hevenC := heven.jointBind_fst (kernel := K) |>.conditionOn hpos
  have hnewRoot : Lc.SupportedOn fun z ↦
      NewRootedActiveCapsGoodIn F (I z.1 ∪ D z.1) z.2.2.chosen
        (A z.1) (W.U i.succ) R := by
    intro z hz
    have hacc := haccumulate z hz
    have hr := hroot z hz
    simpa only [RootGood, relativeReserveProtectedNewRootGood,
      ← hacc, union_assoc] using hr
  have hsupport : Lc.SupportedOn fun z ↦
      True ∧
        LocalizedNewRawResidualInternalOutcomeGood W i F
          (fun z : Omega × FiniteLaw.TimedState (GreedyStateOn V) n ↦ G z.1)
          (relativeReserveProtectedAint A I D)
          (fun z ↦ I z.1 ∪ D z.1)
          (relativeReserveProtectedP0 I D) (fun z ↦ bits z.1)
          Dint R (z.1, z.2.1) z.2.2 ∧
        NewRootedActiveCapsGoodIn F (I z.1 ∪ D z.1) z.2.2.chosen
          (relativeReserveProtectedAint A I D (z.1, z.2.1))
          (W.U i.succ) R := by
    intro z hz
    refine ⟨trivial, houtcome z hz, ?_⟩
    exact (hnewRoot z hz).mono_available
      (pairSafeAvailable_subset_left (A z.1)
        (relativeReserveProtectedP0 I D (z.1, z.2.1)))
  have hlinks := FiniteLaw.SupportedOn.relativeNewCorrelatedRawInternalResidualLinks
    (W := W) (i := i) (F := F) (G := G) (A := A) (I := I) (D := D)
    (Aint := relativeReserveProtectedAint A I D)
    (Plegal := fun z ↦ I z.1 ∪ D z.1)
    (P0 := relativeReserveProtectedP0 I D) (bits := fun z ↦ bits z.1)
    (Dint := Dint) (R := R) (Good := fun _ ↦ True) (total := total)
    (sampled := fun omega ↦
      reserveEdges (G omega) (W.U i.succ) (bits omega))
    hsupport haccumulate hselected hdisjoint hpacking hevenC
    (fun z hz ↦ (hpointC z hz).2.2.2.2.1)
    (fun z hz ↦ (hpointC z hz).2.2.2.2.2.1)
  have hstruct : Lc.SupportedOn fun z ↦
      ConsistsOfTriangles (G z.1) (A z.1) ∧
        G z.1 ≤ leaveGraph (I z.1 ∪ D z.1) ∧
        IsPackingOn (I z.1 ∪ (D z.1 ∪ total z)) ∧
        AvoidsForbidden (I z.1 ∪ (D z.1 ∪ total z)) F ∧
        NewRootedActiveCapsGoodIn F (I z.1 ∪ D z.1) z.2.2.chosen
          (A z.1) (W.U i.succ) R ∧
        (∀ T ∈ A z.1,
          ¬ CompletesForbidden F (I z.1 ∪ D z.1) T) := by
    intro z hz
    exact ⟨(hpointC z hz).2.2.2.2.2.1,
      (hpointC z hz).2.2.2.2.1, hpacking z hz, havoids z hz,
      hnewRoot z hz, (hpointC z hz).2.2.2.2.2.2⟩
  refine ⟨hpos, ?_, hlower⟩
  refine ⟨hstrong, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hs := hlinks z hz
    have hreserveEq :
        relativeReserveProtectedRootedReserve W i G bits I D =
          (fun y : RelativeReserveProtectedCorrelatedSample Omega V n ↦
            preliminaryAugmentedReserve (G y.1) (W.U i.succ)
              (reserveEdges (G y.1) (W.U i.succ) (bits y.1))
              (relativeReserveProtectedTotal I D y.1 y.2)) := rfl
    simpa only [total,
      relativeReserveProtected_internalStageFamily_eq_total,
      hreserveEq, relativeReserveProtectedRootedLinks] using hs
  · simpa only [total] using hstruct
  · simpa only [Lc, J, K] using houtcome
  · simpa only [Lc, J, K] using hpreliminaryCard
  · simpa only [Lc, J, K] using hpreliminaryAtMostOne
  · simpa only [Lc, J, K] using hincidence
  · simpa only [Lc, J, K, total] using haccumulate
  · simpa only [Lc, J, K, total] using hselected
  · simpa only [Lc, J, K, total] using hdisjoint

/-- Also impose the preliminary vertex-star caps.  The two bad events are
controlled in the original correlated law and combined by a union bound. -/
theorem RelativeReserveProtectedNewCorrelatedFacts.conditionOn_newRootedResidualLinks_and_preliminaryCaps
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell}
    {level next : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool}
    {n Kpair Kglobal Kinc Delta delta Icut Dcut d Dint R : ℕ}
    {alphaPre etaPre : ℝ≥0}
    {pOld reserveDensityOld COld bOld p reserveDensity C b : ℝ≥0}
    (i : Fin ell)
    (hfacts : RelativeReserveProtectedNewCorrelatedFacts L W level next F i
      (W.U i.succ) G A I D bits I D n Kpair Kglobal Kinc Delta delta
      Icut Dcut d Dint R alphaPre etaPre
      pOld reserveDensityOld COld bOld p reserveDensity C b)
    {etaMaster xi : ℝ≥0} {h : ℕ}
    (hpoint : L.SupportedOn fun omega ↦
      IsMasterStagePointwiseGood W level F (G omega) (A omega)
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
    (hpreC4 : ∀ Q : TripleSystemOn V,
      (L.jointBind (relativeReserveProtectedCorrelatedKernel W i F
        (W.U i.succ) G A I D bits n Kpair Kglobal Kinc Delta delta
        Icut Dcut d Dint)).probability (fun z ↦ Q ⊆
          relativeReserveProtectedPreliminaryAdded I D z.1 z.2.1) ≤
        alphaPre ^ Q.card)
    (htailPre : ∑ v : V,
      ((ambientTriplesThrough v).powersetCard (caps v)).card *
        alphaPre ^ caps v ≤ epsilonPre)
    (hbudget : epsilonPre +
      newLocalizedRootedTail V 1 kappa R q s < 1) :
    let K := relativeReserveProtectedCorrelatedKernel W i F (W.U i.succ)
      G A I D bits n Kpair Kglobal Kinc Delta delta Icut Dcut d Dint
    let J := L.jointBind K
    let RootGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
      relativeReserveProtectedNewRootGood F I D A (W.U i.succ) R
    let PreGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
      relativeReserveProtectedPreliminaryCapsGood caps I D
    ∃ hrootPos : 0 < J.probability RootGood,
      ∃ hprePos : 0 < (J.conditionOn RootGood hrootPos).probability PreGood,
        RelativeReserveProtectedNewCappedRootedOutput
          ((J.conditionOn RootGood hrootPos).conditionOn PreGood hprePos)
          W next F i G A I D bits d Dint R caps p reserveDensity
          (((2 * C) / (1 -
              newLocalizedRootedTail V 1 kappa R q s)) /
            (1 - (epsilonPre +
              newLocalizedRootedTail V 1 kappa R q s))) b := by
  dsimp only
  let K := relativeReserveProtectedCorrelatedKernel W i F (W.U i.succ)
    G A I D bits n Kpair Kglobal Kinc Delta delta Icut Dcut d Dint
  let J := L.jointBind K
  let RootGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
    relativeReserveProtectedNewRootGood F I D A (W.U i.succ) R
  let PreGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
    relativeReserveProtectedPreliminaryCapsGood caps I D
  let BothGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
    fun z ↦ RootGood z ∧ PreGood z
  have htailRoot : newLocalizedRootedTail V 1 kappa R q s < 1 :=
    lt_of_le_of_lt (le_add_left (le_refl _)) hbudget
  obtain ⟨hrootPos, houtRoot, _hlowerRoot⟩ :=
    hfacts.conditionOn_newRootedResidualLinks i hpoint heven hfamily
      kappa hkappa htailRoot
  let Lroot := J.conditionOn RootGood hrootPos
  have hpreBad : J.probability (fun z ↦ ¬ PreGood z) ≤ epsilonPre := by
    apply probability_not_linkStarCapsGood_selected_le J
      (fun z ↦
        relativeReserveProtectedPreliminaryAdded I D z.1 z.2.1)
      caps alphaPre epsilonPre
    · intro Q
      simpa only [J, K, PreGood] using hpreC4 Q
    · exact htailPre
  have hrootBad : J.probability (fun z ↦ ¬ RootGood z) ≤
      newLocalizedRootedTail V 1 kappa R q s := by
    let Pold : Omega → TripleSystemOn V := fun omega ↦ I omega ∪ D omega
    simpa only [J, K, RootGood, relativeReserveProtectedNewRootGood,
      Pold] using
      L.jointBind_probability_not_newRootedActiveCapsGoodIn_le
        K (fun omega z ↦ relativeReserveProtectedTotal I D omega z)
        F Pold A (W.U i.succ)
        (fun _ ↦ alphaPre + etaPre * (Dint : ℝ≥0)⁻¹)
        1 kappa R hfamily hkappa
        (fun omega hmass Q _hQcard ↦ by
          simpa only [setWeight, prod_const, one_mul] using
            hfacts.combinedC4 omega hmass Q)
  have hbothBad : J.probability (fun z ↦ ¬ BothGood z) ≤
      epsilonPre + newLocalizedRootedTail V 1 kappa R q s := by
    calc
      J.probability (fun z ↦ ¬ BothGood z) =
          J.probability (fun z ↦ ¬ RootGood z ∨ ¬ PreGood z) := by
        congr 1
        funext z
        simp only [BothGood, not_and_or]
      _ ≤ J.probability (fun z ↦ ¬ RootGood z) +
          J.probability (fun z ↦ ¬ PreGood z) :=
        J.probability_or_le _ _
      _ ≤ epsilonPre + newLocalizedRootedTail V 1 kappa R q s := by
        simpa only [add_comm] using add_le_add hrootBad hpreBad
  have hbothLower :
      1 - (epsilonPre + newLocalizedRootedTail V 1 kappa R q s) ≤
        J.probability BothGood := by
    rw [J.probability_not BothGood] at hbothBad
    exact tsub_le_iff_tsub_le.mp hbothBad
  have hbothPos : 0 < J.probability BothGood :=
    (tsub_pos_iff_lt.mpr hbudget).trans_le hbothLower
  have hprePos : 0 < Lroot.probability PreGood := by
    rw [J.conditionOn_probability RootGood PreGood hrootPos]
    apply div_pos
    · simpa only [BothGood] using hbothPos
    · exact hrootPos
  refine ⟨hrootPos, hprePos, ?_⟩
  have hpreLower :
      1 - (epsilonPre + newLocalizedRootedTail V 1 kappa R q s) ≤
        Lroot.probability PreGood := by
    rw [J.conditionOn_probability RootGood PreGood hrootPos]
    apply (le_div_iff₀ hrootPos).2
    calc
      (1 - (epsilonPre + newLocalizedRootedTail V 1 kappa R q s)) *
          J.probability RootGood ≤
          (1 - (epsilonPre + newLocalizedRootedTail V 1 kappa R q s)) * 1 := by
        gcongr
        exact J.probability_le_one RootGood
      _ = 1 - (epsilonPre + newLocalizedRootedTail V 1 kappa R q s) :=
        mul_one _
      _ ≤ J.probability (fun z ↦ RootGood z ∧ PreGood z) := by
        simpa only [BothGood] using hbothLower
  have hden : 0 <
      1 - (epsilonPre + newLocalizedRootedTail V 1 kappa R q s) :=
    tsub_pos_iff_lt.mpr hbudget
  have hfactor :
      ((2 * C) / (1 - newLocalizedRootedTail V 1 kappa R q s)) /
          Lroot.probability PreGood ≤
        ((2 * C) / (1 - newLocalizedRootedTail V 1 kappa R q s)) /
          (1 - (epsilonPre +
            newLocalizedRootedTail V 1 kappa R q s)) :=
    div_le_div_of_nonneg_left zero_le hden hpreLower
  have hstrong := (houtRoot.strong.conditionOn PreGood hprePos).mono_factor
    hfactor
  let Lfinal := Lroot.conditionOn PreGood hprePos
  have hrooted : RelativeReserveProtectedNewRootedOutput Lfinal W next F i
      G A I D bits d Dint R p reserveDensity
      (((2 * C) / (1 - newLocalizedRootedTail V 1 kappa R q s)) /
        (1 - (epsilonPre +
          newLocalizedRootedTail V 1 kappa R q s))) b := by
    refine ⟨hstrong, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact houtRoot.links.conditionOn hprePos
    · exact houtRoot.structural.conditionOn hprePos
    · exact houtRoot.outcome.conditionOn hprePos
    · exact houtRoot.preliminaryCard.conditionOn hprePos
    · exact houtRoot.preliminaryAtMostOne.conditionOn hprePos
    · exact houtRoot.incidence.conditionOn hprePos
    · exact houtRoot.accumulate.conditionOn hprePos
    · exact houtRoot.selected.conditionOn hprePos
    · exact houtRoot.disjoint.conditionOn hprePos
  exact ⟨hrooted, Lroot.conditionOn_supported PreGood hprePos⟩

end

end Erdos207
