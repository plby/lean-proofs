/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RelativeReserveProtectedSparseRooted
import ErdosProblems.Erdos207.RelativeReserveProtectedNewCorrelatedRooted

/-! # Sparse-reserve output with newly activated rooted caps -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

structure RelativeReserveProtectedNewSparseRootedOutput
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell n : ℕ}
    (law : FiniteLaw (RelativeReserveProtectedCorrelatedSample Omega V n))
    (W : Vortex V ell) (next : Fin (ell + 1))
    (F : ForbiddenFamilyOn V) (i : Fin ell)
    (G : Omega → SimpleGraph V) (A I D : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (d Dint R : ℕ)
    (caps : V → ℕ) (dCross mLink DLink CLink : ℕ)
    (p reserveDensity C b : ℝ≥0) : Prop
    extends RelativeReserveProtectedNewCappedRootedOutput law W next F i
      G A I D bits d Dint R caps p reserveDensity C b where
  preliminaryProtected : law.SupportedOn fun z ↦
    relativeReserveProtectedPreliminaryAdded I D z.1 z.2.1 ⊆
      reserveProtectedAvailable
        (reserveEdges (G z.1) (W.U i.succ) (bits z.1)) (A z.1)
  residualOuterIncidence : law.SupportedOn fun z ↦
    relativeReserveProtectedResidualOuterIncidenceGood W i G bits I D
      dCross z
  sampledLinkBounds : law.SupportedOn fun z ↦
    ReserveSampledLinkBoundsGood (G z.1) (A z.1) (W.U i.succ)
      mLink DLink CLink (bits z.1)

theorem RelativeReserveProtectedNewCorrelatedFacts.conditionOn_newSparseRootedResidualLinks
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell}
    {level next : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool}
    {n Kpair Kglobal Kinc Delta delta Icut Dcut d a Dint cutoff R : ℕ}
    {alphaPre etaPre : ℝ≥0}
    {pOld reserveDensityOld COld bOld p reserveDensity C b : ℝ≥0}
    (i : Fin ell)
    (hfacts : RelativeReserveProtectedNewCorrelatedFacts L W level next F i
      (W.U i.succ) G A I D bits I D n Kpair Kglobal Kinc Delta delta
      Icut Dcut d Dint R alphaPre etaPre
      pOld reserveDensityOld COld bOld p reserveDensity C b)
    (P : RelativeReserveProtectedPreliminaryFacts L F (W.U i.succ)
      G A I D bits n Kpair Kglobal Kinc Delta delta Icut Dcut d a Dint
      cutoff alphaPre etaPre)
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
      newLocalizedRootedTail V 1 kappa R q s + epsilonCross < 1) :
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
        RelativeReserveProtectedNewSparseRootedOutput
          ((J.conditionOn RootGood hrootPos).conditionOn RestGood hrestPos)
          W next F i G A I D bits d Dint R caps dCross
          mLink DLink CLink p reserveDensity
          (((2 * C) /
              (1 - newLocalizedRootedTail V 1 kappa R q s)) /
            (1 - (epsilonPre +
              newLocalizedRootedTail V 1 kappa R q s + epsilonCross))) b := by
  classical
  dsimp only
  let Kpre := relativeReserveProtectedPreliminaryKernel n F (W.U i.succ)
    G A I D bits Kpair Kglobal Kinc Delta delta Icut Dcut d
  let K := relativeReserveProtectedCorrelatedKernel W i F (W.U i.succ)
    G A I D bits n Kpair Kglobal Kinc Delta delta Icut Dcut d Dint
  let J := L.jointBind K
  let RootGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
    relativeReserveProtectedNewRootGood F I D A (W.U i.succ) R
  let PreGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
    relativeReserveProtectedPreliminaryCapsGood caps I D
  let CrossGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
    relativeReserveProtectedResidualOuterIncidenceGood W i G bits I D dCross
  let RestGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
    fun z ↦ PreGood z ∧ CrossGood z
  let AllGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
    fun z ↦ RootGood z ∧ RestGood z
  have htailRoot : newLocalizedRootedTail V 1 kappa R q s < 1 := by
    exact lt_of_le_of_lt
      (le_trans (le_add_left (le_refl _)) (le_add_right (le_refl _)))
      hbudget
  obtain ⟨hrootPos, houtRoot, _hlowerRoot⟩ :=
    hfacts.conditionOn_newRootedResidualLinks i hpoint heven hfamily
      kappa hkappa htailRoot
  let Lroot := J.conditionOn RootGood hrootPos
  have hpreC4 := P.probability_correlated_preliminary_subset_le (W := W) i
  have hpreBad : J.probability (fun z ↦ ¬ PreGood z) ≤ epsilonPre := by
    apply probability_not_linkStarCapsGood_selected_le J
      (fun z ↦ relativeReserveProtectedPreliminaryAdded I D z.1 z.2.1)
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
  have hcrossBad : J.probability (fun z ↦ ¬ CrossGood z) ≤
      epsilonCross := by
    simpa only [J, K, CrossGood] using
      P.probability_correlated_not_residualOuterIncidenceGood_le
        i dCross htailCross
  have hallBad : J.probability (fun z ↦ ¬ AllGood z) ≤
      epsilonPre + newLocalizedRootedTail V 1 kappa R q s +
        epsilonCross := by
    calc
      J.probability (fun z ↦ ¬ AllGood z) =
          J.probability (fun z ↦
            ¬ RootGood z ∨ ¬ PreGood z ∨ ¬ CrossGood z) := by
        congr 1
        funext z
        simp only [AllGood, RestGood, not_and_or, or_assoc]
      _ ≤ J.probability (fun z ↦ ¬ RootGood z) +
          J.probability (fun z ↦ ¬ PreGood z) +
          J.probability (fun z ↦ ¬ CrossGood z) :=
        J.probability_or_or_le _ _ _
      _ ≤ newLocalizedRootedTail V 1 kappa R q s + epsilonPre +
          epsilonCross := add_le_add (add_le_add hrootBad hpreBad) hcrossBad
      _ = epsilonPre + newLocalizedRootedTail V 1 kappa R q s +
          epsilonCross := by
        rw [add_comm (newLocalizedRootedTail V 1 kappa R q s) epsilonPre]
  have hallLower :
      1 - (epsilonPre + newLocalizedRootedTail V 1 kappa R q s +
        epsilonCross) ≤ J.probability AllGood := by
    rw [J.probability_not AllGood] at hallBad
    exact tsub_le_iff_tsub_le.mp hallBad
  have hallPos : 0 < J.probability AllGood :=
    (tsub_pos_iff_lt.mpr hbudget).trans_le hallLower
  have hrestPos : 0 < Lroot.probability RestGood := by
    rw [J.conditionOn_probability RootGood RestGood hrootPos]
    apply div_pos
    · simpa only [AllGood] using hallPos
    · exact hrootPos
  refine ⟨hrootPos, hrestPos, ?_⟩
  have hrestLower :
      1 - (epsilonPre + newLocalizedRootedTail V 1 kappa R q s +
        epsilonCross) ≤ Lroot.probability RestGood := by
    rw [J.conditionOn_probability RootGood RestGood hrootPos]
    apply (le_div_iff₀ hrootPos).2
    calc
      (1 - (epsilonPre + newLocalizedRootedTail V 1 kappa R q s +
          epsilonCross)) * J.probability RootGood ≤
          (1 - (epsilonPre + newLocalizedRootedTail V 1 kappa R q s +
            epsilonCross)) * 1 := by
        gcongr
        exact J.probability_le_one RootGood
      _ = 1 - (epsilonPre + newLocalizedRootedTail V 1 kappa R q s +
          epsilonCross) := mul_one _
      _ ≤ J.probability (fun z ↦ RootGood z ∧ RestGood z) := by
        simpa only [AllGood] using hallLower
  have hden : 0 <
      1 - (epsilonPre + newLocalizedRootedTail V 1 kappa R q s +
        epsilonCross) := tsub_pos_iff_lt.mpr hbudget
  have hfactor :
      ((2 * C) / (1 - newLocalizedRootedTail V 1 kappa R q s)) /
          Lroot.probability RestGood ≤
        ((2 * C) / (1 - newLocalizedRootedTail V 1 kappa R q s)) /
          (1 - (epsilonPre + newLocalizedRootedTail V 1 kappa R q s +
            epsilonCross)) :=
    div_le_div_of_nonneg_left zero_le hden hrestLower
  have hstrong := (houtRoot.strong.conditionOn RestGood hrestPos).mono_factor
    hfactor
  let Lfinal := Lroot.conditionOn RestGood hrestPos
  have hrooted : RelativeReserveProtectedNewRootedOutput Lfinal W next F i
      G A I D bits d Dint R p reserveDensity
      (((2 * C) / (1 - newLocalizedRootedTail V 1 kappa R q s)) /
        (1 - (epsilonPre + newLocalizedRootedTail V 1 kappa R q s +
          epsilonCross))) b := by
    refine ⟨hstrong, houtRoot.links.conditionOn hrestPos,
      houtRoot.structural.conditionOn hrestPos,
      houtRoot.outcome.conditionOn hrestPos,
      houtRoot.preliminaryCard.conditionOn hrestPos,
      houtRoot.preliminaryAtMostOne.conditionOn hrestPos,
      houtRoot.incidence.conditionOn hrestPos,
      houtRoot.accumulate.conditionOn hrestPos,
      houtRoot.selected.conditionOn hrestPos,
      houtRoot.disjoint.conditionOn hrestPos⟩
  have hrestSupport : Lfinal.SupportedOn RestGood :=
    Lroot.conditionOn_supported RestGood hrestPos
  have hpreSupport : Lfinal.SupportedOn PreGood := fun z hz ↦
    (hrestSupport z hz).1
  have hcrossSupport : Lfinal.SupportedOn CrossGood := fun z hz ↦
    (hrestSupport z hz).2
  have hpreProtectedJ : J.SupportedOn fun z ↦
      relativeReserveProtectedPreliminaryAdded I D z.1 z.2.1 ⊆
        reserveProtectedAvailable
          (reserveEdges (G z.1) (W.U i.succ) (bits z.1)) (A z.1) := by
    intro z hz
    have hm := (FiniteLaw.jointBind_mass_pos_iff L K z.1 z.2).mp hz
    have hm' := (FiniteLaw.jointBind_mass_pos_iff (Kpre z.1)
      (fun xi ↦ relativeReserveProtectedInternalKernel W i F G A I D
        bits Dint (z.1, xi)) z.2.1 z.2.2).mp (by
          simpa only [K, relativeReserveProtectedCorrelatedKernel, Kpre]
            using hm.2)
    apply P.protectedAvailable (z.1, z.2.1)
    exact (FiniteLaw.jointBind_mass_pos_iff L Kpre z.1 z.2.1).mpr
      ⟨hm.1, hm'.1⟩
  have hpreProtected :=
    (hpreProtectedJ.conditionOn hrootPos).conditionOn hrestPos
  have hsampledJ : J.SupportedOn fun z ↦
      ReserveSampledLinkBoundsGood (G z.1) (A z.1) (W.U i.succ)
        mLink DLink CLink (bits z.1) := by
    exact hsampledLinks.jointBind_fst
  have hsampled := (hsampledJ.conditionOn hrootPos).conditionOn hrestPos
  refine ⟨⟨hrooted, ?_⟩, hpreProtected, hcrossSupport, hsampled⟩
  intro z hz
  exact hpreSupport z hz

end

end Erdos207
