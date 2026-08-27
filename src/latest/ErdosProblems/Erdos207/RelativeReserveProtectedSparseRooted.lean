/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RelativeReserveProtectedCorrelatedRooted
import ErdosProblems.Erdos207.ConditionedCompressedTypicalProtectedReserveStage

/-!
# Sparse-reserve rooted output

The preliminary mixed product law also makes the nonsampled residual
crossing star small at every outside vertex.  We condition on that event
together with the preliminary vertex-star cap after the rooted conditioning.
The resulting output retains the sampled-link estimates and the fact that
the preliminary family never covers a sampled reserve edge.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def relativeReserveProtectedResidualOuterIncidenceGood
    {Omega V : Type*} [Fintype V] [DecidableEq V] {ell n : ℕ}
    (W : Vortex V ell) (i : Fin ell)
    (G : Omega → SimpleGraph V) (bits : Omega → Sym2 V → Bool)
    (I D : Omega → TripleSystemOn V) (dCross : ℕ)
    (z : RelativeReserveProtectedCorrelatedSample Omega V n) : Prop :=
  ∀ center : V,
    (outerIncidentEdges
        (reserveProtectedOuterGraph (G z.1) (W.U i.succ)
          (reserveEdges (G z.1) (W.U i.succ) (bits z.1)))
        (W.U i.succ) center ∩
      preliminaryResidualOuterEdges
        (reserveProtectedOuterGraph (G z.1) (W.U i.succ)
          (reserveEdges (G z.1) (W.U i.succ) (bits z.1)))
        (W.U i.succ) z.2.1.2.chosen).card ≤ dCross

/-- The rooted/capped output strengthened by exactly the support facts used
to compare an actual residual link with its sampled-reserve approximation.
-/
structure RelativeReserveProtectedSparseRootedOutput
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell n : ℕ}
    (law : FiniteLaw (RelativeReserveProtectedCorrelatedSample Omega V n))
    (W : Vortex V ell) (next : Fin (ell + 1))
    (F : ForbiddenFamilyOn V) (i : Fin ell)
    (G : Omega → SimpleGraph V) (A I D : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (d Dint R : ℕ)
    (caps : V → ℕ) (dCross mLink DLink CLink : ℕ)
    (p reserveDensity C b : ℝ≥0) : Prop
    extends RelativeReserveProtectedCappedRootedOutput law W next F i
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

/-- The correlated internal sample does not alter the probability of a
residual-outer incidence event determined by the preliminary sample. -/
theorem RelativeReserveProtectedPreliminaryFacts.probability_correlated_not_residualOuterIncidenceGood_le
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool}
    {n Kpair Kglobal Kinc Delta delta Icut Dcut d a Dint cutoff : ℕ}
    {alphaPre etaPre epsilonCross : ℝ≥0}
    (i : Fin ell)
    (P : RelativeReserveProtectedPreliminaryFacts L F (W.U i.succ)
      G A I D bits n Kpair Kglobal Kinc Delta delta Icut Dcut d a Dint
      cutoff alphaPre etaPre)
    (dCross : ℕ)
    (htailCross : ∀ omega, 0 < L.mass omega →
      ∑ center : V,
        ((outerIncidentEdges
          (reserveProtectedOuterGraph (G omega) (W.U i.succ)
            (reserveEdges (G omega) (W.U i.succ) (bits omega)))
          (W.U i.succ) center).powersetCard (dCross + 1)).card *
            etaPre ^ (dCross + 1) ≤ epsilonCross) :
    (L.jointBind (relativeReserveProtectedCorrelatedKernel W i F
      (W.U i.succ) G A I D bits n Kpair Kglobal Kinc Delta delta
      Icut Dcut d Dint)).probability
        (fun z ↦ ¬ relativeReserveProtectedResidualOuterIncidenceGood
          W i G bits I D dCross z) ≤ epsilonCross := by
  let U := W.U i.succ
  let Kpre := relativeReserveProtectedPreliminaryKernel n F U G A I D bits
    Kpair Kglobal Kinc Delta delta Icut Dcut d
  let Kint := relativeReserveProtectedInternalKernel (n := n)
    W i F G A I D bits Dint
  let BadPre : Omega → FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun omega xi ↦ ∃ center : V,
      dCross + 1 ≤
        (outerIncidentEdges
            (reserveProtectedOuterGraph (G omega) U
              (reserveEdges (G omega) U (bits omega))) U center ∩
          preliminaryResidualOuterEdges
            (reserveProtectedOuterGraph (G omega) U
              (reserveEdges (G omega) U (bits omega))) U
            xi.2.chosen).card
  have hpoint : ∀ omega, 0 < L.mass omega →
      (Kpre omega).probability (BadPre omega) ≤ epsilonCross := by
    intro omega hmass
    let GP := reserveProtectedOuterGraph (G omega) U
      (reserveEdges (G omega) U (bits omega))
    let residual : FiniteLaw.TimedState (GreedyStateOn V) n →
        Finset (Sym2 V) := fun xi ↦
      preliminaryResidualOuterEdges GP U xi.2.chosen
    have hmixed : ∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
        (Kpre omega).probability (fun xi ↦
          Q ⊆ relativeReserveProtectedPreliminaryAdded I D omega xi ∧
            E ⊆ residual xi) ≤
          alphaPre ^ Q.card * etaPre ^ E.card + 0 := by
      intro Q E
      simpa only [Kpre, residual, GP, U, add_zero] using
        P.outerProduct omega hmass Q E
    have hraw := (Kpre omega).probability_exists_large_residualOuter_incidence_le
      GP U (relativeReserveProtectedPreliminaryAdded I D omega) residual
        alphaPre etaPre 0 (dCross + 1) hmixed
    have heq : (Kpre omega).probability (BadPre omega) =
        (Kpre omega).probability (fun xi ↦ ∃ center : V,
          dCross + 1 ≤
            (outerIncidentEdges GP U center ∩ residual xi).card) := by
      congr 1
    rw [heq]
    exact hraw.trans (by
      simpa only [add_zero, GP, U] using htailCross omega hmass)
  have hbound := L.jointBind_jointBind_probability_snd_fst_le_on_support
    Kpre (fun omega xi ↦ Kint (omega, xi)) BadPre epsilonCross hpoint
  change (L.jointBind (fun omega ↦
    (Kpre omega).jointBind (fun xi ↦ Kint (omega, xi)))).probability
      (fun z ↦ ¬ relativeReserveProtectedResidualOuterIncidenceGood
        W i G bits I D dCross z) ≤ epsilonCross
  have hevent : (fun z : RelativeReserveProtectedCorrelatedSample Omega V n ↦
      ¬ relativeReserveProtectedResidualOuterIncidenceGood
        W i G bits I D dCross z) =
      (fun z ↦ BadPre z.1 z.2.1) := by
    funext z
    apply propext
    simp only [relativeReserveProtectedResidualOuterIncidenceGood,
      BadPre, U, not_forall, not_le]
    constructor <;> rintro ⟨center, hcenter⟩ <;>
      exact ⟨center, by omega⟩
  rw [hevent]
  exact hbound

/-- Simultaneously impose the rooted caps, preliminary star caps, and the
small nonsampled residual-star event. -/
theorem RelativeReserveProtectedCorrelatedFacts.conditionOn_sparseRootedResidualLinks
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell}
    {level next : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool}
    {n Kpair Kglobal Kinc Delta delta Icut Dcut d a Dint cutoff R : ℕ}
    {pOld reserveDensityOld COld bOld p reserveDensity C b : ℝ≥0}
    (i : Fin ell)
    (hfacts : RelativeReserveProtectedCorrelatedFacts L W level next F i
      (W.U i.succ) G A I D bits I D n Kpair Kglobal Kinc Delta delta
      Icut Dcut d Dint R pOld reserveDensityOld COld bOld
      p reserveDensity C b)
    {alphaPre etaPre : ℝ≥0}
    (P : RelativeReserveProtectedPreliminaryFacts L F (W.U i.succ)
      G A I D bits n Kpair Kglobal Kinc Delta delta Icut Dcut d a Dint
      cutoff alphaPre etaPre)
    {etaMaster xi : ℝ≥0} {h : ℕ}
    (hpoint : L.SupportedOn fun omega ↦
      IsMasterStagePointwiseGood W level F (G omega) (A omega)
        (I omega) (D omega) pOld etaMaster xi h)
    (heven : L.SupportedOn fun omega ↦
      ∀ v : V, Even ((neighborsIn (G omega) univ v).card))
    {q : ℕ}
    (hC : 1 ≤ 2 * C)
    (hfamily : ∀ S ∈ F, S.card ≤ q)
    (hbroot : ∀ T : TripleSystemOn V, T.card ≤ q - 1 →
      b ≤ setWeight (masterUnionTriangleWeight W next p) T)
    (kappa : ℝ≥0)
    (hkappa : ∀ e : DistinctPair V,
      extensionWeight
          (fun z : LocalizedRootedThreatWitness V F e.1.1 e.1.2
            (W.U i.succ) ↦ localizedRootedThreatRemainder z)
          (masterUnionTriangleWeight W next p) ∅ ≤ kappa)
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
      strongLocalizedRootedFirstTail V (2 * C) kappa R q + epsilonCross < 1) :
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
        RelativeReserveProtectedSparseRootedOutput
          ((J.conditionOn RootGood hrootPos).conditionOn RestGood hrestPos)
          W next F i G A I D bits d Dint R caps dCross
          mLink DLink CLink p reserveDensity
          (((2 * C) /
              (1 - strongLocalizedRootedFirstTail V (2 * C) kappa R q)) /
            (1 - (epsilonPre +
              strongLocalizedRootedFirstTail V (2 * C) kappa R q + epsilonCross))) b := by
  classical
  dsimp only
  let Kpre := relativeReserveProtectedPreliminaryKernel n F (W.U i.succ)
    G A I D bits Kpair Kglobal Kinc Delta delta Icut Dcut d
  let K := relativeReserveProtectedCorrelatedKernel W i F (W.U i.succ)
    G A I D bits n Kpair Kglobal Kinc Delta delta Icut Dcut d Dint
  let J := L.jointBind K
  let RootGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
    relativeReserveProtectedRootGood W i F I D R
  let PreGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
    relativeReserveProtectedPreliminaryCapsGood caps I D
  let CrossGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
    relativeReserveProtectedResidualOuterIncidenceGood W i G bits I D dCross
  let RestGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
    fun z ↦ PreGood z ∧ CrossGood z
  let AllGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
    fun z ↦ RootGood z ∧ RestGood z
  have htailRoot : strongLocalizedRootedFirstTail V (2 * C) kappa R q < 1 := by
    exact lt_of_le_of_lt
      (le_trans (le_add_left (le_refl _)) (le_add_right (le_refl _)))
      hbudget
  obtain ⟨hrootPos, houtRoot, _hlowerRoot⟩ :=
    hfacts.conditionOn_rootedResidualLinks i hpoint heven hC hfamily
      hbroot kappa hkappa htailRoot
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
      strongLocalizedRootedFirstTail V (2 * C) kappa R q := by
    simpa only [J, K, RootGood, relativeReserveProtectedRootGood] using
      hfacts.strong.toStrong.probability_not_rootedActiveCapsGoodIn_le_firstMoment
        F (W.U i.succ) R hC hfamily hbroot kappa hkappa
  have hcrossBad : J.probability (fun z ↦ ¬ CrossGood z) ≤
      epsilonCross := by
    simpa only [J, K, CrossGood] using
      P.probability_correlated_not_residualOuterIncidenceGood_le
        i dCross htailCross
  have hallBad : J.probability (fun z ↦ ¬ AllGood z) ≤
      epsilonPre + strongLocalizedRootedFirstTail V (2 * C) kappa R q +
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
      _ ≤ strongLocalizedRootedFirstTail V (2 * C) kappa R q + epsilonPre +
          epsilonCross := add_le_add (add_le_add hrootBad hpreBad) hcrossBad
      _ = epsilonPre + strongLocalizedRootedFirstTail V (2 * C) kappa R q +
          epsilonCross := by
        rw [add_comm (strongLocalizedRootedFirstTail V (2 * C) kappa R q) epsilonPre]
  have hallLower :
      1 - (epsilonPre + strongLocalizedRootedFirstTail V (2 * C) kappa R q +
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
      1 - (epsilonPre + strongLocalizedRootedFirstTail V (2 * C) kappa R q +
        epsilonCross) ≤ Lroot.probability RestGood := by
    rw [J.conditionOn_probability RootGood RestGood hrootPos]
    apply (le_div_iff₀ hrootPos).2
    calc
      (1 - (epsilonPre + strongLocalizedRootedFirstTail V (2 * C) kappa R q +
          epsilonCross)) * J.probability RootGood ≤
          (1 - (epsilonPre + strongLocalizedRootedFirstTail V (2 * C) kappa R q +
            epsilonCross)) * 1 := by
        gcongr
        exact J.probability_le_one RootGood
      _ = 1 - (epsilonPre + strongLocalizedRootedFirstTail V (2 * C) kappa R q +
          epsilonCross) := mul_one _
      _ ≤ J.probability (fun z ↦ RootGood z ∧ RestGood z) := by
        simpa only [AllGood] using hallLower
  have hden : 0 <
      1 - (epsilonPre + strongLocalizedRootedFirstTail V (2 * C) kappa R q +
        epsilonCross) := tsub_pos_iff_lt.mpr hbudget
  have hfactor :
      ((2 * C) / (1 - strongLocalizedRootedFirstTail V (2 * C) kappa R q)) /
          Lroot.probability RestGood ≤
        ((2 * C) / (1 - strongLocalizedRootedFirstTail V (2 * C) kappa R q)) /
          (1 - (epsilonPre + strongLocalizedRootedFirstTail V (2 * C) kappa R q +
            epsilonCross)) :=
    div_le_div_of_nonneg_left zero_le hden hrestLower
  have hstrong := (houtRoot.strong.conditionOn RestGood hrestPos).mono_factor
    hfactor
  let Lfinal := Lroot.conditionOn RestGood hrestPos
  have hrooted : RelativeReserveProtectedRootedOutput Lfinal W next F i
      G A I D bits d Dint R p reserveDensity
      (((2 * C) / (1 - strongLocalizedRootedFirstTail V (2 * C) kappa R q)) /
        (1 - (epsilonPre + strongLocalizedRootedFirstTail V (2 * C) kappa R q +
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
