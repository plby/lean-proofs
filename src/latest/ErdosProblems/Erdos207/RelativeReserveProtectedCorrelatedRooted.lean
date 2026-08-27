/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RelativeReserveProtectedCorrelatedStage
import ErdosProblems.Erdos207.RelativeCorrelatedRootedResidualLinks
import ErdosProblems.Erdos207.MasterLinkStarConditioning

/-!
# Rooted residual links for a relative reserve-protected stage

This is the later-stage counterpart of `ReserveProtectedCorrelatedRooted`.
The old `I/D` split is retained both in the strong-distribution law and in
the residual-link state.  Root conditioning is applied to the accumulated
old-plus-new family, which the correlated stage identifies with the terminal
chosen family of the raw internal process.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

abbrev RelativeReserveProtectedCorrelatedSample
    (Omega V : Type*) [Fintype V] [DecidableEq V] (n : ℕ) :=
  Omega × (FiniteLaw.TimedState (GreedyStateOn V) n ×
    InternalEdgeGreedyStateOn V)

def relativeReserveProtectedRootedReserve
    {Omega V : Type*} [Fintype V] [DecidableEq V] {ell n : ℕ}
    (W : Vortex V ell) (i : Fin ell) (G : Omega → SimpleGraph V)
    (bits : Omega → Sym2 V → Bool) (I D : Omega → TripleSystemOn V)
    (z : RelativeReserveProtectedCorrelatedSample Omega V n) :
    Finset (Sym2 V) :=
  preliminaryAugmentedReserve (G z.1) (W.U i.succ)
    (reserveEdges (G z.1) (W.U i.succ) (bits z.1))
    (relativeReserveProtectedTotal I D z.1 z.2)

def relativeReserveProtectedRootedLinks
    {Omega V : Type*} [Fintype V] [DecidableEq V] {ell n : ℕ}
    (W : Vortex V ell) (i : Fin ell) (F : ForbiddenFamilyOn V)
    (G : Omega → SimpleGraph V) (A I D : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool)
    (z : RelativeReserveProtectedCorrelatedSample Omega V n) :
    {x : V // x ∉ W.U i.succ} → BipartiteLink V :=
  internalOutcomeResidualLinks (fun z ↦ G z.1) (W.U i.succ)
    (relativeReserveProtectedRootedReserve W i G bits I D) F
    (fun z ↦ A z.1) (fun z ↦ I z.1) (fun z ↦ D z.1)
    (fun z ↦ relativeReserveProtectedTotal I D z.1 z.2)
    (fun z ↦ z.2.2.chosen) z

/-- The rooted-cap event for a correlated later-stage sample. -/
def relativeReserveProtectedRootGood
    {Omega V : Type*} [Fintype V] [DecidableEq V] {ell n : ℕ}
    (W : Vortex V ell) (i : Fin ell)
    (F : ForbiddenFamilyOn V) (I D : Omega → TripleSystemOn V)
    (R : ℕ) (z : RelativeReserveProtectedCorrelatedSample Omega V n) : Prop :=
  RootedActiveCapsGoodIn F
    (jointInitial I z ∪ jointLater D
      (relativeReserveProtectedTotal I D) z) (W.U i.succ) R

/-- The preliminary vertex-star event for a correlated later-stage sample. -/
def relativeReserveProtectedPreliminaryCapsGood
    {Omega V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (caps : V → ℕ) (I D : Omega → TripleSystemOn V)
    (z : RelativeReserveProtectedCorrelatedSample Omega V n) : Prop :=
  LinkStarCapsGood caps
    (relativeReserveProtectedPreliminaryAdded I D z.1 z.2.1)

/-- The structural stage family produced by the raw internal state is
definitionally the correlated new difference, even away from the support of
the law.  This normalization is useful because the probabilistic law charges
exactly that new difference. -/
lemma relativeReserveProtected_internalStageFamily_eq_total
    {Omega V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (I D : Omega → TripleSystemOn V)
    (z : RelativeReserveProtectedCorrelatedSample Omega V n) :
    internalStageFamily (I z.1) (D z.1)
        (relativeReserveProtectedTotal I D z.1 z.2) z.2.2.chosen =
      relativeReserveProtectedTotal I D z.1 z.2 := by
  ext T
  simp only [internalStageFamily, relativeReserveProtectedTotal,
    preliminaryInternalCombinedAdded,
    relativeReserveProtectedInternalAdded,
    rawResidualInternalAdded, relativeReserveProtectedP0,
    relativeReserveProtectedPreliminaryAdded]
  aesop

/-- Complete output of the rooted later-stage construction.  It contains
exactly the support certificates consumed by the supported compressed
transition. -/
structure RelativeReserveProtectedRootedOutput
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
      RootedActiveCapsGoodIn F z.2.2.chosen (W.U i.succ) R
  outcome : law.SupportedOn fun z ↦
    LocalizedRawResidualInternalOutcomeGood W i F
      (fun z : Omega × FiniteLaw.TimedState (GreedyStateOn V) n ↦ G z.1)
      (relativeReserveProtectedAint A I D) (relativeReserveProtectedP0 I D)
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

/-- A rooted output together with a strict vertex-star cap on the
preliminary difference.  The latter is what turns sparse-reserve geometry
into a localized loss estimate. -/
structure RelativeReserveProtectedCappedRootedOutput
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell n : ℕ}
    (law : FiniteLaw (RelativeReserveProtectedCorrelatedSample Omega V n))
    (W : Vortex V ell) (next : Fin (ell + 1))
    (F : ForbiddenFamilyOn V) (i : Fin ell)
    (G : Omega → SimpleGraph V) (A I D : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (d Dint R : ℕ)
    (caps : V → ℕ) (p reserveDensity C b : ℝ≥0) : Prop
    extends RelativeReserveProtectedRootedOutput law W next F i G A I D
      bits d Dint R p reserveDensity C b where
  preliminaryCaps : law.SupportedOn fun z ↦
    LinkStarCapsGood caps
      (relativeReserveProtectedPreliminaryAdded I D z.1 z.2.1)

/-- Condition the sharp relative correlated stage on the rooted-cap event
and expose its canonical reserve-supported residual links. -/
theorem RelativeReserveProtectedCorrelatedFacts.conditionOn_rootedResidualLinks
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell}
    {level next : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool}
    {n Kpair Kglobal Kinc Delta delta Icut Dcut d Dint R : ℕ}
    {pOld reserveDensityOld COld bOld p reserveDensity C b : ℝ≥0}
    (i : Fin ell)
    (hfacts : RelativeReserveProtectedCorrelatedFacts L W level next F i
      (W.U i.succ) G A I D bits I D n Kpair Kglobal Kinc Delta delta
      Icut Dcut d Dint R pOld reserveDensityOld COld bOld
      p reserveDensity C b)
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
    (htail : strongLocalizedRootedFirstTail V (2 * C) kappa R q < 1) :
    let K := relativeReserveProtectedCorrelatedKernel W i F (W.U i.succ)
      G A I D bits n Kpair Kglobal Kinc Delta delta Icut Dcut d Dint
    let J := L.jointBind K
    let RootGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
      fun z ↦ RootedActiveCapsGoodIn F
        (jointInitial I z ∪
          jointLater D (relativeReserveProtectedTotal I D) z)
        (W.U i.succ) R
    ∃ hpos : 0 < J.probability RootGood,
      RelativeReserveProtectedRootedOutput
        (J.conditionOn RootGood hpos) W next F i G A I D bits d Dint R
        p reserveDensity
        ((2 * C) / (1 - strongLocalizedRootedFirstTail V (2 * C) kappa R q)) b ∧
      1 - strongLocalizedRootedFirstTail V (2 * C) kappa R q ≤
        J.probability RootGood := by
  dsimp only
  let K := relativeReserveProtectedCorrelatedKernel W i F (W.U i.succ)
    G A I D bits n Kpair Kglobal Kinc Delta delta Icut Dcut d Dint
  let J := L.jointBind K
  let total : RelativeReserveProtectedCorrelatedSample Omega V n →
      TripleSystemOn V := fun z ↦
    relativeReserveProtectedTotal I D z.1 z.2
  let RootGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
    fun z ↦ RootedActiveCapsGoodIn F
      (jointInitial I z ∪ jointLater D (relativeReserveProtectedTotal I D) z)
      (W.U i.succ) R
  have hbad : J.probability (fun z ↦ ¬ RootGood z) ≤
      strongLocalizedRootedFirstTail V (2 * C) kappa R q := by
    simpa only [J, K, RootGood] using
      hfacts.strong.toStrong.probability_not_rootedActiveCapsGoodIn_le_firstMoment
        F (W.U i.succ) R hC hfamily hbroot kappa hkappa
  have hlower0 : 1 - strongLocalizedRootedFirstTail V (2 * C) kappa R q ≤
      J.probability RootGood := by
    rw [J.probability_not RootGood] at hbad
    exact tsub_le_iff_tsub_le.mp hbad
  have hpos : 0 < J.probability RootGood :=
    (tsub_pos_iff_lt.mpr htail).trans_le hlower0
  let Lc := J.conditionOn RootGood hpos
  have hden : 0 <
      1 - strongLocalizedRootedFirstTail V (2 * C) kappa R q :=
    tsub_pos_iff_lt.mpr htail
  have hfactor : (2 * C) / J.probability RootGood ≤
      (2 * C) /
        (1 - strongLocalizedRootedFirstTail V (2 * C) kappa R q) :=
    div_le_div_of_nonneg_left zero_le hden hlower0
  have hstrong0 := (hfacts.strong.conditionOn RootGood hpos).mono_factor hfactor
  have hrootSupport0 : Lc.SupportedOn RootGood :=
    J.conditionOn_supported RootGood hpos
  have hstrong : IsReserveStronglyWellDistributed Lc W next
      (jointInitial I) (jointLater D (relativeReserveProtectedTotal I D))
      (fun z ↦ preliminaryAugmentedReserve (G z.1) (W.U i.succ)
        (reserveEdges (G z.1) (W.U i.succ) (bits z.1))
        (relativeReserveProtectedTotal I D z.1 z.2))
      p reserveDensity
      ((2 * C) /
        (1 - strongLocalizedRootedFirstTail V (2 * C) kappa R q)) b := by
    simpa only [Lc, J, K, RootGood] using hstrong0
  have hrootSupport : Lc.SupportedOn RootGood := by
    simpa only [Lc, J, K, RootGood] using
      hrootSupport0
  have hlower : 1 - strongLocalizedRootedFirstTail V (2 * C) kappa R q ≤
      J.probability RootGood := by
    simpa only [J, K, RootGood] using hlower0
  have houtcome := hfacts.outcome.conditionOn hpos
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
  have hsupport : Lc.SupportedOn fun z ↦
      True ∧
        LocalizedRawResidualInternalOutcomeGood W i F
          (fun z : Omega × FiniteLaw.TimedState (GreedyStateOn V) n ↦ G z.1)
          (relativeReserveProtectedAint A I D)
          (relativeReserveProtectedP0 I D) (fun z ↦ bits z.1)
          Dint R (z.1, z.2.1) z.2.2 ∧
        RootedActiveCapsGoodIn F z.2.2.chosen (W.U i.succ) R := by
    intro z hz
    refine ⟨trivial, houtcome z hz, ?_⟩
    rw [← haccumulate z hz]
    exact hrootSupport z hz
  have hlinks := FiniteLaw.SupportedOn.relativeCorrelatedRawInternalResidualLinks
    (W := W) (i := i) (F := F) (G := G) (A := A) (I := I) (D := D)
    (Aint := relativeReserveProtectedAint A I D)
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
        RootedActiveCapsGoodIn F z.2.2.chosen (W.U i.succ) R := by
    intro z hz
    exact ⟨(hpointC z hz).2.2.2.2.2.1,
      (hpointC z hz).2.2.2.2.1, hpacking z hz, havoids z hz,
      hsupport z hz |>.2.2⟩
  refine ⟨hpos, ?_, hlower⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hstrong
  · intro z hz
    have hz' : 0 < Lc.mass z := by
      simpa only [Lc, J, K, RootGood] using hz
    have hs := hlinks z hz'
    have hreserveEq :
        relativeReserveProtectedRootedReserve W i G bits I D =
          (fun y : RelativeReserveProtectedCorrelatedSample Omega V n ↦
            preliminaryAugmentedReserve (G y.1) (W.U i.succ)
              (reserveEdges (G y.1) (W.U i.succ) (bits y.1))
              (relativeReserveProtectedTotal I D y.1 y.2)) := rfl
    simpa only [total,
      relativeReserveProtected_internalStageFamily_eq_total,
      hreserveEq,
      relativeReserveProtectedRootedLinks] using hs
  · simpa only [total] using hstruct
  · simpa only [Lc, J, K] using houtcome
  · simpa only [Lc, J, K] using hpreliminaryCard
  · simpa only [Lc, J, K] using hpreliminaryAtMostOne
  · simpa only [Lc, J, K] using hincidence
  · simpa only [Lc, J, K, total] using haccumulate
  · simpa only [Lc, J, K, total] using hselected
  · simpa only [Lc, J, K, total] using hdisjoint

/-- Impose the preliminary vertex-star caps after the rooted conditioning.
The preliminary C4 tail and the rooted-threat tail are combined by a union
bound.  All structural certificates survive the second conditioning, while
the reserve-aware strong constant incurs only the displayed reciprocal
high-probability loss. -/
theorem RelativeReserveProtectedCorrelatedFacts.conditionOn_rootedResidualLinks_and_preliminaryCaps
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell}
    {level next : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool}
    {n Kpair Kglobal Kinc Delta delta Icut Dcut d Dint R : ℕ}
    {pOld reserveDensityOld COld bOld p reserveDensity C b : ℝ≥0}
    (i : Fin ell)
    (hfacts : RelativeReserveProtectedCorrelatedFacts L W level next F i
      (W.U i.succ) G A I D bits I D n Kpair Kglobal Kinc Delta delta
      Icut Dcut d Dint R pOld reserveDensityOld COld bOld
      p reserveDensity C b)
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
    (caps : V → ℕ) (alphaPre epsilonPre : ℝ≥0)
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
      strongLocalizedRootedFirstTail V (2 * C) kappa R q < 1) :
    ∃ hrootPos : 0 <
        (L.jointBind (relativeReserveProtectedCorrelatedKernel W i F
          (W.U i.succ) G A I D bits n Kpair Kglobal Kinc Delta delta
          Icut Dcut d Dint)).probability
            (relativeReserveProtectedRootGood W i F I D R),
      ∃ hprePos : 0 <
          ((L.jointBind (relativeReserveProtectedCorrelatedKernel W i F
            (W.U i.succ) G A I D bits n Kpair Kglobal Kinc Delta delta
            Icut Dcut d Dint)).conditionOn
              (relativeReserveProtectedRootGood W i F I D R) hrootPos).probability
                (relativeReserveProtectedPreliminaryCapsGood caps I D),
        RelativeReserveProtectedCappedRootedOutput
          (((L.jointBind (relativeReserveProtectedCorrelatedKernel W i F
            (W.U i.succ) G A I D bits n Kpair Kglobal Kinc Delta delta
            Icut Dcut d Dint)).conditionOn
              (relativeReserveProtectedRootGood W i F I D R) hrootPos).conditionOn
                (relativeReserveProtectedPreliminaryCapsGood caps I D)
                hprePos)
          W next F i G A I D bits
          d Dint R caps p reserveDensity
          (((2 * C) /
              (1 - strongLocalizedRootedFirstTail V (2 * C) kappa R q)) /
            (1 - (epsilonPre +
              strongLocalizedRootedFirstTail V (2 * C) kappa R q))) b := by
  let K := relativeReserveProtectedCorrelatedKernel W i F (W.U i.succ)
    G A I D bits n Kpair Kglobal Kinc Delta delta Icut Dcut d Dint
  let J := L.jointBind K
  let RootGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
    relativeReserveProtectedRootGood W i F I D R
  let PreGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
    relativeReserveProtectedPreliminaryCapsGood caps I D
  let BothGood : RelativeReserveProtectedCorrelatedSample Omega V n → Prop :=
    fun z ↦ RootGood z ∧ PreGood z
  have htailRoot : strongLocalizedRootedFirstTail V (2 * C) kappa R q < 1 :=
    lt_of_le_of_lt (le_add_left (le_refl _)) hbudget
  obtain ⟨hrootPos, houtRoot, _hlowerRoot⟩ :=
    hfacts.conditionOn_rootedResidualLinks i hpoint heven hC hfamily
      hbroot kappa hkappa htailRoot
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
      strongLocalizedRootedFirstTail V (2 * C) kappa R q := by
    simpa only [J, K, RootGood, relativeReserveProtectedRootGood] using
      hfacts.strong.toStrong.probability_not_rootedActiveCapsGoodIn_le_firstMoment
        F (W.U i.succ) R hC hfamily hbroot kappa hkappa
  have hbothBad : J.probability (fun z ↦ ¬ BothGood z) ≤
      epsilonPre + strongLocalizedRootedFirstTail V (2 * C) kappa R q := by
    calc
      J.probability (fun z ↦ ¬ BothGood z) =
          J.probability (fun z ↦ ¬ RootGood z ∨ ¬ PreGood z) := by
        congr 1
        funext z
        simp only [BothGood, not_and_or]
      _ ≤ J.probability (fun z ↦ ¬ RootGood z) +
          J.probability (fun z ↦ ¬ PreGood z) :=
        J.probability_or_le _ _
      _ ≤ epsilonPre + strongLocalizedRootedFirstTail V (2 * C) kappa R q := by
        simpa only [add_comm] using add_le_add hrootBad hpreBad
  have hbothLower :
      1 - (epsilonPre + strongLocalizedRootedFirstTail V (2 * C) kappa R q) ≤
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
      1 - (epsilonPre + strongLocalizedRootedFirstTail V (2 * C) kappa R q) ≤
        Lroot.probability PreGood := by
    rw [J.conditionOn_probability RootGood PreGood hrootPos]
    apply (le_div_iff₀ hrootPos).2
    calc
      (1 - (epsilonPre + strongLocalizedRootedFirstTail V (2 * C) kappa R q)) *
          J.probability RootGood ≤
          (1 - (epsilonPre +
            strongLocalizedRootedFirstTail V (2 * C) kappa R q)) * 1 := by
        gcongr
        exact J.probability_le_one RootGood
      _ = 1 - (epsilonPre +
          strongLocalizedRootedFirstTail V (2 * C) kappa R q) := mul_one _
      _ ≤ J.probability (fun z ↦ RootGood z ∧ PreGood z) := by
        simpa only [BothGood] using hbothLower
  have hden : 0 <
      1 - (epsilonPre + strongLocalizedRootedFirstTail V (2 * C) kappa R q) :=
    tsub_pos_iff_lt.mpr hbudget
  have hfactor :
      ((2 * C) / (1 - strongLocalizedRootedFirstTail V (2 * C) kappa R q)) /
          Lroot.probability PreGood ≤
        ((2 * C) / (1 - strongLocalizedRootedFirstTail V (2 * C) kappa R q)) /
          (1 - (epsilonPre +
            strongLocalizedRootedFirstTail V (2 * C) kappa R q)) :=
    div_le_div_of_nonneg_left zero_le hden hpreLower
  have hstrong := (houtRoot.strong.conditionOn PreGood hprePos).mono_factor
    hfactor
  let Lfinal := Lroot.conditionOn PreGood hprePos
  have hrooted : RelativeReserveProtectedRootedOutput Lfinal W next F i
      G A I D bits d Dint R p reserveDensity
      (((2 * C) / (1 - strongLocalizedRootedFirstTail V (2 * C) kappa R q)) /
        (1 - (epsilonPre +
          strongLocalizedRootedFirstTail V (2 * C) kappa R q))) b := by
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
  refine ⟨hrooted, ?_⟩
  exact Lroot.conditionOn_supported PreGood hprePos

end

end Erdos207
