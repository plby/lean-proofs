/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpRobustHallSampling
import ErdosProblems.Erdos207.SimultaneousRobustLinkCoverFamilyLaw

/-!
# The simultaneous robust-link law with the exact Hall lower tail

The original link-cover law partitions every Hall candidate set into fixed
blocks.  That loses most of the exponent when the terminal vortex is sparse.
Here the exact binomial lower tail from `SharpRobustHallSampling` replaces
that block estimate.  The rooted-threat event and all deterministic cover
arguments are unchanged.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The joint good event fails with probability at most the exact sum of the
binomial Hall tails plus the existing rooted-threat tail. -/
theorem independentBits_probability_not_simultaneousRobustLinkGood_le_sharp
    {O V : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    [rDecidable : ∀ o, DecidableRel (r o)]
    (Delta : ℕ)
    (hbalanced : ∀ o, (K o).left.card = (K o).right.card)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (kappa : ℝ≥0) {familyCutoff momentOrder : ℕ}
    (rootCutoff : ℕ)
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hkappa : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 ↦
          relativeRootedThreatRemainder P z)
        (fun _ ↦ sigma) kappa) :
    (FiniteLaw.independentBits
      (fun _ : SimultaneousLinkPair O V K ↦ sigma)
      (fun _ ↦ hsigma)).probability (fun omega ↦
        ¬ IsSimultaneousRobustLinkGood F P U center K hcenter hout hleft
          hright r Delta rootCutoff omega) ≤
      (∑ o : O,
        ∑ h : OrientedSmallHallObstruction
            ↥(K o).left ↥(K o).right,
          (1 - sigma / 2) ^
              (orientedSmallHallCandidates (r o) h).card /
            (1 / 2 : ℝ≥0) ^ (Delta * orientedSmallHallSize h)) +
        (Fintype.card (DistinctPair V) : ℝ≥0) *
          ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
              momentOrder) /
            (rootCutoff + 1 : ℝ≥0) ^ momentOrder) := by
  let L := FiniteLaw.independentBits
    (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)
  let HallGood : (SimultaneousLinkPair O V K → Bool) → Prop :=
    fun omega ↦ ∀ o, IsTwoSidedRobustMatchingSample (r o) Delta
      (simultaneousLinkSelectedPairs K omega o)
  let RootGood : (SimultaneousLinkPair O V K → Bool) → Prop :=
    IsSimultaneousRootedGood F P U center K hcenter hout hleft hright
      rootCutoff
  calc
    L.probability (fun omega ↦
        ¬ IsSimultaneousRobustLinkGood F P U center K hcenter hout hleft
          hright r Delta rootCutoff omega) =
        L.probability (fun omega ↦ ¬ HallGood omega ∨ ¬ RootGood omega) := by
      congr 1
      funext omega
      simp only [IsSimultaneousRobustLinkGood, HallGood, RootGood, not_and_or]
    _ ≤ L.probability (fun omega ↦ ¬ HallGood omega) +
        L.probability (fun omega ↦ ¬ RootGood omega) :=
      L.probability_or_le _ _
    _ ≤ (∑ o : O,
          ∑ h : OrientedSmallHallObstruction
              ↥(K o).left ↥(K o).right,
            (1 - sigma / 2) ^
                (orientedSmallHallCandidates (r o) h).card /
              (1 / 2 : ℝ≥0) ^ (Delta * orientedSmallHallSize h)) +
        (Fintype.card (DistinctPair V) : ℝ≥0) *
          ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
              momentOrder) /
            (rootCutoff + 1 : ℝ≥0) ^ momentOrder) := by
      apply add_le_add
      · change
          (FiniteLaw.independentBits
            (fun _ : SimultaneousLinkPair O V K ↦ sigma)
            (fun _ ↦ hsigma)).probability (fun omega ↦
              ¬ ∀ o, IsTwoSidedRobustMatchingSample (r o) Delta
                (simultaneousLinkSelectedPairs K omega o)) ≤ _
        exact independentBits_probability_not_all_twoSidedRobust_le_sharp
          K r Delta hbalanced sigma hsigma
      · simpa only [L, RootGood] using
          independentBits_probability_simultaneousRootedBad_le
            F P U center K hcenter hout hleft hright sigma hsigma kappa
              rootCutoff hfamily hkappa

/-- Complete robust-link law with the exact Hall-tail scalar hypothesis. -/
theorem exists_simultaneousRobustLinkCoverLaw_sharp
    {O V : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V)
    (available P Pbase : TripleSystemOn V)
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    [rDecidable : ∀ o, DecidableRel (r o)]
    (Delta degreeCutoff rootCutoff familyCutoff : ℕ)
    (hbalanced : ∀ o, (K o).left.card = (K o).right.card)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (kappa : ℝ≥0) (momentOrder : ℕ)
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hkappa : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 ↦
          relativeRootedThreatRemainder P z)
        (fun _ ↦ sigma) kappa)
    (hsmall :
      (∑ o : O,
        ∑ h : OrientedSmallHallObstruction
            ↥(K o).left ↥(K o).right,
          (1 - sigma / 2) ^
              (orientedSmallHallCandidates (r o) h).card /
            (1 / 2 : ℝ≥0) ^ (Delta * orientedSmallHallSize h)) +
        (Fintype.card (DistinctPair V) : ℝ≥0) *
          ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
              momentOrder) /
            (rootCutoff + 1 : ℝ≥0) ^ momentOrder) < 1)
    (hPpacking : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (havailable : ∀ o a b, r o a b →
      linkMatchingTriple (K o).center (K o).leftEmbedding
        (K o).rightEmbedding (K o).center_ne_left
        (K o).center_ne_right (K o).left_ne_right a b ∈ available)
    (hbaseSafe : ∀ o a b, r o a b →
      TriangleAvoidsGraph (coveredGraph Pbase)
        (linkMatchingTriple (K o).center (K o).leftEmbedding
          (K o).rightEmbedding (K o).center_ne_left
          (K o).center_ne_right (K o).left_ne_right a b))
    (hstateControls : ∀ (omega : SimultaneousLinkPair O V K → Bool),
      ∀ (S : Finset O) (P' : TripleSystemOn V),
      P ⊆ P' →
      P' ⊆ P ∪ (available ∩ simultaneousLinkReservoir U center K
        hcenter hout hleft hright omega) →
      IsPackingOn P' → AvoidsForbidden P' F →
      IsProcessedSimultaneousLinkFamily K S (P' \ P) →
      ∀ o, o ∉ S →
        (∀ a : ↥(K o).left, (leaveGraph P').Adj (K o).center a.1) ∧
        (∀ b : ↥(K o).right, (leaveGraph P').Adj (K o).center b.1) ∧
        (∀ a : ↥(K o).left,
          (coveredGraph (P' \ Pbase)).degree a.1 ≤ degreeCutoff) ∧
        (∀ b : ↥(K o).right,
          (coveredGraph (P' \ Pbase)).degree b.1 ≤ degreeCutoff))
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta) :
    ∃ law : FiniteLaw (TripleSystemOn V),
      law.SupportedOn (IsSimultaneousLinkCover F available P K) ∧
      ∀ Q : TripleSystemOn V,
        law.probability (fun M ↦ Q ⊆ M) ≤
          (sigma /
            (FiniteLaw.independentBits
              (fun _ : SimultaneousLinkPair O V K ↦ sigma)
              (fun _ ↦ hsigma)).probability
                (IsSimultaneousRobustLinkGood F P U center K hcenter hout
                  hleft hright r Delta rootCutoff)) ^ Q.card := by
  let L := FiniteLaw.independentBits
    (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)
  let Good := IsSimultaneousRobustLinkGood F P U center K hcenter hout
    hleft hright r Delta rootCutoff
  have hbad : L.probability (fun omega ↦ ¬ Good omega) < 1 :=
    (independentBits_probability_not_simultaneousRobustLinkGood_le_sharp
      F P U center K hcenter hout hleft hright r Delta hbalanced sigma
      hsigma kappa rootCutoff hfamily hkappa).trans_lt hsmall
  have hGood : 0 < L.probability Good := by
    by_contra hnot
    have hzero : L.probability Good = 0 :=
      le_antisymm (not_lt.mp hnot) zero_le
    have hone : L.probability (fun omega ↦ ¬ Good omega) = 1 := by
      rw [L.probability_not Good, hzero]
      simp
    rw [hone] at hbad
    exact (lt_irrefl 1 hbad)
  apply exists_simultaneousLinkCoverLaw_of_good_reservoir_pow
    U center K hcenter hout hleft hright F available P sigma hsigma
      Good hGood
  intro omega hgood
  apply exists_simultaneousLinkCover_of_robust_samples
    U center K hcenter hout hleft hright F available P r Delta omega
      hgood.1 hPpacking hPavoid havailable
  intro S P' hPP' hP'sub hP'packing hP'avoid hprocessed o ho
  have hcontrols := hstateControls omega S P' hPP' hP'sub hP'packing
    hP'avoid hprocessed o ho
  have hroots := simultaneousRootedGood_local_cutoffs F P P' U center K
    hcenter hout hleft hright rootCutoff omega hgood.2
      (hP'sub.trans (by
        intro T hT
        rcases mem_union.mp hT with hTP | hTR
        · exact mem_union_left _ hTP
        · exact mem_union_right _ (mem_inter.mp hTR).2)) o
  exact bipartiteLinkRelevantBadDegree_of_cutoffs F Pbase P' (K o)
    (r o) (simultaneousLinkSelectedPairs K omega o) Delta degreeCutoff
      rootCutoff familyCutoff hfamily (hbaseSafe o) hcontrols.1
      hcontrols.2.1 hcontrols.2.2.1 hcontrols.2.2.2 hroots.1 hroots.2
      hdeletionScalar

/-- Reserve-accounting strengthening of the sharp law. -/
theorem exists_simultaneousRobustLinkCoverFamilyLaw_sharp
    {O V : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V)
    (available P Pbase : TripleSystemOn V)
    (U : Finset V) (center : O ↪ V) (K : O → BipartiteLink V)
    (hcenter : ∀ o, (K o).center = center o)
    (hout : ∀ o, center o ∉ U)
    (hleft : ∀ o, (K o).left ⊆ U)
    (hright : ∀ o, (K o).right ⊆ U)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    [rDecidable : ∀ o, DecidableRel (r o)]
    (Delta degreeCutoff rootCutoff familyCutoff : ℕ)
    (hbalanced : ∀ o, (K o).left.card = (K o).right.card)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (kappa : ℝ≥0) (momentOrder : ℕ)
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hkappa : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 ↦
          relativeRootedThreatRemainder P z)
        (fun _ ↦ sigma) kappa)
    (hsmall :
      (∑ o : O,
        ∑ h : OrientedSmallHallObstruction
            ↥(K o).left ↥(K o).right,
          (1 - sigma / 2) ^
              (orientedSmallHallCandidates (r o) h).card /
            (1 / 2 : ℝ≥0) ^ (Delta * orientedSmallHallSize h)) +
        (Fintype.card (DistinctPair V) : ℝ≥0) *
          ((((2 : ℝ≥0) ^ (momentOrder * (familyCutoff - 1)) * kappa) ^
              momentOrder) /
            (rootCutoff + 1 : ℝ≥0) ^ momentOrder) < 1)
    (hPpacking : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (havailable : ∀ o a b, r o a b →
      linkMatchingTriple (K o).center (K o).leftEmbedding
        (K o).rightEmbedding (K o).center_ne_left
        (K o).center_ne_right (K o).left_ne_right a b ∈ available)
    (hbaseSafe : ∀ o a b, r o a b →
      TriangleAvoidsGraph (coveredGraph Pbase)
        (linkMatchingTriple (K o).center (K o).leftEmbedding
          (K o).rightEmbedding (K o).center_ne_left
          (K o).center_ne_right (K o).left_ne_right a b))
    (hstateControls : ∀ (omega : SimultaneousLinkPair O V K → Bool),
      ∀ (S : Finset O) (P' : TripleSystemOn V),
      P ⊆ P' →
      P' ⊆ P ∪ (available ∩ simultaneousLinkReservoir U center K
        hcenter hout hleft hright omega) →
      IsPackingOn P' → AvoidsForbidden P' F →
      IsProcessedSimultaneousLinkFamily K S (P' \ P) →
      ∀ o, o ∉ S →
        (∀ a : ↥(K o).left, (leaveGraph P').Adj (K o).center a.1) ∧
        (∀ b : ↥(K o).right, (leaveGraph P').Adj (K o).center b.1) ∧
        (∀ a : ↥(K o).left,
          (coveredGraph (P' \ Pbase)).degree a.1 ≤ degreeCutoff) ∧
        (∀ b : ↥(K o).right,
          (coveredGraph (P' \ Pbase)).degree b.1 ≤ degreeCutoff))
    (hdeletionScalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta) :
    ∃ law : FiniteLaw (TripleSystemOn V),
      law.SupportedOn (fun M ↦
        IsSimultaneousLinkCover F available P K M ∧
          IsSimultaneousLinkFamily K M) ∧
      ∀ Q : TripleSystemOn V,
        law.probability (fun M ↦ Q ⊆ M) ≤
          (sigma /
            (FiniteLaw.independentBits
              (fun _ : SimultaneousLinkPair O V K ↦ sigma)
              (fun _ ↦ hsigma)).probability
                (IsSimultaneousRobustLinkGood F P U center K hcenter hout
                  hleft hright r Delta rootCutoff)) ^ Q.card := by
  let L := FiniteLaw.independentBits
    (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)
  let Good := IsSimultaneousRobustLinkGood F P U center K hcenter hout
    hleft hright r Delta rootCutoff
  have hbad : L.probability (fun omega ↦ ¬ Good omega) < 1 :=
    (independentBits_probability_not_simultaneousRobustLinkGood_le_sharp
      F P U center K hcenter hout hleft hright r Delta hbalanced sigma
      hsigma kappa rootCutoff hfamily hkappa).trans_lt hsmall
  have hGood : 0 < L.probability Good := by
    by_contra hnot
    have hzero : L.probability Good = 0 :=
      le_antisymm (not_lt.mp hnot) zero_le
    have hone : L.probability (fun omega ↦ ¬ Good omega) = 1 := by
      rw [L.probability_not Good, hzero]
      simp
    rw [hone] at hbad
    exact (lt_irrefl 1 hbad)
  apply exists_simultaneousLinkCoverFamilyLaw_of_good_reservoir_pow
    U center K hcenter hout hleft hright F available P sigma hsigma
      Good hGood
  intro omega hgood
  apply exists_simultaneousLinkCover_of_robust_samples
    U center K hcenter hout hleft hright F available P r Delta omega
      hgood.1 hPpacking hPavoid havailable
  intro S P' hPP' hP'sub hP'packing hP'avoid hprocessed o ho
  have hcontrols := hstateControls omega S P' hPP' hP'sub hP'packing
    hP'avoid hprocessed o ho
  have hroots := simultaneousRootedGood_local_cutoffs F P P' U center K
    hcenter hout hleft hright rootCutoff omega hgood.2
      (hP'sub.trans (by
        intro T hT
        rcases mem_union.mp hT with hTP | hTR
        · exact mem_union_left _ hTP
        · exact mem_union_right _ (mem_inter.mp hTR).2)) o
  exact bipartiteLinkRelevantBadDegree_of_cutoffs F Pbase P' (K o)
    (r o) (simultaneousLinkSelectedPairs K omega o) Delta degreeCutoff
      rootCutoff familyCutoff hfamily (hbaseSafe o) hcontrols.1
      hcontrols.2.1 hcontrols.2.2.1 hcontrols.2.2.2 hroots.1 hroots.2
      hdeletionScalar

end

end Erdos207
