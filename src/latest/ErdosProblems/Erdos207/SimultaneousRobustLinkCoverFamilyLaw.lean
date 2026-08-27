/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SimultaneousRobustLinkCoverLaw
import ErdosProblems.Erdos207.LinkReserveAccounting

/-!
# Structurally supported simultaneous robust-link law

This is the reserve-accounting strengthening of the simultaneous robust-link
law: besides cover validity and C4, support remembers that every selected
triple is in the injectively encoded global link reservoir.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem exists_simultaneousRobustLinkCoverFamilyLaw
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
    (Delta groupSize degreeCutoff rootCutoff familyCutoff : ℕ)
    (hcandidates : ∀ o,
      ∀ h : OrientedSmallHallObstruction ↥(K o).left ↥(K o).right,
        (Delta * orientedSmallHallSize h + 1) * groupSize ≤
          (orientedSmallHallCandidates (r o) h).card)
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
      (Fintype.card (SimultaneousHallGroupIndex O V K Delta) : ℝ≥0) *
          (1 - sigma) ^ groupSize +
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
    (independentBits_probability_not_simultaneousRobustLinkGood_le
      F P U center K hcenter hout hleft hright r Delta groupSize
      hcandidates hbalanced sigma hsigma kappa rootCutoff hfamily
      hkappa).trans_lt hsmall
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
