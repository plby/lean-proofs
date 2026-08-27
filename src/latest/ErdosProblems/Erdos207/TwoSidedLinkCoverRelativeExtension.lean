/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LinkReservoirRelativeExtension
import ErdosProblems.Erdos207.TwoSidedLinkCoverGood

/-!
# Safe link covers preserving a relative-extension invariant

The robust-Hall, rooted-cutoff, and relative-extension events are imposed on
one Bernoulli link reservoir.  The matching eventually retained by the link
step is a subfamily of that reservoir.  Hence the relative-extension bound
for the reservoir passes to the retained matching by the root-changing
monotonicity lemma.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Add a relative-extension cutoff to any auxiliary good-reservoir event in
the two-sided robust matching theorem.  The conclusion records the bound for
the actual matching, rather than merely for the larger sampled reservoir. -/
theorem exists_safe_linkMatchingTriangles_of_twoSided_candidate_bound_with_good_extension
    {A B V J : Type*} [Fintype A] [Fintype B] [Fintype V] [Fintype J]
    [DecidableEq A] [DecidableEq B] [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (F : ForbiddenFamilyOn V) (P available : TripleSystemOn V)
    (r : A → B → Prop) [DecidableRel r]
    (Delta groupSize : ℕ)
    (hcandidates : ∀ o : OrientedSmallHallObstruction A B,
      (Delta * orientedSmallHallSize o + 1) * groupSize ≤
        (orientedSmallHallCandidates r o).card)
    (sampleProbability : ℝ≥0) (hprob : sampleProbability ≤ 1)
    (Good : Finset (A × B) → Prop) (epsilonGood : ℝ≥0)
    (hbadGood : (FiniteLaw.independentBits
      (fun _ : A × B ↦ sampleProbability) (fun _ ↦ hprob)).probability
        (fun omega ↦ ¬ Good (FiniteLaw.selectedByBits omega)) ≤ epsilonGood)
    (configurations : J → TripleSystemOn V)
    (futureWeight totalWeight : TripleOn V → ℝ≥0) (d : ℕ)
    (hconfigCard : ∀ j, (configurations j \ P).card ≤ d)
    (hweight : ∀ T,
      linkReservoirPointWeight center left right hcenterLeft
          hcenterRight hleftRight sampleProbability T + futureWeight T ≤
        totalWeight T)
    (kappa kappaOut : ℝ≥0)
    (hkappa : HasExtensionBound (fun j ↦ configurations j \ P)
      totalWeight kappa)
    (hkappaOut : 0 < kappaOut)
    (epsilonExtension : ℝ≥0)
    (hepsilonExtension :
      (configurationRoots (fun j ↦ configurations j \ P)).card *
        (kappa / kappaOut) ≤ epsilonExtension)
    (hsmall : (epsilonGood + epsilonExtension) +
      (Fintype.card
        (Σ o : OrientedSmallHallObstruction A B,
          OrientedSmallHallGroupIndex Delta o) : ℝ≥0) *
        (1 - sampleProbability) ^ groupSize < 1)
    (hcard : Fintype.card A = Fintype.card B)
    (hPpacking : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (havailable : ∀ a b, r a b →
      linkMatchingTriple center left right hcenterLeft hcenterRight
        hleftRight a b ∈ available)
    (deleted : Finset (A × B) → A → B → Prop)
    [deletedDecidable : ∀ R, DecidableRel (deleted R)]
    (havoidsOld : ∀ R a b, r a b → (a, b) ∈ R →
      ¬ deleted R a b →
      TriangleAvoidsGraph (coveredGraph P)
        (linkMatchingTriple center left right hcenterLeft hcenterRight
          hleftRight a b))
    (hleftDeleted : ∀ R, Good R → ∀ a,
      (deletedNeighbors (deleted R) a).card ≤ Delta)
    (hrightDeleted : ∀ R, Good R → ∀ b,
      (deletedNeighbors (transposeRelation (deleted R)) b).card ≤ Delta)
    (hsafe : ∀ R a b, r a b → (a, b) ∈ R → ¬ deleted R a b →
      ¬ ParticipatesForbidden F P
        (linkReservoirTriangles center left right hcenterLeft hcenterRight
          hleftRight R)
        (linkMatchingTriple center left right hcenterLeft hcenterRight
          hleftRight a b))
    (hfutureWeight : ∀ T, futureWeight T ≤ 1) :
    ∃ M : TripleSystemOn V,
      M ⊆ available ∧
      Disjoint P M ∧ IsPackingOn (P ∪ M) ∧
      AvoidsForbidden (P ∪ M) F ∧
      (∀ a, (coveredGraph M).Adj center (left a)) ∧
      (∀ b, (coveredGraph M).Adj center (right b)) ∧
      HasExtensionBound
        (fun j ↦ configurations j \ (P ∪ M)) futureWeight kappaOut := by
  classical
  let L := FiniteLaw.independentBits
    (fun _ : A × B ↦ sampleProbability) (fun _ ↦ hprob)
  let reservoir : (A × B → Bool) → TripleSystemOn V := fun omega ↦
    linkReservoirTriangles center left right hcenterLeft hcenterRight
      hleftRight (FiniteLaw.selectedByBits omega)
  let ExtensionGood : Finset (A × B) → Prop := fun R ↦
    HasExtensionBound
      (fun j ↦ (configurations j \ P) \
        linkReservoirTriangles center left right hcenterLeft hcenterRight
          hleftRight R)
      futureWeight kappaOut
  have hbadExtension : L.probability (fun omega ↦
      ¬ ExtensionGood (FiniteLaw.selectedByBits omega)) ≤
      epsilonExtension := by
    apply (independentBits_probability_linkReservoir_badExtension_le_of_weight
      center left right hcenterLeft hcenterRight hleftRight
        sampleProbability hprob configurations P futureWeight totalWeight d
        hconfigCard hweight kappa kappaOut hkappa hkappaOut).trans
    exact hepsilonExtension
  let CombinedGood : Finset (A × B) → Prop := fun R ↦
    Good R ∧ ExtensionGood R
  have hbadCombined : L.probability (fun omega ↦
      ¬ CombinedGood (FiniteLaw.selectedByBits omega)) ≤
      epsilonGood + epsilonExtension := by
    calc
      L.probability (fun omega ↦
          ¬ CombinedGood (FiniteLaw.selectedByBits omega)) =
          L.probability (fun omega ↦
            (¬ Good (FiniteLaw.selectedByBits omega)) ∨
            (¬ ExtensionGood (FiniteLaw.selectedByBits omega))) := by
              congr 1
              funext omega
              simp only [CombinedGood, not_and_or]
      _ ≤ L.probability (fun omega ↦
            ¬ Good (FiniteLaw.selectedByBits omega)) +
          L.probability (fun omega ↦
            ¬ ExtensionGood (FiniteLaw.selectedByBits omega)) :=
        L.probability_or_le _ _
      _ ≤ epsilonGood + epsilonExtension :=
        add_le_add hbadGood hbadExtension
  obtain ⟨R, hRgood, M, hMavailable, hMreservoir,
      hPMdisjoint, hPMpacking, hPMavoid, hleft, hright⟩ :=
    exists_safe_linkMatchingTriangles_of_twoSided_candidate_bound_with_good
      center left right hcenterLeft hcenterRight hleftRight F P available r
      Delta groupSize hcandidates sampleProbability hprob CombinedGood
      (epsilonGood + epsilonExtension) (by
        simpa only [L] using hbadCombined) hsmall hcard hPpacking hPavoid
      havailable deleted havoidsOld
      (fun R hR ↦ hleftDeleted R hR.1)
      (fun R hR ↦ hrightDeleted R hR.1) hsafe
  have hrelativeMatching : HasExtensionBound
      (fun j ↦ (configurations j \ P) \ M) futureWeight kappaOut :=
    HasExtensionBound.of_subset_selected hfutureWeight hMreservoir hRgood.2
  have hrelativeUnion : HasExtensionBound
      (fun j ↦ configurations j \ (P ∪ M)) futureWeight kappaOut := by
    simpa only [Finset.sdiff_sdiff_left', sdiff_union_distrib] using
      hrelativeMatching
  exact ⟨M, hMavailable, hPMdisjoint, hPMpacking, hPMavoid,
    hleft, hright, hrelativeUnion⟩

/-- Concrete pair-conflict and forbidden-participation deletions, with both
the rooted cutoff and a relative-extension cutoff selected on the same link
reservoir. -/
theorem exists_linkCover_of_twoSided_degree_rooted_probability_with_extension
    {V J : Type*} [Fintype V] [Fintype J] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (available P : TripleSystemOn V)
    (K : BipartiteLink V) (Delta groupSize degreeCutoff rootCutoff
      familyCutoff : ℕ)
    (hcandidates : ∀ o : OrientedSmallHallObstruction ↥K.left ↥K.right,
      (Delta * orientedSmallHallSize o + 1) * groupSize ≤
        (orientedSmallHallCandidates
          (linkAvailableRelation K available) o).card)
    (sampleProbability : ℝ≥0) (hprob : sampleProbability ≤ 1)
    (epsilonRoot : ℝ≥0)
    (hrootBad : (FiniteLaw.independentBits
      (fun _ : ↥K.left × ↥K.right ↦ sampleProbability)
      (fun _ ↦ hprob)).probability (fun omega ↦
        ¬ ((∀ a : ↥K.left,
          (rootedActiveForbiddenConfigurations F
            (P ∪ linkReservoirTriangles K.center K.leftEmbedding
              K.rightEmbedding K.center_ne_left K.center_ne_right
              K.left_ne_right (FiniteLaw.selectedByBits omega))
            K.center a.1).card ≤ rootCutoff) ∧
        (∀ b : ↥K.right,
          (rootedActiveForbiddenConfigurations F
            (P ∪ linkReservoirTriangles K.center K.leftEmbedding
              K.rightEmbedding K.center_ne_left K.center_ne_right
              K.left_ne_right (FiniteLaw.selectedByBits omega))
            K.center b.1).card ≤ rootCutoff))) ≤ epsilonRoot)
    (configurations : J → TripleSystemOn V)
    (futureWeight totalWeight : TripleOn V → ℝ≥0) (d : ℕ)
    (hconfigCard : ∀ j, (configurations j \ P).card ≤ d)
    (hweight : ∀ T,
      linkReservoirPointWeight K.center K.leftEmbedding K.rightEmbedding
          K.center_ne_left K.center_ne_right K.left_ne_right
          sampleProbability T + futureWeight T ≤ totalWeight T)
    (kappa kappaOut : ℝ≥0)
    (hkappa : HasExtensionBound (fun j ↦ configurations j \ P)
      totalWeight kappa)
    (hkappaOut : 0 < kappaOut)
    (epsilonExtension : ℝ≥0)
    (hepsilonExtension :
      (configurationRoots (fun j ↦ configurations j \ P)).card *
        (kappa / kappaOut) ≤ epsilonExtension)
    (hsmall : (epsilonRoot + epsilonExtension) +
      (Fintype.card
        (Σ o : OrientedSmallHallObstruction ↥K.left ↥K.right,
          OrientedSmallHallGroupIndex Delta o) : ℝ≥0) *
        (1 - sampleProbability) ^ groupSize < 1)
    (hbalanced : K.left.card = K.right.card)
    (hPpacking : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (hfamily : ∀ C ∈ F, C.card ≤ familyCutoff)
    (hleaveLeft : ∀ a : ↥K.left,
      (leaveGraph P).Adj K.center a.1)
    (hleaveRight : ∀ b : ↥K.right,
      (leaveGraph P).Adj K.center b.1)
    (hdegreeLeft : ∀ a : ↥K.left,
      (coveredGraph P).degree K.center + (coveredGraph P).degree a.1 ≤
        degreeCutoff)
    (hdegreeRight : ∀ b : ↥K.right,
      (coveredGraph P).degree K.center + (coveredGraph P).degree b.1 ≤
        degreeCutoff)
    (hscalar : degreeCutoff + rootCutoff * familyCutoff ≤ Delta)
    (hfutureWeight : ∀ T, futureWeight T ≤ 1) :
    ∃ M : TripleSystemOn V,
      M ⊆ available ∧ Disjoint P M ∧
      IsPackingOn (P ∪ M) ∧ AvoidsForbidden (P ∪ M) F ∧
      CoversBipartiteLink K M ∧
      HasExtensionBound
        (fun j ↦ configurations j \ (P ∪ M)) futureWeight kappaOut := by
  classical
  let RootGood : Finset (↥K.left × ↥K.right) → Prop := fun R ↦
    (∀ a : ↥K.left,
      (rootedActiveForbiddenConfigurations F
        (P ∪ linkReservoirTriangles K.center K.leftEmbedding
          K.rightEmbedding K.center_ne_left K.center_ne_right
          K.left_ne_right R) K.center a.1).card ≤ rootCutoff) ∧
    (∀ b : ↥K.right,
      (rootedActiveForbiddenConfigurations F
        (P ∪ linkReservoirTriangles K.center K.leftEmbedding
          K.rightEmbedding K.center_ne_left K.center_ne_right
          K.left_ne_right R) K.center b.1).card ≤ rootCutoff)
  have hcard : Fintype.card ↥K.left = Fintype.card ↥K.right := by
    simpa using hbalanced
  obtain ⟨M, hMavailable, hPMdisjoint, hPMpacking, hPMavoid,
      hleft, hright, hrelative⟩ :=
    exists_safe_linkMatchingTriangles_of_twoSided_candidate_bound_with_good_extension
      K.center K.leftEmbedding K.rightEmbedding K.center_ne_left
      K.center_ne_right K.left_ne_right F P available
      (linkAvailableRelation K available) Delta groupSize hcandidates
      sampleProbability hprob RootGood epsilonRoot (by
        simpa only [RootGood] using hrootBad)
      configurations futureWeight totalWeight d hconfigCard hweight
      kappa kappaOut hkappa hkappaOut epsilonExtension hepsilonExtension
      hsmall hcard hPpacking hPavoid (by intro a b h; exact h)
      (linkDeleted F P K)
      (by
        intro R a b _hr _hR hsurvive
        exact linkDeleted_survivor_avoids hsurvive)
      (by
        intro R hgood a
        exact (card_deletedNeighbors_linkDeleted_le F P K R a
          (hleaveLeft a) familyCutoff hfamily).trans <| by
            exact (Nat.add_le_add (hdegreeLeft a)
              (Nat.mul_le_mul_right familyCutoff (hgood.1 a))).trans hscalar)
      (by
        intro R hgood b
        exact (card_deletedNeighbors_transpose_linkDeleted_le F P K R b
          (hleaveRight b) familyCutoff hfamily).trans <| by
            exact (Nat.add_le_add (hdegreeRight b)
              (Nat.mul_le_mul_right familyCutoff (hgood.2 b))).trans hscalar)
      (by
        intro R a b _hr _hR hsurvive
        exact linkDeleted_survivor_nonparticipating hsurvive)
      hfutureWeight
  exact ⟨M, hMavailable, hPMdisjoint, hPMpacking, hPMavoid,
    ⟨fun x hx ↦ hleft ⟨x, hx⟩, fun x hx ↦ hright ⟨x, hx⟩⟩,
    hrelative⟩

end

end Erdos207
