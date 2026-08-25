/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RandomLinkMatchingCover
import ErdosProblems.Erdos207.TwoSidedRandomRobustMatching

/-!
# Two-sided randomly sparsified safe link covers

This upgrades the original one-sided robust-link interface to the exact
two-sided Hall criterion used in KSSS.  Both endpoint deletion degrees are
explicit, and only small Hall obstructions in the two orientations enter the
sampling union bound.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- A two-sided robust sampled relation yields a safe family of covering
link triangles. -/
theorem exists_safe_linkMatchingTriangles_of_twoSided_sample
    {A B V : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (F : ForbiddenFamilyOn V) (P available : TripleSystemOn V)
    (r : A → B → Prop) [DecidableRel r]
    (Delta : ℕ) (R : Finset (A × B))
    (hmatching : ∀ (deleted : A → B → Prop) [DecidableRel deleted],
      (∀ a, (deletedNeighbors deleted a).card ≤ Delta) →
      (∀ b, (deletedNeighbors (transposeRelation deleted) b).card ≤ Delta) →
      ∃ f : A → B, Function.Bijective f ∧
        ∀ a, r a (f a) ∧ (a, f a) ∈ R ∧ ¬ deleted a (f a))
    (hPpacking : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (havailable : ∀ a b, r a b →
      linkMatchingTriple center left right hcenterLeft hcenterRight
        hleftRight a b ∈ available)
    (deleted : A → B → Prop) [DecidableRel deleted]
    (havoidsOld : ∀ a b, r a b → (a, b) ∈ R → ¬ deleted a b →
      TriangleAvoidsGraph (coveredGraph P)
        (linkMatchingTriple center left right hcenterLeft hcenterRight
          hleftRight a b))
    (hleftDeleted : ∀ a, (deletedNeighbors deleted a).card ≤ Delta)
    (hrightDeleted : ∀ b,
      (deletedNeighbors (transposeRelation deleted) b).card ≤ Delta)
    (hsafe : ∀ a b, r a b → (a, b) ∈ R → ¬ deleted a b →
      ¬ ParticipatesForbidden F P
        (linkReservoirTriangles center left right hcenterLeft hcenterRight
          hleftRight R)
        (linkMatchingTriple center left right hcenterLeft hcenterRight
          hleftRight a b)) :
    ∃ M : TripleSystemOn V,
      M ⊆ available ∧
      M ⊆ linkReservoirTriangles center left right hcenterLeft
        hcenterRight hleftRight R ∧
      Disjoint P M ∧ IsPackingOn (P ∪ M) ∧
      AvoidsForbidden (P ∪ M) F ∧
      (∀ a, (coveredGraph M).Adj center (left a)) ∧
      (∀ b, (coveredGraph M).Adj center (right b)) := by
  classical
  obtain ⟨f, hfbij, hf⟩ :=
    hmatching deleted hleftDeleted hrightDeleted
  let M := linkMatchingTriangles center left right hcenterLeft
    hcenterRight hleftRight f
  have hMpacking : IsPackingOn M :=
    linkMatchingTriangles_isPacking center left right hcenterLeft
      hcenterRight hleftRight f hfbij.1
  have hMavailable : M ⊆ available := by
    apply linkMatchingTriangles_subset_of_relation center left right
      hcenterLeft hcenterRight hleftRight r available havailable f
    exact fun a ↦ (hf a).1
  have hMreservoir : M ⊆ linkReservoirTriangles center left right
      hcenterLeft hcenterRight hleftRight R :=
    linkMatchingTriangles_subset_linkReservoirTriangles center left right
      hcenterLeft hcenterRight hleftRight R f (fun a ↦ (hf a).2.1)
  have hMavoidsOld : ∀ T ∈ M,
      TriangleAvoidsGraph (coveredGraph P) T := by
    intro T hTM
    obtain ⟨a, rfl⟩ := mem_linkMatchingTriangles_iff.mp hTM
    exact havoidsOld a (f a) (hf a).1 (hf a).2.1 (hf a).2.2
  have hMsafe : ∀ T ∈ M,
      ¬ ParticipatesForbidden F P
        (linkReservoirTriangles center left right hcenterLeft
          hcenterRight hleftRight R) T := by
    intro T hTM
    obtain ⟨a, rfl⟩ := mem_linkMatchingTriangles_iff.mp hTM
    exact hsafe a (f a) (hf a).1 (hf a).2.1 (hf a).2.2
  refine ⟨M, hMavailable, hMreservoir,
    disjoint_of_triangleAvoidsCovered hMavoidsOld,
    hPpacking.union_of_triangleAvoidsCovered hMpacking hMavoidsOld,
    avoidsForbidden_union_of_nonparticipating hPavoid hMreservoir hMsafe,
    ?_, ?_⟩
  · exact linkMatchingTriangles_covers_left center left right hcenterLeft
      hcenterRight hleftRight f
  · exact linkMatchingTriangles_covers_right center left right hcenterLeft
      hcenterRight hleftRight f hfbij.2

/-- Full two-sided candidate-count and finite-union-bound specialization. -/
theorem exists_safe_linkMatchingTriangles_of_twoSided_candidate_bound
    {A B V : Type*} [Fintype A] [Fintype B]
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
    (sampleProbability : NNReal) (hprob : sampleProbability ≤ 1)
    (hsmall :
      (Fintype.card
        (Σ o : OrientedSmallHallObstruction A B,
          OrientedSmallHallGroupIndex Delta o) : NNReal) *
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
    (hleftDeleted : ∀ R a,
      (deletedNeighbors (deleted R) a).card ≤ Delta)
    (hrightDeleted : ∀ R b,
      (deletedNeighbors (transposeRelation (deleted R)) b).card ≤ Delta)
    (hsafe : ∀ R a b, r a b → (a, b) ∈ R → ¬ deleted R a b →
      ¬ ParticipatesForbidden F P
        (linkReservoirTriangles center left right hcenterLeft hcenterRight
          hleftRight R)
        (linkMatchingTriple center left right hcenterLeft hcenterRight
          hleftRight a b)) :
    ∃ R : Finset (A × B), ∃ M : TripleSystemOn V,
      M ⊆ available ∧ Disjoint P M ∧ IsPackingOn (P ∪ M) ∧
      AvoidsForbidden (P ∪ M) F ∧
      (∀ a, (coveredGraph M).Adj center (left a)) ∧
      (∀ b, (coveredGraph M).Adj center (right b)) := by
  classical
  obtain ⟨R, hR⟩ := exists_bijective_twoSided_robust_matching_sample
    r Delta groupSize hcandidates sampleProbability hprob hsmall hcard
  obtain ⟨M, hMavailable, _hMreservoir, hPMdisjoint, hPMpacking,
      hPMavoid, hleft, hright⟩ :=
    exists_safe_linkMatchingTriangles_of_twoSided_sample
      center left right hcenterLeft hcenterRight hleftRight F P available
      r Delta R hR hPpacking hPavoid havailable (deleted R)
      (havoidsOld R) (hleftDeleted R) (hrightDeleted R) (hsafe R)
  exact ⟨R, M, hMavailable, hPMdisjoint, hPMpacking, hPMavoid,
    hleft, hright⟩

end

end Erdos207
