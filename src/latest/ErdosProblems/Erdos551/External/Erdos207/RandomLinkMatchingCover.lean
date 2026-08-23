/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos551.External.Erdos207.LinkMatchingTriangles

/-!
# A randomly sparsified safe link cover

This file connects the exact independent-sampling robust Hall theorem with
the link-triangle bridge.  Its main theorem is the deterministic/probabilistic
endpoint of the KSSS `M^\ddagger` construction for one bipartite link:

* sample a reservoir satisfying every future bounded-deletion Hall problem;
* delete pair conflicts and forbidden participants;
* take a surviving bijective matching;
* turn it into edge-disjoint available triples which cover both link sides.

All estimates remain explicit hypotheses.  In particular, no asymptotic
notation is hidden in the statement.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- All link triples represented by a sampled set of bipartite relation
pairs.  This is the ambient reservoir relative to which forbidden
participation is tested before taking a matching subfamily. -/
def linkReservoirTriangles
    {A B V : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (R : Finset (A × B)) : TripleSystemOn V :=
  R.image fun ab ↦ linkMatchingTriple center left right hcenterLeft
    hcenterRight hleftRight ab.1 ab.2

lemma linkMatchingTriangles_subset_linkReservoirTriangles
    {A B V : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (R : Finset (A × B)) (f : A → B)
    (hfR : ∀ a, (a, f a) ∈ R) :
    linkMatchingTriangles center left right hcenterLeft hcenterRight
      hleftRight f ⊆
      linkReservoirTriangles center left right hcenterLeft hcenterRight
        hleftRight R := by
  classical
  intro T hT
  obtain ⟨a, rfl⟩ := mem_linkMatchingTriangles_iff.mp hT
  exact mem_image.mpr ⟨(a, f a), hfR a, rfl⟩

/-- A robust sampled relation, together with explicit deletion and safety
bounds, yields one safe covering link matching. -/
theorem exists_safe_linkMatchingTriangles_of_sample
    {A B V : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (F : ForbiddenFamilyOn V) (P available : TripleSystemOn V)
    (r : A → B → Prop) [DecidableRel r]
    (Delta : Nat) (R : Finset (A × B))
    (hmatching : ∀ (deleted : A → B → Prop) [DecidableRel deleted],
      (∀ a, (deletedNeighbors deleted a).card ≤ Delta) →
      ∃ f : A → B, Function.Injective f ∧
        ∀ a, r a (f a) ∧ (a, f a) ∈ R ∧ ¬ deleted a (f a))
    (hcard : Fintype.card A = Fintype.card B)
    (hPpacking : IsPackingOn P) (hPavoid : AvoidsForbidden P F)
    (havailable : ∀ a b, r a b →
      linkMatchingTriple center left right hcenterLeft hcenterRight
        hleftRight a b ∈ available)
    (deleted : A → B → Prop) [DecidableRel deleted]
    (havoidsOld : ∀ a b, r a b → (a, b) ∈ R → ¬ deleted a b →
      TriangleAvoidsGraph (coveredGraph P)
        (linkMatchingTriple center left right hcenterLeft hcenterRight
          hleftRight a b))
    (hdeleted : ∀ a, (deletedNeighbors deleted a).card ≤ Delta)
    (hsafe : ∀ a b, r a b → (a, b) ∈ R → ¬ deleted a b →
      ¬ ParticipatesForbidden F P
        (linkReservoirTriangles center left right hcenterLeft hcenterRight
          hleftRight R)
        (linkMatchingTriple center left right hcenterLeft hcenterRight
          hleftRight a b)) :
    ∃ M : TripleSystemOn V,
      M ⊆ available ∧ Disjoint P M ∧ IsPackingOn (P ∪ M) ∧
      AvoidsForbidden (P ∪ M) F ∧
      (∀ a, (coveredGraph M).Adj center (left a)) ∧
      (∀ b, (coveredGraph M).Adj center (right b)) := by
  classical
  obtain ⟨f, hfinj, hf⟩ := hmatching deleted hdeleted
  have hfbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, hcard⟩
  let M := linkMatchingTriangles center left right hcenterLeft
    hcenterRight hleftRight f
  have hMpacking : IsPackingOn M := by
    exact linkMatchingTriangles_isPacking center left right hcenterLeft
      hcenterRight hleftRight f hfinj
  have hMavailable : M ⊆ available := by
    apply linkMatchingTriangles_subset_of_relation center left right
      hcenterLeft hcenterRight hleftRight r available havailable f
    exact fun a ↦ (hf a).1
  have hMreservoir : M ⊆ linkReservoirTriangles center left right
      hcenterLeft hcenterRight hleftRight R := by
    exact linkMatchingTriangles_subset_linkReservoirTriangles center left
      right hcenterLeft hcenterRight hleftRight R f
        (fun a ↦ (hf a).2.1)
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
  refine ⟨M, hMavailable, disjoint_of_triangleAvoidsCovered hMavoidsOld,
    hPpacking.union_of_triangleAvoidsCovered hMpacking hMavoidsOld,
    avoidsForbidden_union_of_nonparticipating hPavoid hMreservoir hMsafe,
    ?_, ?_⟩
  · intro a
    exact linkMatchingTriangles_covers_left center left right hcenterLeft
      hcenterRight hleftRight f a
  · intro b
    exact linkMatchingTriangles_covers_right center left right hcenterLeft
      hcenterRight hleftRight f hfbij.2 b

/-- Full candidate-count/union-bound specialization.  The returned sample
is chosen before the caller's deletion relation is applied; hence the
deletion and forbidden-safety functions may depend on that exact sample. -/
theorem exists_safe_linkMatchingTriangles_of_candidate_bound
    {A B V : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq V]
    (center : V) (left : A ↪ V) (right : B ↪ V)
    (hcenterLeft : ∀ a, center ≠ left a)
    (hcenterRight : ∀ b, center ≠ right b)
    (hleftRight : ∀ a b, left a ≠ right b)
    (F : ForbiddenFamilyOn V) (P available : TripleSystemOn V)
    (r : A → B → Prop) [DecidableRel r]
    (Delta k : Nat)
    (hcandidates : ∀ o : HallObstruction A B,
      (Delta * o.1.1.card + 1) * k ≤
        (relationPairsLeaving r o.1.1 o.1.2).card)
    (sampleProbability : NNReal) (hprob : sampleProbability ≤ 1)
    (hsmall :
      (Fintype.card
        (Σ o : HallObstruction A B, HallGroupIndex Delta o) : NNReal) *
          (1 - sampleProbability) ^ k < 1)
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
    (hdeleted : ∀ R a,
      (deletedNeighbors (deleted R) a).card ≤ Delta)
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
  obtain ⟨R, hR⟩ :=
    exists_injective_robust_matching_sample_of_candidate_bound
      r Delta k hcandidates sampleProbability hprob hsmall
  obtain ⟨M, hM⟩ := exists_safe_linkMatchingTriangles_of_sample
    center left right hcenterLeft hcenterRight hleftRight F P available
      r Delta R hR hcard hPpacking hPavoid havailable (deleted R)
      (havoidsOld R) (hdeleted R) (hsafe R)
  exact ⟨R, M, hM⟩

end

end Erdos207
