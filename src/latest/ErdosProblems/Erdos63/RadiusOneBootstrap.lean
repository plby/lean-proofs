/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos63.AdjusterBase

/-!
# The radius-one bootstrap in Liu--Montgomery Lemma 3.7

This file isolates the first growth step in the source proof.  Starting at a
vertex of degree at least `d`, the radius-one ball loses at most the neighbors
in the common deletion `U`, all vertices of the candidate-dependent barrier
`B`, and the vertices of `C` measured by limited contact.

The second part applies the general count to the canonical seed, barrier, and
shortest path attached to a reaching eligible adjuster candidate.
-/

open Finset Set SimpleGraph
open scoped SimpleGraph

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

variable {V : Type u}
variable {G : SimpleGraph V}

/-! ## The finite radius-one count -/

/-- The radius-one bootstrap used in the source proof of Lemma 3.7.

The losses are kept separate: `u` bounds the neighbors of the chosen root in
the common deletion `U`, `b` bounds all of `B`, and `c` bounds the contact of
the seed with `C` after deleting `U ∪ B`. -/
theorem degree_sub_degreeInto_sub_card_sub_contact_le_card_ballAvoidingFrom_one
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (U B C A : Finset V) (x : V) (d u b c : ℕ)
    (hx : x ∈ A) (hdisjoint : Disjoint A (U ∪ B ∪ C))
    (hdegree : d ≤ G.degree x)
    (hdegreeInto : (G.neighborFinset x ∩ U).card ≤ u)
    (hBcard : B.card ≤ b)
    (hcontact : HasLimitedContactAfterDeletion G A (U ∪ B) C c) :
    d - u - b - c ≤
      (ballAvoidingFrom G
        ((U : Set V) ∪ (B : Set V) ∪ (C : Set V)) A 1).card := by
  classical
  let W : Finset V := U ∪ B ∪ C
  let blocked := blockedExternalNeighborhood G (C : Set V) A
  have hneighborSubset : G.neighborFinset x \ W ⊆
      ballAvoidingFrom G
        ((U : Set V) ∪ (B : Set V) ∪ (C : Set V)) A 1 := by
    intro y hy
    obtain ⟨hyNeighbor, hyW⟩ := Finset.mem_sdiff.1 hy
    have hxy : G.Adj x y := (G.mem_neighborFinset x y).1 hyNeighbor
    let p : G.Walk x y := Walk.cons hxy Walk.nil
    rw [mem_ballAvoidingFrom]
    refine ⟨x, hx, p, ⟨?_, ?_⟩, by simp [p]⟩
    · simp [p, Walk.cons_isPath_iff, G.ne_of_adj hxy]
    · intro z hz hzForbidden
      simp only [p, Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hz
      rcases hz with hzx | hzy
      · simpa only [Set.mem_singleton_iff] using hzx
      · have hzW : z ∈ W := by
          change ((z ∈ U ∨ z ∈ B) ∨ z ∈ C) at hzForbidden
          simpa only [W, Finset.mem_union] using hzForbidden
        exact (hyW (hzy ▸ hzW)).elim
  have hcontactZero : blocked.card ≤ c := by
    simpa only [blocked, ballAvoidingFrom_zero, Nat.zero_add, Nat.mul_one]
      using hcontact 0
  have hbadSubset : W ∩ G.neighborFinset x ⊆
      ((G.neighborFinset x ∩ U) ∪ B) ∪ blocked := by
    intro y hy
    obtain ⟨hyW, hyNeighbor⟩ := Finset.mem_inter.1 hy
    change y ∈ U ∪ B ∪ C at hyW
    simp only [Finset.mem_union] at hyW
    rcases hyW with (hyU | hyB) | hyC
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hyNeighbor, hyU⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hyB)
    · apply Finset.mem_union_right
      rw [mem_blockedExternalNeighborhood]
      refine ⟨?_, hyC⟩
      rw [mem_externalNeighborhood]
      refine ⟨?_, x, hx, (G.mem_neighborFinset x y).1 hyNeighbor⟩
      intro hyA
      exact (Finset.disjoint_left.1 hdisjoint hyA (by
        exact Finset.mem_union_right _ hyC)).elim
  have hbadCard : (W ∩ G.neighborFinset x).card ≤ u + b + c := by
    have hsub := Finset.card_le_card hbadSubset
    have hfirst := Finset.card_union_le (G.neighborFinset x ∩ U) B
    have hsecond := Finset.card_union_le
      ((G.neighborFinset x ∩ U) ∪ B) blocked
    omega
  have hsurviving := Finset.card_le_card hneighborSubset
  rw [Finset.card_sdiff, G.card_neighborFinset_eq_degree] at hsurviving
  omega

/-! ## Reaching eligible candidates -/

namespace SmallSimpleAdjusterCandidate

/-- The source Lemma 3.7 radius-one bootstrap for the canonical opposite
seed of a reaching eligible candidate.  The candidate's exact radius controls
the barrier loss. -/
theorem reachingCandidate_radiusOne_bootstrap
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius minRadius maxRadius d degreeInto : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
    (hdegree : d ≤ G.degree
      (reachingCandidateConnectionData i).adjusted.rightRoot)
    (hprotected : deleted ∪ manyNeighborsInto G deleted degreeInto ⊆
      protectedSet) :
    d - degreeInto - (11 * i.1.1.radius + 1) - 2 ≤
      (ballAvoidingFrom G
        ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) 1).card := by
  classical
  let P := reachingCandidateConnectionData i
  let x := P.adjusted.rightRoot
  have hx : x ∈ reachingCandidateSeed i := by
    simpa only [x, P, reachingCandidateSeed] using P.adjusted.rightEnd.root_mem
  have hseedDisjoint : Disjoint (reachingCandidateSeed i)
      (deleted ∪ reachingCandidateBarrier i ∪ reachingCandidatePath i) := by
    rw [Finset.disjoint_left]
    intro z hzSeed hzForbidden
    simp only [Finset.mem_union] at hzForbidden
    rcases hzForbidden with (hzDeleted | hzBarrier) | hzPath
    · exact (Finset.disjoint_left.1
        (reachingCandidateSeed_disjoint_deleted_union_barrier i)
        hzSeed (Finset.mem_union_left _ hzDeleted)).elim
    · exact (Finset.disjoint_left.1
        (reachingCandidateSeed_disjoint_deleted_union_barrier i)
        hzSeed (Finset.mem_union_right _ hzBarrier)).elim
    · exact (Finset.disjoint_left.1 P.opposite_disjoint_path hzSeed (by
        simpa only [reachingCandidatePath] using hzPath)).elim
  have hballZero :
      ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) 0 =
        ballAvoidingFrom G
          ((deleted : Set V) ∪ (highDegree : Set V) ∪
            (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) 0 := by
    simp
  have hdegreeInto : (G.neighborFinset x ∩ deleted).card ≤ degreeInto := by
    apply reachingCandidate_degreeInto_deleted_le G i
      (ballRadius := 0) (by omega) hprotected hballZero x
    simpa only [ballAvoidingFrom_zero] using hx
  apply degree_sub_degreeInto_sub_card_sub_contact_le_card_ballAvoidingFrom_one
    G deleted (reachingCandidateBarrier i) (reachingCandidatePath i)
      (reachingCandidateSeed i) x d degreeInto
      (11 * i.1.1.radius + 1) 2 hx hseedDisjoint hdegree hdegreeInto
  · exact card_reachingCandidateBarrier_le i
  · exact reachingCandidate_limitedContact_barrier i

/-- A uniform version of `reachingCandidate_radiusOne_bootstrap`, using the
maximum allowed candidate radius and a graph-wide minimum-degree hypothesis. -/
theorem reachingCandidate_radiusOne_bootstrap_maxRadius
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius minRadius maxRadius d degreeInto : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (hprotected : deleted ∪ manyNeighborsInto G deleted degreeInto ⊆
      protectedSet) :
    d - degreeInto - (11 * maxRadius + 1) - 2 ≤
      (ballAvoidingFrom G
        ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) 1).card := by
  have hbootstrap := reachingCandidate_radiusOne_bootstrap G i
    (hdegree (reachingCandidateConnectionData i).adjusted.rightRoot)
    hprotected
  have hradius := i.1.1.le_max
  omega

end SmallSimpleAdjusterCandidate

end Erdos63
