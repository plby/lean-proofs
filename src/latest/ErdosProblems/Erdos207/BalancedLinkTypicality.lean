/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.BalancedBisection
import ErdosProblems.Erdos207.TypicalBipartiteCandidate
import ErdosProblems.Erdos207.LinkDeletion

/-!
# Typical balanced link bisections

This file packages exactly the degree and codegree conclusions required of
the random bisection in the robust matching lemma.  It also composes those
conclusions with the verified second-moment/Hall calculation, and provides
the finite-probability extraction of one good balanced link.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Degree and codegree bounds for the available relation across both
orientations of a balanced link. -/
def HasLinkDegreeCodegreeBounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (available : TripleSystemOn V) (K : BipartiteLink V)
    (d D codegree : ℕ) : Prop :=
  (∀ a : ↥K.left,
      d ≤ (relationNeighborsIn (linkAvailableRelation K available) univ a).card ∧
        (relationNeighborsIn (linkAvailableRelation K available) univ a).card ≤ D) ∧
  (∀ b : ↥K.right,
      d ≤ (relationNeighborsIn
        (transposeRelation (linkAvailableRelation K available)) univ b).card ∧
        (relationNeighborsIn
          (transposeRelation (linkAvailableRelation K available)) univ b).card ≤ D) ∧
  (∀ a a' : ↥K.left, a ≠ a' →
      (relationCommonNeighbors (linkAvailableRelation K available) a a').card ≤
        codegree) ∧
  (∀ b b' : ↥K.right, b ≠ b' →
      (relationCommonNeighbors
        (transposeRelation (linkAvailableRelation K available)) b b').card ≤
        codegree)

/-- The degree/codegree output of a good bisection supplies every oriented
small-Hall candidate count, subject only to the explicit scalar inequalities
from the Cauchy--Schwarz mixing calculation. -/
theorem HasLinkDegreeCodegreeBounds.orientedSmallHallCandidateBound
    {V : Type*} [Fintype V] [DecidableEq V]
    {available : TripleSystemOn V} {K : BipartiteLink V}
    {d D codegree : ℕ}
    (htyp : HasLinkDegreeCodegreeBounds available K d D codegree)
    (Delta groupSize density c cutoff : ℕ)
    (hbalanced : K.left.card = K.right.card)
    (hpositive : 0 < K.right.card)
    (hleftSecondMomentScalar :
      ∀ S : Finset ↥K.left, ∀ U : Finset ↥K.right, cutoff < S.card →
        K.right.card ^ 2 * (K.right.card - U.card) *
            (D * S.card + codegree * S.card * (S.card - 1)) <
          (K.right.card * d * S.card -
            density * S.card * U.card) ^ 2)
    (hrightSecondMomentScalar :
      ∀ S : Finset ↥K.right, ∀ U : Finset ↥K.left, cutoff < S.card →
        K.left.card ^ 2 * (K.left.card - U.card) *
            (D * S.card + codegree * S.card * (S.card - 1)) <
          (K.left.card * d * S.card -
            density * S.card * U.card) ^ 2)
    (hdegreeScalar : Delta * groupSize + groupSize ≤ d - cutoff)
    (hdensityScalar : K.right.card * c ≤
      density * (K.right.card / 2))
    (hcandidateScalar : Delta * groupSize + groupSize ≤ c) :
    ∀ o : OrientedSmallHallObstruction ↥K.left ↥K.right,
      (Delta * orientedSmallHallSize o + 1) * groupSize ≤
        (orientedSmallHallCandidates
          (linkAvailableRelation K available) o).card := by
  apply orientedSmallHallCandidateBound_of_degree_codegree
    (linkAvailableRelation K available) Delta groupSize d D codegree
      density c cutoff
  · simpa using hbalanced
  · simpa using hpositive
  · exact htyp.1
  · exact htyp.2.1
  · exact htyp.2.2.1
  · exact htyp.2.2.2
  · simpa using hleftSecondMomentScalar
  · simpa using hrightSecondMomentScalar
  · exact hdegreeScalar
  · simpa using hdensityScalar
  · exact hcandidateScalar

/-- A bisection outcome is good when its induced available link relation has
the required two-oriented degree and codegree bounds. -/
def IsGoodLinkBisection
    {V : Type*} [Fintype V] [DecidableEq V]
    (center : V) (W : Finset V) (hcenter : center ∉ W)
    (available : TripleSystemOn V) (d D codegree : ℕ)
    (B : BalancedBisection V W) : Prop :=
  HasLinkDegreeCodegreeBounds available
    (B.toBipartiteLink center hcenter) d D codegree

/-- If a uniformly random balanced bisection fails the degree/codegree
conditions with probability below one, one concrete good residual link
exists.  This is the exact extraction endpoint to which the hypergeometric
concentration estimate will be connected. -/
theorem exists_goodLinkBisection_of_failure_probability_lt_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (center : V) (W : Finset V) (hcenter : center ∉ W)
    (heven : Even W.card) (available : TripleSystemOn V)
    (d D codegree : ℕ)
    (hfailure :
      (BalancedBisection.uniformLaw W heven).probability
        (fun B ↦ ¬ IsGoodLinkBisection center W hcenter available
          d D codegree B) < 1) :
    ∃ K : BipartiteLink V,
      K.center = center ∧ K.left ∪ K.right = W ∧
      K.left.card = K.right.card ∧
      HasLinkDegreeCodegreeBounds available K d D codegree := by
  let bad : Fin 1 → BalancedBisection V W → Prop :=
    fun _ B ↦ ¬ IsGoodLinkBisection center W hcenter available
      d D codegree B
  have hsum :
      ∑ _i : Fin 1,
        (BalancedBisection.uniformLaw W heven).probability (bad _i) < 1 := by
    simpa [bad] using hfailure
  obtain ⟨B, hB⟩ :=
    BalancedBisection.exists_avoiding_of_sum_probability_lt_one
      W heven bad hsum
  let K := B.toBipartiteLink center hcenter
  refine ⟨K, rfl, B.toBipartiteLink_union center hcenter,
    B.toBipartiteLink_balanced center hcenter, ?_⟩
  exact not_not.mp (hB 0)

end

end Erdos207
