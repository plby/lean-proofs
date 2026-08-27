/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.BipartiteCodegreeMoment

/-!
# Degree/codegree typicality gives robust Hall candidates

This file composes the exact double count, Cauchy--Schwarz mixing lemma, and
two-sided Hall reduction.  It is the finite natural-number counterpart of
KSSS equation (5.6) followed by the candidate-edge part of their robust
perfect matching lemma.
-/

namespace Erdos207

open Finset

/-- Two-sided degree/codegree bounds and explicit scalar slack imply the
oriented small-Hall candidate premise used by random sparsification. -/
theorem orientedSmallHallCandidateBound_of_degree_codegree
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (Delta groupSize d D codegree density c cutoff : ℕ)
    (hcard : Fintype.card A = Fintype.card B)
    (hpositive : 0 < Fintype.card B)
    (hleftDegree : ∀ a,
      d ≤ (relationNeighborsIn r univ a).card ∧
        (relationNeighborsIn r univ a).card ≤ D)
    (hrightDegree : ∀ b,
      d ≤ (relationNeighborsIn (transposeRelation r) univ b).card ∧
        (relationNeighborsIn (transposeRelation r) univ b).card ≤ D)
    (hleftCodegree : ∀ a a', a ≠ a' →
      (relationCommonNeighbors r a a').card ≤ codegree)
    (hrightCodegree : ∀ b b', b ≠ b' →
      (relationCommonNeighbors (transposeRelation r) b b').card ≤ codegree)
    (hleftSecondMomentScalar :
      ∀ S : Finset A, ∀ U : Finset B, cutoff < S.card →
        Fintype.card B ^ 2 * (Fintype.card B - U.card) *
            (D * S.card + codegree * S.card * (S.card - 1)) <
          (Fintype.card B * d * S.card -
            density * S.card * U.card) ^ 2)
    (hrightSecondMomentScalar :
      ∀ S : Finset B, ∀ U : Finset A, cutoff < S.card →
        Fintype.card A ^ 2 * (Fintype.card A - U.card) *
            (D * S.card + codegree * S.card * (S.card - 1)) <
          (Fintype.card A * d * S.card -
            density * S.card * U.card) ^ 2)
    (hdegreeScalar : Delta * groupSize + groupSize ≤ d - cutoff)
    (hdensityScalar : Fintype.card B * c ≤
      density * (Fintype.card B / 2))
    (hcandidateScalar : Delta * groupSize + groupSize ≤ c) :
    ∀ o : OrientedSmallHallObstruction A B,
      (Delta * orientedSmallHallSize o + 1) * groupSize ≤
        (orientedSmallHallCandidates r o).card := by
  have hleftBounds :=
    hasBipartiteDegreeSecondMomentBounds_of_degree_codegree
      r d D codegree hleftDegree hleftCodegree
  have hrightBounds :=
    hasBipartiteDegreeSecondMomentBounds_of_degree_codegree
      (transposeRelation r) d D codegree hrightDegree hrightCodegree
  have hleftMixing := normalizedLowerMixing_of_degree_secondMoment
    r d D codegree density cutoff hleftBounds hleftSecondMomentScalar
  have hrightMixing := normalizedLowerMixing_of_degree_secondMoment
    (transposeRelation r) d D codegree density cutoff hrightBounds
      hrightSecondMomentScalar
  exact orientedSmallHallCandidateBound_of_normalizedMixing
    r Delta groupSize d density c cutoff hcard hpositive
      (fun a ↦ (hleftDegree a).1) (fun b ↦ (hrightDegree b).1)
      hleftMixing hrightMixing hdegreeScalar hdensityScalar
      hcandidateScalar

end Erdos207
