/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.BipartiteHallMixing

/-!
# Normalized edge mixing implies Hall mixing

This file packages a denominator-free finite form of the typical-graph
mixing estimate.  A density numerator `density` means that every tested
rectangle `S × U` contains at least
`density * |S| * |U| / |B|` relation-pairs.
-/

namespace Erdos207

open Finset

/-- Denominator-free lower-density mixing on rectangles whose left side is
larger than `cutoff`. -/
def HasNormalizedBipartiteLowerMixing
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (density cutoff : ℕ) : Prop :=
  ∀ S : Finset A, ∀ U : Finset B,
    cutoff < S.card →
    density * S.card * U.card ≤
      Fintype.card B * (relationPairsBetween r S U).card

/-- Normalized rectangle mixing yields the linear escaping-edge estimate
needed by robust Hall.  The scalar inequality uses the smallest possible
right complement, namely `floor(|B| / 2)`. -/
theorem balancedHallLowerMixing_of_normalized
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (density c cutoff : ℕ)
    (hcard : Fintype.card A = Fintype.card B)
    (hpositive : 0 < Fintype.card B)
    (hmixing : HasNormalizedBipartiteLowerMixing r density cutoff)
    (hscalar : Fintype.card B * c ≤
      density * (Fintype.card B / 2)) :
    HasBalancedHallLowerMixing r c cutoff := by
  intro S U hScut hShalf hUlarge
  have hhalf : Fintype.card B / 2 ≤ U.card := by
    apply le_trans _ hUlarge
    rw [← hcard]
    omega
  have hscaled : Fintype.card B * (c * S.card) ≤
      Fintype.card B * (relationPairsBetween r S U).card := by
    calc
      Fintype.card B * (c * S.card) =
          (Fintype.card B * c) * S.card := by ring
      _ ≤ (density * (Fintype.card B / 2)) * S.card :=
        Nat.mul_le_mul_right _ hscalar
      _ ≤ (density * U.card) * S.card := by
        gcongr
      _ = density * S.card * U.card := by ring
      _ ≤ Fintype.card B * (relationPairsBetween r S U).card :=
        hmixing S U hScut
  exact Nat.le_of_mul_le_mul_left hscaled hpositive

/-- The full two-oriented candidate bound, expressed through minimum degree
and normalized rectangle mixing in each orientation. -/
theorem orientedSmallHallCandidateBound_of_normalizedMixing
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (Delta groupSize d density c cutoff : ℕ)
    (hcard : Fintype.card A = Fintype.card B)
    (hpositive : 0 < Fintype.card B)
    (hleftDegree : ∀ a, d ≤ (relationNeighborsIn r univ a).card)
    (hrightDegree : ∀ b,
      d ≤ (relationNeighborsIn (transposeRelation r) univ b).card)
    (hleftMixing : HasNormalizedBipartiteLowerMixing r density cutoff)
    (hrightMixing :
      HasNormalizedBipartiteLowerMixing (transposeRelation r)
        density cutoff)
    (hdegreeScalar : Delta * groupSize + groupSize ≤ d - cutoff)
    (hdensityScalar : Fintype.card B * c ≤
      density * (Fintype.card B / 2))
    (hcandidateScalar : Delta * groupSize + groupSize ≤ c) :
    ∀ o : OrientedSmallHallObstruction A B,
      (Delta * orientedSmallHallSize o + 1) * groupSize ≤
        (orientedSmallHallCandidates r o).card := by
  apply orientedSmallHallCandidateBound_of_degree_and_lowerMixing
    r Delta groupSize d c cutoff hcard hleftDegree hrightDegree
  · exact balancedHallLowerMixing_of_normalized r density c cutoff hcard
      hpositive hleftMixing hdensityScalar
  · exact balancedHallLowerMixing_of_normalized
      (transposeRelation r) density c cutoff hcard.symm
      (by simpa [hcard] using hpositive) hrightMixing (by
        simpa [hcard] using hdensityScalar)
  · exact hdegreeScalar
  · exact hcandidateScalar

end Erdos207
