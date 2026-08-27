/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TwoSidedRandomRobustMatching

/-!
# From bipartite mixing to the two-sided Hall candidate bound

The KSSS robust matching proof has two quantitative regimes.  Very small
left sets use minimum degree.  Larger sets, still no larger than half of a
balanced side, use the typical-graph mixing estimate against the complement
of the proposed Hall set.  This file isolates that exact deterministic
argument.
-/

namespace Erdos207

open Finset

/-- A lower mixing estimate strong enough for all non-small Hall sets.  If
`S` has more than `cutoff` vertices and at most rounded-up half of the left
side, every right set of the minimum size forced by a Hall obstruction spans
at least `c * |S|` relation-pairs with `S`. -/
def HasBalancedHallLowerMixing
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (c cutoff : ℕ) : Prop :=
  ∀ S : Finset A, ∀ U : Finset B,
    cutoff < S.card →
    2 * S.card ≤ Fintype.card A + 1 →
    Fintype.card B + 1 - S.card ≤ U.card →
    c * S.card ≤ (relationPairsBetween r S U).card

/-- Minimum degree handles small sets and lower mixing handles the remaining
half-size sets, yielding the exact candidate-group bound for one
orientation. -/
theorem smallHallCandidateBound_of_degree_and_lowerMixing
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (Delta groupSize d c cutoff : ℕ)
    (hcard : Fintype.card A = Fintype.card B)
    (hdegree : ∀ a, d ≤ (relationNeighborsIn r univ a).card)
    (hmixing : HasBalancedHallLowerMixing r c cutoff)
    (hdegreeScalar : Delta * groupSize + groupSize ≤ d - cutoff)
    (hmixingScalar : Delta * groupSize + groupSize ≤ c) :
    SmallHallCandidateBound r Delta groupSize := by
  intro S T hTS hSsmall
  by_cases hScut : S.card ≤ cutoff
  · exact smallHallCandidateBound_of_left_degree r Delta groupSize d
      cutoff hdegree hdegreeScalar S T hTS hScut
  · have hTcard : T.card ≤ Fintype.card B := by
      simpa using T.card_le_univ
    have hUcard : (univ \ T : Finset B).card =
        Fintype.card B - T.card := by
      simp [card_sdiff_of_subset (subset_univ T)]
    have hUlarge : Fintype.card B + 1 - S.card ≤
        (univ \ T : Finset B).card := by
      rw [hUcard]
      have hScard : S.card ≤ Fintype.card A := by
        simpa using S.card_le_univ
      rw [hcard] at hScard
      omega
    rw [relationPairsLeaving_eq_between_sdiff]
    refine le_trans ?_ (hmixing S (univ \ T) (by omega)
      hSsmall hUlarge)
    have hnonempty : 1 ≤ S.card := by omega
    calc
      (Delta * S.card + 1) * groupSize =
          Delta * groupSize * S.card + groupSize := by ring
      _ ≤ (Delta * groupSize + groupSize) * S.card := by nlinarith
      _ ≤ c * S.card := Nat.mul_le_mul_right _ hmixingScalar

/-- Applying the preceding theorem in both orientations produces the exact
candidate premise of the two-sided random robust matching theorem. -/
theorem orientedSmallHallCandidateBound_of_degree_and_lowerMixing
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (Delta groupSize d c cutoff : ℕ)
    (hcard : Fintype.card A = Fintype.card B)
    (hleftDegree : ∀ a, d ≤ (relationNeighborsIn r univ a).card)
    (hrightDegree : ∀ b,
      d ≤ (relationNeighborsIn (transposeRelation r) univ b).card)
    (hleftMixing : HasBalancedHallLowerMixing r c cutoff)
    (hrightMixing :
      HasBalancedHallLowerMixing (transposeRelation r) c cutoff)
    (hdegreeScalar : Delta * groupSize + groupSize ≤ d - cutoff)
    (hmixingScalar : Delta * groupSize + groupSize ≤ c) :
    ∀ o : OrientedSmallHallObstruction A B,
      (Delta * orientedSmallHallSize o + 1) * groupSize ≤
        (orientedSmallHallCandidates r o).card := by
  have hleft := smallHallCandidateBound_of_degree_and_lowerMixing
    r Delta groupSize d c cutoff hcard hleftDegree hleftMixing
      hdegreeScalar hmixingScalar
  have hright := smallHallCandidateBound_of_degree_and_lowerMixing
    (transposeRelation r) Delta groupSize d c cutoff hcard.symm
      hrightDegree hrightMixing hdegreeScalar hmixingScalar
  intro o
  rcases o with o | o
  · rw [card_orientedSmallHallCandidates_left]
    exact hleft o.1.1.1 o.1.1.2 o.1.2 o.2
  · rw [card_orientedSmallHallCandidates_right]
    exact hright o.1.1.1 o.1.1.2 o.1.2 o.2

end Erdos207
