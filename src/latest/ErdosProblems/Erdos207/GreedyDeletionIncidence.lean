/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AvailablePairDegree

/-!
# Averaged deletion incidences in the constrained greedy process

The pointwise deletion envelope is too wasteful late in the process.  This
file keeps only obstructions which are themselves currently available and
then sums the resulting bound over the uniformly chosen next triangle.  The
pair-sharing contribution is controlled by the current maximum pair degree;
the other contribution is the symmetric number of available two-away
incidences.  These identities are the global-availability input for the
differential-equation argument.
-/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

/-- Currently available triangles which are two-away partners of `U`. -/
def availableTwoAwayForbiddenTriangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (U : TripleOn V) :
    TripleSystemOn V :=
  S.available ∩ twoAwayForbiddenTriangles F S.chosen U

@[simp]
lemma mem_availableTwoAwayForbiddenTriangles_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T U : TripleOn V} :
    T ∈ availableTwoAwayForbiddenTriangles F S U ↔
      T ∈ S.available ∧ T ∈ twoAwayForbiddenTriangles F S.chosen U := by
  simp [availableTwoAwayForbiddenTriangles]

/-- Symmetry of the two-away relation persists after restricting both
endpoints to the current availability family. -/
lemma availableTwoAway_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {T U : TripleOn V} (hT : T ∈ S.available) (hU : U ∈ S.available) :
    T ∈ availableTwoAwayForbiddenTriangles F S U ↔
      U ∈ availableTwoAwayForbiddenTriangles F S T := by
  simp only [mem_availableTwoAwayForbiddenTriangles_iff, hT, hU, true_and]
  exact mem_twoAwayForbiddenTriangles_comm

/-- Total number of ordered available two-away incidences. -/
def totalAvailableTwoAwayIncidences
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) : ℕ :=
  ∑ U : S.available,
    (availableTwoAwayForbiddenTriangles F S U.1).card

/-- After both branches are intersected with current availability, they
still cover every triangle deleted in a legal step. -/
theorem greedyDeleted_available_subset_availablePair_union_availableTwoAway
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {U : TripleOn V}
    (hInv : GreedyInvariant F S) (hU : U ∈ S.available) :
    greedyDeletedIn F (univ : TripleSystemOn V) S U ⊆
      (S.available ∩ triplesSharingPair U) ∪
        availableTwoAwayForbiddenTriangles F S U := by
  intro T hT
  have hTavailable : T ∈ S.available := by
    have hold := (mem_sdiff.mp hT).1
    simpa [greedyAvailableIn] using hold
  rcases mem_union.mp
      (greedyDeletedIn_subset_pairSharing_union_twoAway hInv hU hT) with
    hpair | htwo
  · exact mem_union.mpr (Or.inl (mem_inter.mpr ⟨hTavailable, hpair⟩))
  · exact mem_union.mpr (Or.inr
      (mem_availableTwoAwayForbiddenTriangles_iff.mpr
        ⟨hTavailable, htwo⟩))

/-- Pointwise incidence bound with both obstruction families restricted to
the current availability family. -/
theorem card_greedyDeleted_available_le_availableIncidences
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {U : TripleOn V}
    (hInv : GreedyInvariant F S) (hU : U ∈ S.available) :
    (greedyDeletedIn F (univ : TripleSystemOn V) S U).card ≤
      (S.available ∩ triplesSharingPair U).card +
        (availableTwoAwayForbiddenTriangles F S U).card := by
  exact (card_le_card
    (greedyDeleted_available_subset_availablePair_union_availableTwoAway
      hInv hU)).trans (card_union_le _ _)

/-- Summing over all possible next choices turns the two-away contribution
into the global ordered-incidence count. -/
theorem sum_card_greedyDeleted_available_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {Δ : ℕ}
    (hInv : GreedyInvariant F S) (hpair : HasAvailablePairCutoff Δ S) :
    (∑ U : S.available,
        (greedyDeletedIn F (univ : TripleSystemOn V) S U.1).card) ≤
      S.available.card * (3 * Δ) +
        totalAvailableTwoAwayIncidences F S := by
  calc
    (∑ U : S.available,
        (greedyDeletedIn F (univ : TripleSystemOn V) S U.1).card) ≤
        ∑ U : S.available,
          (3 * Δ +
            (availableTwoAwayForbiddenTriangles F S U.1).card) := by
      apply sum_le_sum
      intro U _
      exact (card_greedyDeleted_available_le_availableIncidences
        hInv U.2).trans (Nat.add_le_add_right
          (card_available_inter_triplesSharingPair_le hpair U.1) _)
    _ = S.available.card * (3 * Δ) +
        totalAvailableTwoAwayIncidences F S := by
      rw [sum_add_distrib]
      simp [totalAvailableTwoAwayIncidences]

/-- The exact global-availability drift is bounded below by the averaged
pair and two-away incidence envelope. -/
theorem greedyKernel_expectationReal_availableCount_increment_ge_incidence
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {Δ : ℕ}
    (hInv : GreedyInvariant F S) (hpair : HasAvailablePairCutoff Δ S)
    (hA : S.available.Nonempty) :
    -((S.available.card : ℝ)⁻¹) *
        ((S.available.card * (3 * Δ) +
          totalAvailableTwoAwayIncidences F S : ℕ) : ℝ) ≤
      (greedyKernel F S).expectationReal
        (fun S' ↦ greedyAvailableCountReal
            (univ : TripleSystemOn V) S' -
          greedyAvailableCountReal (univ : TripleSystemOn V) S) := by
  rw [greedyKernel_expectationReal_availableCount_increment F
    (univ : TripleSystemOn V) S hA]
  have hsum := sum_card_greedyDeleted_available_le hInv hpair
  have hsumReal :
      (∑ U : S.available,
          ((greedyDeletedIn F (univ : TripleSystemOn V) S U.1).card : ℝ)) ≤
        ((S.available.card * (3 * Δ) +
          totalAvailableTwoAwayIncidences F S : ℕ) : ℝ) := by
    exact_mod_cast hsum
  have hinv : (0 : ℝ) ≤ (S.available.card : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hsumReal hinv]

/-- A pointwise jump bound converts the first incidence moment into a
second-moment bound. -/
theorem greedyKernel_expectationReal_availableCount_sqIncrement_le_incidence
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {Δ K : ℕ}
    (hInv : GreedyInvariant F S) (hpair : HasAvailablePairCutoff Δ S)
    (htwo : HasTwoAwayCutoff F K S) (hA : S.available.Nonempty) :
    (greedyKernel F S).expectationReal
        (fun S' ↦ (greedyAvailableCountReal
            (univ : TripleSystemOn V) S' -
          greedyAvailableCountReal (univ : TripleSystemOn V) S) ^ 2) ≤
      ((3 * Δ + K : ℕ) : ℝ) * (S.available.card : ℝ)⁻¹ *
        ((S.available.card * (3 * Δ) +
          totalAvailableTwoAwayIncidences F S : ℕ) : ℝ) := by
  rw [greedyKernel_expectationReal_availableCount_sqIncrement F
    (univ : TripleSystemOn V) S hA]
  let d : S.available → ℕ := fun U ↦
    (greedyDeletedIn F (univ : TripleSystemOn V) S U.1).card
  have hd (U : S.available) : d U ≤ 3 * Δ + K :=
    card_greedyDeleted_available_le_pairCutoff hInv hpair htwo U.2
  have hsquares :
      (∑ U : S.available, ((d U : ℝ) ^ 2)) ≤
        ((3 * Δ + K : ℕ) : ℝ) *
          ∑ U : S.available, (d U : ℝ) := by
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro U _
    have hdReal : (d U : ℝ) ≤ ((3 * Δ + K : ℕ) : ℝ) := by
      exact_mod_cast hd U
    have hdNonneg : (0 : ℝ) ≤ d U := by positivity
    nlinarith
  have hsum := sum_card_greedyDeleted_available_le hInv hpair
  have hsumReal :
      (∑ U : S.available, (d U : ℝ)) ≤
        ((S.available.card * (3 * Δ) +
          totalAvailableTwoAwayIncidences F S : ℕ) : ℝ) := by
    exact_mod_cast hsum
  have hcoef : (0 : ℝ) ≤ ((3 * Δ + K : ℕ) : ℝ) := by positivity
  have hsecond := hsquares.trans
    (mul_le_mul_of_nonneg_left hsumReal hcoef)
  have hinv : (0 : ℝ) ≤ (S.available.card : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  change (S.available.card : ℝ)⁻¹ *
      ∑ U : S.available, ((d U : ℝ) ^ 2) ≤ _
  calc
    (S.available.card : ℝ)⁻¹ *
        ∑ U : S.available, ((d U : ℝ) ^ 2) ≤
      (S.available.card : ℝ)⁻¹ *
        (((3 * Δ + K : ℕ) : ℝ) *
          ((S.available.card * (3 * Δ) +
            totalAvailableTwoAwayIncidences F S : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hsecond hinv
    _ = _ := by ring

end

end Erdos207
