/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairAggregateTwoAwayAbsorberBound
import ErdosProblems.Erdos207.PairAggregateDeletionDrift

/-!
# Moment bound for aggregate two-away pair-star incidences

The ordered incidence relation is first transposed, so its target is the
triangle through the tracked pair.  It is then dominated by the aggregate
witness extension system constructed for the absorber forbidden family.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

lemma selectedCount_aggregatePairTwoAwayThreatRemainder_eq_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A : TripleSystemOn V) (P : PairOn V) :
    selectedCount
        (fun z : AggregatePairTwoAwayThreatWitness V F P ↦
          aggregatePairTwoAwayThreatRemainder z) A =
      ∑ U : TripleOn V,
        selectedCount
          (fun z : PairTwoAwayThreatWitness V F U P ↦
            pairTwoAwayThreatRemainder z) A := by
  unfold selectedCount AggregatePairTwoAwayThreatWitness
  rw [Fintype.sum_sigma]
  rfl

/-- The actual available incidence is dominated by the aggregate witness
count over the chosen partial system. -/
lemma pairStarAvailableTwoAwayIncidences_le_selectedCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (P : PairOn V) :
    (pairStarAvailableTwoAwayIncidences F S P.1 : ℝ≥0) ≤
      selectedCount
        (fun z : AggregatePairTwoAwayThreatWitness V F P ↦
          aggregatePairTwoAwayThreatRemainder z) S.chosen := by
  rw [pairStarAvailableTwoAwayIncidences_eq_transpose]
  have hlocal :
      (∑ T ∈ S.available,
        ((availableTrianglesContainingPair S P.1 ∩
          nonPairTwoAwayForbiddenTriangles F S.chosen T).card : ℝ≥0)) ≤
      ∑ T ∈ S.available,
        selectedCount
          (fun z : PairTwoAwayThreatWitness V F T P ↦
            pairTwoAwayThreatRemainder z) S.chosen := by
    apply sum_le_sum
    intro T hT
    calc
      ((availableTrianglesContainingPair S P.1 ∩
          nonPairTwoAwayForbiddenTriangles F S.chosen T).card : ℝ≥0) ≤
        ((pairTwoAwayForbiddenTriangles F S.chosen T P).card : ℝ≥0) := by
          exact_mod_cast card_le_card (by
            intro U hU
            obtain ⟨hUstar, hUnonpair⟩ := mem_inter.mp hU
            exact mem_inter.mpr
              ⟨mem_universeTriplesContainingPair_iff.mpr
                (mem_availableTrianglesContainingPair_iff.mp hUstar).2,
                hUnonpair⟩)
      _ ≤ selectedCount
          (fun z : PairTwoAwayThreatWitness V F T P ↦
            pairTwoAwayThreatRemainder z) S.chosen :=
        pairTwoAwayForbidden_count_le_selectedCount F S.chosen T P
  have huniv :
      (∑ T ∈ S.available,
        selectedCount
          (fun z : PairTwoAwayThreatWitness V F T P ↦
            pairTwoAwayThreatRemainder z) S.chosen) ≤
      ∑ T : TripleOn V,
        selectedCount
          (fun z : PairTwoAwayThreatWitness V F T P ↦
            pairTwoAwayThreatRemainder z) S.chosen := by
    calc
      _ ≤ ∑ T ∈ (univ : Finset (TripleOn V)),
          selectedCount
            (fun z : PairTwoAwayThreatWitness V F T P ↦
              pairTwoAwayThreatRemainder z) S.chosen :=
        sum_le_sum_of_subset_of_nonneg (subset_univ S.available)
          (fun _T _hT _ ↦ by positivity)
      _ = _ := by simp
  rw [Nat.cast_sum]
  exact hlocal.trans (huniv.trans_eq
    (selectedCount_aggregatePairTwoAwayThreatRemainder_eq_sum
      F S.chosen P).symm)

lemma card_aggregatePairTwoAwayThreatRemainder_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P : PairOn V} {k : ℕ}
    (hcard : ∀ C ∈ F, C.card ≤ k)
    (z : AggregatePairTwoAwayThreatWitness V F P) :
    (aggregatePairTwoAwayThreatRemainder z).card ≤ k - 2 :=
  card_pairTwoAwayThreatRemainder_le hcard z.2

/-- Generic moment estimate for the full genuinely two-away incidence in a
fixed pair star. -/
theorem pairStarAvailableTwoAwayIncidenceMomentBound
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Omega) (R : Omega → GreedyStateOn V)
    (F : ForbiddenFamilyOn V) (P : PairOn V)
    (pi : TripleOn V → ℝ≥0) (C kappa : ℝ≥0) {k s : ℕ}
    (hcard : ∀ A ∈ F, A.card ≤ k)
    (hkappa : HasExtensionBound
      (fun z : AggregatePairTwoAwayThreatWitness V F P ↦
        aggregatePairTwoAwayThreatRemainder z) pi kappa)
    (hjoint : ∀ T : TripleSystemOn V, T.card ≤ s * (k - 2) →
      L.probability (fun omega ↦ T ⊆ (R omega).chosen) ≤
        C * setWeight pi T) :
    L.expectation (fun omega ↦
      (pairStarAvailableTwoAwayIncidences F (R omega) P.1 : ℝ≥0) ^ s) ≤
      C * (((2 : ℝ≥0) ^ (s * (k - 2)) * kappa) ^ s) := by
  calc
    L.expectation (fun omega ↦
        (pairStarAvailableTwoAwayIncidences F (R omega) P.1 : ℝ≥0) ^ s) ≤
      L.expectation (fun omega ↦
        (selectedCount
          (fun z : AggregatePairTwoAwayThreatWitness V F P ↦
            aggregatePairTwoAwayThreatRemainder z)
          (R omega).chosen) ^ s) := by
        apply FiniteLaw.expectation_mono
        intro omega
        exact pow_le_pow_left'
          (pairStarAvailableTwoAwayIncidences_le_selectedCount F (R omega) P) s
    _ ≤ C * (((2 : ℝ≥0) ^ (s * (k - 2)) * kappa) ^ s) := by
      apply configurationMomentBound L
        (fun z : AggregatePairTwoAwayThreatWitness V F P ↦
          aggregatePairTwoAwayThreatRemainder z)
        (fun omega ↦ (R omega).chosen) pi C kappa
      · exact card_aggregatePairTwoAwayThreatRemainder_le hcard
      · exact hkappa
      · exact hjoint

end

end Erdos207
