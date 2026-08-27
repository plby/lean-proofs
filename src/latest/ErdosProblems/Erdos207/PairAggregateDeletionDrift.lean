/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairExtensionDeletionDrift
import ErdosProblems.Erdos207.PairTwoAwayCutoff
import ErdosProblems.Erdos207.AlivePairVariance

/-!
# Aggregate two-away incidence in one available pair star

The maximum two-away degree is needed to bound a single greedy jump, but it
must not be multiplied by the size of a tracked pair star in the drift
estimate.  This file separates the two roles.  After transposing the ordered
deletion relation, all genuinely two-away selectors of all targets in one
pair star are charged once to a single aggregate statistic.
-/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

/-- Ordered genuinely two-away incidences whose target lies in the available
star over `P` and whose selector is also currently available. -/
def pairStarAvailableTwoAwayIncidences
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (P : Finset V) : ℕ :=
  ∑ U ∈ availableTrianglesContainingPair S P,
    (S.available ∩
      nonPairTwoAwayForbiddenTriangles F S.chosen U).card

/-- Uniform aggregate genuinely two-away cutoff for every vertex pair. -/
def HasPairStarTwoAwayIncidenceCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (K : ℕ) (S : GreedyStateOn V) : Prop :=
  ∀ P : Finset V, P.card = 2 →
    pairStarAvailableTwoAwayIncidences F S P ≤ K

lemma mem_nonPairTwoAwayForbiddenTriangles_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V}
    {T U : TripleOn V} :
    T ∈ nonPairTwoAwayForbiddenTriangles F A U ↔
      U ∈ nonPairTwoAwayForbiddenTriangles F A T := by
  simp only [nonPairTwoAwayForbiddenTriangles, mem_sdiff]
  have hpair : T ∈ triplesSharingPair U ↔ U ∈ triplesSharingPair T := by
    rw [mem_triplesSharingPair_iff, mem_triplesSharingPair_iff]
    simp [inter_comm]
  constructor
  · rintro ⟨htwo, hnot⟩
    exact ⟨mem_twoAwayForbiddenTriangles_comm.mp htwo,
      fun h ↦ hnot (hpair.mpr h)⟩
  · rintro ⟨htwo, hnot⟩
    exact ⟨mem_twoAwayForbiddenTriangles_comm.mpr htwo,
      fun h ↦ hnot (hpair.mp h)⟩

/-- Transpose the available genuinely two-away relation in one pair star. -/
theorem pairStarAvailableTwoAwayIncidences_eq_transpose
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (P : Finset V) :
    pairStarAvailableTwoAwayIncidences F S P =
      ∑ T ∈ S.available,
        (availableTrianglesContainingPair S P ∩
          nonPairTwoAwayForbiddenTriangles F S.chosen T).card := by
  classical
  unfold pairStarAvailableTwoAwayIncidences
  calc
    (∑ U ∈ availableTrianglesContainingPair S P,
        (S.available ∩
          nonPairTwoAwayForbiddenTriangles F S.chosen U).card) =
      ∑ U ∈ availableTrianglesContainingPair S P,
        ∑ T ∈ S.available,
          if T ∈ nonPairTwoAwayForbiddenTriangles F S.chosen U
          then 1 else 0 := by
        apply sum_congr rfl
        intro U _hU
        rw [card_eq_sum_ones, ← sum_filter]
        congr 1
    _ = ∑ T ∈ S.available,
        ∑ U ∈ availableTrianglesContainingPair S P,
          if T ∈ nonPairTwoAwayForbiddenTriangles F S.chosen U
          then 1 else 0 := by
        rw [sum_comm]
    _ = ∑ T ∈ S.available,
        ∑ U ∈ availableTrianglesContainingPair S P,
          if U ∈ nonPairTwoAwayForbiddenTriangles F S.chosen T
          then 1 else 0 := by
        apply sum_congr rfl
        intro T _hT
        apply sum_congr rfl
        intro U _hU
        simp only [mem_nonPairTwoAwayForbiddenTriangles_comm]
    _ = ∑ T ∈ S.available,
        (availableTrianglesContainingPair S P ∩
          nonPairTwoAwayForbiddenTriangles F S.chosen T).card := by
        apply sum_congr rfl
        intro T _hT
        rw [card_eq_sum_ones, ← sum_filter]
        congr 1

/-- The pair-local two-away cutoff bounds every fiber after transposing the
ordered incidence relation.  If the selector itself contains the tracked
pair, the genuinely two-away fiber is empty. -/
lemma card_pairStar_inter_nonPairTwoAway_le_pairCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {K : ℕ}
    (hpairTwo : HasPairTwoAwayCutoff F K S) {T : TripleOn V}
    (hT : T ∈ S.available) :
    (availableTrianglesContainingPair S P ∩
      nonPairTwoAwayForbiddenTriangles F S.chosen T).card ≤ K := by
  by_cases hPT : P ⊆ T.1
  · have hempty : availableTrianglesContainingPair S P ∩
        nonPairTwoAwayForbiddenTriangles F S.chosen T = ∅ := by
      rw [← not_nonempty_iff_eq_empty]
      rintro ⟨U, hU⟩
      obtain ⟨hUstar, hUnon⟩ := mem_inter.mp hU
      have hPU := (mem_availableTrianglesContainingPair_iff.mp hUstar).2
      have hPinter : P ⊆ U.1 ∩ T.1 := by
        intro x hx
        exact mem_inter.mpr ⟨hPU hx, hPT hx⟩
      have hinter : 1 < (U.1 ∩ T.1).card := by
        have := card_le_card hPinter
        omega
      apply (mem_sdiff.mp hUnon).2
      rw [mem_triplesSharingPair_iff]
      have hinter' : 2 ≤ (U.1 ∩ T.1).card := by omega
      simpa only [inter_comm] using hinter'
    simp [hempty]
  · exact hpairTwo T hT P hP hPT

/-- The total genuinely two-away incidence of a tracked pair star is at
most the current number of available selectors times the pair-local cutoff.
This is the state-scaled estimate needed in the sparse phase. -/
theorem pairStarAvailableTwoAwayIncidences_le_available_mul_pairCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {K : ℕ}
    (hpairTwo : HasPairTwoAwayCutoff F K S) :
    pairStarAvailableTwoAwayIncidences F S P ≤ S.available.card * K := by
  rw [pairStarAvailableTwoAwayIncidences_eq_transpose]
  calc
    (∑ T ∈ S.available,
        (availableTrianglesContainingPair S P ∩
          nonPairTwoAwayForbiddenTriangles F S.chosen T).card) ≤
      ∑ _T ∈ S.available, K := by
        apply sum_le_sum
        intro T hT
        exact card_pairStar_inter_nonPairTwoAway_le_pairCutoff hP hpairTwo hT
    _ = S.available.card * K := by simp

/-- The aggregate incidence in one pair star is bounded deterministically by
the size of that star times the global two-away cutoff.  This observation is
useful in the long outer phase: it avoids paying for a separate, much coarser
quadratic extension-weight estimate. -/
lemma pairStarAvailableTwoAwayIncidences_le_card_mul_of_twoAwayCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {K : ℕ}
    (hglobal : HasTwoAwayCutoff F K S) (P : Finset V) :
    pairStarAvailableTwoAwayIncidences F S P ≤
      (availableTrianglesContainingPair S P).card * K := by
  unfold pairStarAvailableTwoAwayIncidences
  calc
    ∑ U ∈ availableTrianglesContainingPair S P,
        (S.available ∩
          nonPairTwoAwayForbiddenTriangles F S.chosen U).card ≤
      ∑ _U ∈ availableTrianglesContainingPair S P, K := by
        apply sum_le_sum
        intro U hU
        have hUavailable : U ∈ S.available :=
          (mem_availableTrianglesContainingPair_iff.mp hU).1
        exact (card_le_card (inter_subset_right.trans sdiff_subset)).trans
          (hglobal U hUavailable)
    _ = (availableTrianglesContainingPair S P).card * K := by simp

/-- A tracked pair-codegree cutoff and the global two-away cutoff imply the
aggregate pair-star cutoff used in the lower drift estimate. -/
theorem HasAvailablePairCutoff.hasPairStarTwoAwayIncidenceCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {Δ K Kinc : ℕ}
    (hpair : HasAvailablePairCutoff Δ S)
    (hglobal : HasTwoAwayCutoff F K S) (hproduct : Δ * K ≤ Kinc) :
    HasPairStarTwoAwayIncidenceCutoff F Kinc S := by
  intro P hP
  exact (pairStarAvailableTwoAwayIncidences_le_card_mul_of_twoAwayCutoff
    hglobal P).trans ((Nat.mul_le_mul_right K (hpair P hP)).trans hproduct)

/-- For a fixed available target, deleting selectors are covered by the
pair-sharing selectors and the genuinely two-away available selectors. -/
theorem deletingSelectors_subset_pairSharing_union_availableNonPairTwoAway
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {Q : TripleSystemOn V}
    {S : GreedyStateOn V} (hS : GreedyInvariant F S) (U : TripleOn V) :
    deletingSelectors F Q S U ⊆
      (S.available ∩ triplesSharingPair U) ∪
        (S.available ∩
          nonPairTwoAwayForbiddenTriangles F S.chosen U) := by
  intro T hT
  have hTavailable : T ∈ S.available := (mem_filter.mp hT).1
  rcases mem_union.mp
      (deletingSelectors_subset_pairSharing_union_twoAway hS U hT) with
    hshare | htwo
  · exact mem_union.mpr (Or.inl hshare)
  · by_cases hpair : T ∈ triplesSharingPair U
    · exact mem_union.mpr (Or.inl (mem_inter.mpr ⟨hTavailable, hpair⟩))
    · exact mem_union.mpr (Or.inr (mem_inter.mpr
        ⟨hTavailable, mem_sdiff.mpr ⟨htwo, hpair⟩⟩))

/-- The ordered deletion incidence of one pair star has an additive, rather
than multiplicative, genuinely two-away term. -/
theorem sum_deletions_le_pairStar_pairSharing_add_twoAwayIncidences
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} {Delta : ℕ}
    (hS : GreedyInvariant F S) (hpair : HasAvailablePairCutoff Delta S) :
    (∑ T : S.available,
        (greedyDeletedIn F
          (availableTrianglesContainingPair S P) S T.1).card) ≤
      (availableTrianglesContainingPair S P).card * (3 * Delta) +
        pairStarAvailableTwoAwayIncidences F S P := by
  let Q := availableTrianglesContainingPair S P
  have hQsub : Q ⊆ S.available := by
    intro U hU
    exact (mem_availableTrianglesContainingPair_iff.mp hU).1
  have hgreedyQ : greedyAvailableIn Q S = Q := inter_eq_right.mpr hQsub
  have htranspose := sum_card_greedyDeletedIn_eq_sum_card_deletingSelectors
    F Q S
  rw [hgreedyQ] at htranspose
  have hbound : ∑ U ∈ Q, (deletingSelectors F Q S U).card ≤
      ∑ U ∈ Q,
        (3 * Delta +
          (S.available ∩
            nonPairTwoAwayForbiddenTriangles F S.chosen U).card) := by
    apply sum_le_sum
    intro U hU
    calc
      (deletingSelectors F Q S U).card ≤
          (S.available ∩ triplesSharingPair U).card +
            (S.available ∩
              nonPairTwoAwayForbiddenTriangles F S.chosen U).card :=
        (card_le_card
          (deletingSelectors_subset_pairSharing_union_availableNonPairTwoAway
            hS U)).trans (card_union_le _ _)
      _ ≤ 3 * Delta +
            (S.available ∩
              nonPairTwoAwayForbiddenTriangles F S.chosen U).card :=
        Nat.add_le_add_right
          (card_available_inter_triplesSharingPair_le hpair U) _
  have hsubtype :
      (∑ T ∈ S.available, (greedyDeletedIn F Q S T).card) =
        ∑ T : S.available, (greedyDeletedIn F Q S T.1).card := by
    rw [Finset.univ_eq_attach]
    exact (Finset.sum_attach S.available
      (fun T ↦ (greedyDeletedIn F Q S T).card)).symm
  rw [← htranspose, hsubtype] at hbound
  simpa [Q, pairStarAvailableTwoAwayIncidences, sum_add_distrib] using hbound

/-- The aggregate cutoff gives the pair-star drift envelope
`3 Delta d + Kinc`. -/
theorem sum_deletions_le_pairStar_add_aggregateCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} {Delta Kinc : ℕ}
    (hS : GreedyInvariant F S) (hpair : HasAvailablePairCutoff Delta S)
    (hinc : HasPairStarTwoAwayIncidenceCutoff F Kinc S)
    (hP : P.card = 2) :
    (∑ T : S.available,
        (greedyDeletedIn F
          (availableTrianglesContainingPair S P) S T.1).card) ≤
      (availableTrianglesContainingPair S P).card * (3 * Delta) + Kinc :=
  (sum_deletions_le_pairStar_pairSharing_add_twoAwayIncidences hS hpair).trans
    (Nat.add_le_add_left (hinc P hP) _)

/-- Conditional pair-star drift with the additive aggregate cutoff. -/
theorem greedyKernel_expectationReal_pairStar_increment_ge_aggregateCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} {Delta Kinc : ℕ}
    (hS : GreedyInvariant F S) (hA : S.available.Nonempty)
    (hpair : HasAvailablePairCutoff Delta S)
    (hinc : HasPairStarTwoAwayIncidenceCutoff F Kinc S)
    (hP : P.card = 2) :
    -(S.available.card : ℝ)⁻¹ *
        (((availableTrianglesContainingPair S P).card : ℝ) *
            (3 * Delta : ℕ) + Kinc) ≤
      (greedyKernel F S).expectationReal
        (fun S' ↦ greedyAvailableCountReal
            (availableTrianglesContainingPair S P) S' -
          greedyAvailableCountReal
            (availableTrianglesContainingPair S P) S) := by
  rw [greedyKernel_expectationReal_availableCount_increment
    F (availableTrianglesContainingPair S P) S hA]
  apply mul_le_mul_of_nonpos_left
  · exact_mod_cast sum_deletions_le_pairStar_add_aggregateCutoff
      hS hpair hinc hP
  · exact neg_nonpos.mpr (by positivity)

/-- The global maximum cutoff is used only as a one-step jump bound; the
first incidence moment uses the additive pair-star aggregate cutoff. -/
theorem greedyKernel_expectationReal_pairStar_sqIncrement_le_mixedCutoffs
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} {Delta Kglobal Kinc : ℕ}
    (hS : GreedyInvariant F S) (hA : S.available.Nonempty)
    (hpair : HasAvailablePairCutoff Delta S)
    (hglobal : HasTwoAwayCutoff F Kglobal S)
    (hinc : HasPairStarTwoAwayIncidenceCutoff F Kinc S)
    (hP : P.card = 2) :
    (greedyKernel F S).expectationReal
        (fun S' ↦ (greedyAvailableCountReal
            (availableTrianglesContainingPair S P) S' -
          greedyAvailableCountReal
            (availableTrianglesContainingPair S P) S) ^ 2) ≤
      (S.available.card : ℝ)⁻¹ *
        (((3 * Delta + Kglobal : ℕ) : ℝ) *
          (((availableTrianglesContainingPair S P).card : ℝ) *
            (3 * Delta : ℕ) + Kinc)) := by
  rw [greedyKernel_expectationReal_availableCount_sqIncrement
    F (availableTrianglesContainingPair S P) S hA]
  apply mul_le_mul_of_nonneg_left
  · have hsq : ∑ T : S.available,
        (greedyDeletedIn F
          (availableTrianglesContainingPair S P) S T.1).card ^ 2 ≤
      (3 * Delta + Kglobal) * ∑ T : S.available,
        (greedyDeletedIn F
          (availableTrianglesContainingPair S P) S T.1).card := by
      rw [Finset.mul_sum]
      apply sum_le_sum
      intro T _hT
      have hd := card_greedyDeletedIn_le_pairCutoff
        hS hpair hglobal T.2
        (Q := availableTrianglesContainingPair S P)
      nlinarith
    have hsum := sum_deletions_le_pairStar_add_aggregateCutoff
      hS hpair hinc hP
    have hnat : ∑ T : S.available,
        (greedyDeletedIn F
          (availableTrianglesContainingPair S P) S T.1).card ^ 2 ≤
      (3 * Delta + Kglobal) *
        ((availableTrianglesContainingPair S P).card * (3 * Delta) + Kinc) :=
      hsq.trans (Nat.mul_le_mul_left _ hsum)
    exact_mod_cast hnat
  · positivity

/-- Fixed-initial-state form of the additive aggregate drift bound. -/
theorem greedyKernel_expectationReal_fixedPair_increment_ge_aggregateCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S0 S : GreedyStateOn V}
    {P : Finset V} {Delta Kinc : ℕ}
    (hS : PairTrajectoryInvariant F S0 S) (hA : S.available.Nonempty)
    (hpair : HasAvailablePairCutoff Delta S)
    (hinc : HasPairStarTwoAwayIncidenceCutoff F Kinc S)
    (hP : P.card = 2) :
    -(S.available.card : ℝ)⁻¹ *
        (((availableTrianglesContainingPair S P).card : ℝ) *
            (3 * Delta : ℕ) + Kinc) ≤
      (greedyKernel F S).expectationReal
        (fun S' ↦ fixedPairAvailableCountReal S0 P S' -
          fixedPairAvailableCountReal S0 P S) := by
  rw [greedyKernel_expectationReal_fixedPair_increment_eq_current
    F S0 S P hS.2]
  exact greedyKernel_expectationReal_pairStar_increment_ge_aggregateCutoff
    hS.1 hA hpair hinc hP

/-- Survival-masked second moment with the local jump cutoff and aggregate
pair-star first incidence moment. -/
theorem greedyKernel_expectationReal_fixedPair_sqIncrement_if_alive_le_mixedCutoffs
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S0 S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2)
    {Delta Kpair Kinc : ℕ}
    (hS : PairTrajectoryInvariant F S0 S) (hA : S.available.Nonempty)
    (hpair : HasAvailablePairCutoff Delta S)
    (hpairTwo : HasPairTwoAwayCutoff F Kpair S)
    (hinc : HasPairStarTwoAwayIncidenceCutoff F Kinc S) :
    (greedyKernel F S).expectationReal (fun S' ↦
        if PairAlive P S' then
          (fixedPairAvailableCountReal S0 P S' -
            fixedPairAvailableCountReal S0 P S) ^ 2
        else 0) ≤
      (S.available.card : ℝ)⁻¹ *
        (((3 + Kpair : ℕ) : ℝ) *
          (((availableTrianglesContainingPair S P).card : ℝ) *
            (3 * Delta : ℕ) + Kinc)) := by
  rw [greedyKernel_expectationReal_of_nonempty F S hA]
  apply mul_le_mul_of_nonneg_left
  · calc
      ∑ T : S.available,
          (if PairAlive P (greedyStep F S T.1) then
              (fixedPairAvailableCountReal S0 P (greedyStep F S T.1) -
                fixedPairAvailableCountReal S0 P S) ^ 2
            else 0) ≤
        ∑ T : S.available,
          ((3 + Kpair : ℕ) : ℝ) *
            (greedyDeletedIn F
              (availableTrianglesContainingPair S P) S T.1).card := by
          apply sum_le_sum
          intro T _hT
          exact fixedPair_sqIncrement_if_alive_step_le_of_pairCutoff
            hP hS T.2 hpairTwo
      _ = ((3 + Kpair : ℕ) : ℝ) *
          ∑ T : S.available,
            ((greedyDeletedIn F
              (availableTrianglesContainingPair S P) S T.1).card : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ ((3 + Kpair : ℕ) : ℝ) *
          (((availableTrianglesContainingPair S P).card : ℝ) *
            (3 * Delta : ℕ) + Kinc) := by
          apply mul_le_mul_of_nonneg_left
          · exact_mod_cast sum_deletions_le_pairStar_add_aggregateCutoff
              hS.1 hpair hinc hP
          · positivity
  · positivity

/-- Among selectors which do not cover the tracked pair, pair-sharing with a
target in its pair star can occur through only the target's other two pairs.
This is the factor two which is hidden if pair-killing transitions are kept
inside the lower-tail drift calculation. -/
theorem card_nonPairSelectors_inter_triplesSharingPair_le_two_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    {S : GreedyStateOn V} {P : Finset V} {U : TripleOn V} {Delta : ℕ}
    (hP : P.card = 2) (hPU : P ⊆ U.1)
    (hpair : HasAvailablePairCutoff Delta S) :
    (nonPairSelectors S P ∩ triplesSharingPair U).card ≤ 2 * Delta := by
  let pairs := (U.1.powersetCard 2).erase P
  have hPmem : P ∈ U.1.powersetCard 2 :=
    mem_powersetCard.mpr ⟨hPU, hP⟩
  have hpairsCard : pairs.card = 2 := by
    simp only [pairs, card_erase_of_mem hPmem, card_powersetCard, U.2]
    norm_num
  have hsub : nonPairSelectors S P ∩ triplesSharingPair U ⊆
      pairs.biUnion fun R ↦ availableTrianglesContainingPair S R := by
    intro T hT
    have hTnon := mem_filter.mp (mem_inter.mp hT).1
    have hshare := triplesSharingPair_subset_pair_union U (mem_inter.mp hT).2
    obtain ⟨R, hRU, hTR⟩ := mem_biUnion.mp hshare
    have hRne : R ≠ P := by
      intro hRP
      subst R
      exact hTnon.2 (mem_universeTriplesContainingPair_iff.mp hTR)
    apply mem_biUnion.mpr
    refine ⟨R, mem_erase.mpr ⟨hRne, hRU⟩, ?_⟩
    exact mem_availableTrianglesContainingPair_iff.mpr
      ⟨hTnon.1, mem_universeTriplesContainingPair_iff.mp hTR⟩
  calc
    (nonPairSelectors S P ∩ triplesSharingPair U).card ≤
        (pairs.biUnion fun R ↦
          availableTrianglesContainingPair S R).card := card_le_card hsub
    _ ≤ ∑ R ∈ pairs,
        (availableTrianglesContainingPair S R).card := card_biUnion_le
    _ ≤ ∑ _R ∈ pairs, Delta := by
      apply sum_le_sum
      intro R hR
      exact hpair R (mem_powersetCard.mp (mem_of_mem_erase hR)).2
    _ = 2 * Delta := by simp [hpairsCard]

/-- Transpose deletion incidences after discarding selectors which cover the
tracked pair. -/
theorem sum_nonPairSelectors_deletions_eq_sum_targets
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (P : Finset V)
    (Q : TripleSystemOn V) :
    (∑ T ∈ nonPairSelectors S P,
        (greedyDeletedIn F Q S T).card) =
      ∑ U ∈ greedyAvailableIn Q S,
        (deletingSelectors F Q S U ∩ nonPairSelectors S P).card := by
  calc
    (∑ T ∈ nonPairSelectors S P,
        (greedyDeletedIn F Q S T).card) =
        ∑ T ∈ nonPairSelectors S P,
          ∑ U ∈ greedyAvailableIn Q S,
            if U ∈ greedyDeletedIn F Q S T then 1 else 0 := by
      apply sum_congr rfl
      intro T _hT
      let R := greedyDeletedIn F Q S T
      have hR : R ⊆ greedyAvailableIn Q S := sdiff_subset
      calc
        R.card = ∑ U ∈ R,
            (if U ∈ R then (1 : ℕ) else 0) := by simp
        _ = ∑ U ∈ greedyAvailableIn Q S,
            (if U ∈ R then (1 : ℕ) else 0) := by
          apply sum_subset hR
          intro U _hU hUR
          simp [hUR]
    _ = ∑ U ∈ greedyAvailableIn Q S,
          ∑ T ∈ nonPairSelectors S P,
            if U ∈ greedyDeletedIn F Q S T then 1 else 0 := by
      rw [sum_comm]
    _ = ∑ U ∈ greedyAvailableIn Q S,
        (deletingSelectors F Q S U ∩ nonPairSelectors S P).card := by
      apply sum_congr rfl
      intro U hU
      let R := deletingSelectors F Q S U ∩ nonPairSelectors S P
      have hR : R ⊆ nonPairSelectors S P := inter_subset_right
      symm
      calc
        R.card = ∑ T ∈ R, (1 : ℕ) := Finset.card_eq_sum_ones R
        _ = ∑ T ∈ R,
            (if U ∈ greedyDeletedIn F Q S T then (1 : ℕ) else 0) := by
          apply sum_congr rfl
          intro T hT
          have hdel : U ∈ greedyDeletedIn F Q S T :=
            (mem_filter.mp (mem_inter.mp hT).1).2
          simp [hdel]
        _ = ∑ T ∈ nonPairSelectors S P,
            (if U ∈ greedyDeletedIn F Q S T then (1 : ℕ) else 0) := by
          apply sum_subset hR
          intro T hT hTR
          have hnotdel : U ∉ greedyDeletedIn F Q S T := by
            intro hdel
            apply hTR
            exact mem_inter.mpr
              ⟨mem_filter.mpr ⟨(mem_filter.mp hT).1, hdel⟩, hT⟩
          simp [hnotdel]

/-- The aggregate deletion incidence of a surviving pair is at most
`2 * Delta` per current target, plus the genuinely two-away aggregate term.
Pair-killing selectors make no contribution to the survival-masked process. -/
theorem sum_nonPairSelectors_deletions_le_two_mul_add_aggregateCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {Delta Kinc : ℕ}
    (hS : GreedyInvariant F S) (hpair : HasAvailablePairCutoff Delta S)
    (hinc : HasPairStarTwoAwayIncidenceCutoff F Kinc S) :
    (∑ T ∈ nonPairSelectors S P,
        (greedyDeletedIn F
          (availableTrianglesContainingPair S P) S T).card) ≤
      (availableTrianglesContainingPair S P).card * (2 * Delta) + Kinc := by
  let Q := availableTrianglesContainingPair S P
  have hQsub : Q ⊆ S.available := by
    intro U hU
    exact (mem_availableTrianglesContainingPair_iff.mp hU).1
  have hgreedyQ : greedyAvailableIn Q S = Q := inter_eq_right.mpr hQsub
  rw [sum_nonPairSelectors_deletions_eq_sum_targets, hgreedyQ]
  calc
    (∑ U ∈ Q,
        (deletingSelectors F Q S U ∩ nonPairSelectors S P).card) ≤
        ∑ U ∈ Q,
          (2 * Delta +
            (S.available ∩
              nonPairTwoAwayForbiddenTriangles F S.chosen U).card) := by
      apply sum_le_sum
      intro U hU
      have hPU := (mem_availableTrianglesContainingPair_iff.mp hU).2
      have hsub : deletingSelectors F Q S U ∩ nonPairSelectors S P ⊆
          (nonPairSelectors S P ∩ triplesSharingPair U) ∪
            (S.available ∩
              nonPairTwoAwayForbiddenTriangles F S.chosen U) := by
        intro T hT
        have hnon := (mem_inter.mp hT).2
        rcases mem_union.mp
            (deletingSelectors_subset_pairSharing_union_availableNonPairTwoAway
              hS U (mem_inter.mp hT).1) with hshare | htwo
        · exact mem_union.mpr
            (Or.inl (mem_inter.mpr ⟨hnon, (mem_inter.mp hshare).2⟩))
        · exact mem_union.mpr (Or.inr htwo)
      exact (card_le_card hsub).trans <|
        (card_union_le _ _).trans <| Nat.add_le_add_right
          (card_nonPairSelectors_inter_triplesSharingPair_le_two_mul
            hP hPU hpair) _
    _ = Q.card * (2 * Delta) +
        pairStarAvailableTwoAwayIncidences F S P := by
      rw [sum_add_distrib]
      simp [Q, pairStarAvailableTwoAwayIncidences]
    _ ≤ Q.card * (2 * Delta) + Kinc :=
      Nat.add_le_add_left (hinc P hP) _

/-- Survival-masked lower-deviation drift with the sharp factor two. -/
theorem greedyKernel_expectationReal_fixedPairLowerIncrement_if_alive_le_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {D Delta Kpair Kinc d : ℕ}
    (hS : PairTrajectoryInvariant F S₀ S) (hA : S.available.Nonempty)
    (hD : D ≤ S.available.card) (hDgap : Delta < D)
    (hpair : HasAvailablePairCutoff Delta S)
    (hpairTwo : HasPairTwoAwayCutoff F Kpair S)
    (hinc : HasPairStarTwoAwayIncidenceCutoff F Kinc S)
    (hfloor : HasAvailablePairFloor d S) (halive : PairAlive P S)
    (hsmall : 3 + Kpair < d)
    (dq : ℝ) (hdq : -(d : ℝ) ≤ dq) (hdqnonpos : dq ≤ 0)
    (hDrift : dq ≤ -((D - Delta : ℕ) : ℝ)⁻¹ *
      (((Delta : ℝ) * (2 * Delta : ℕ)) + Kinc)) :
    (greedyKernel F S).expectationReal (fun S' ↦
        if PairAlive P S' then
          (dq - (fixedPairAvailableCountReal S₀ P S' -
            fixedPairAvailableCountReal S₀ P S))
        else 0) ≤ 0 := by
  have hcurrentFloor : d ≤
      (availableTrianglesContainingPair S P).card := hfloor P hP halive
  have haliveIff : ∀ T : S.available,
      PairAlive P (greedyStep F S T.1) ↔ ¬ P ⊆ T.1 := by
    intro T
    exact pairAlive_greedyStep_iff_not_subset_of_floor_of_pairCutoff
      hP hS.1 T.2 hpairTwo hcurrentFloor hsmall
  rw [greedyKernel_expectationReal_of_nonempty F S hA]
  let del : TripleOn V → ℕ := fun T ↦
    (greedyDeletedIn F
      (availableTrianglesContainingPair S P) S T).card
  have hpoint : ∀ T : S.available,
      (if PairAlive P (greedyStep F S T.1) then
          dq - (fixedPairAvailableCountReal S₀ P (greedyStep F S T.1) -
            fixedPairAvailableCountReal S₀ P S)
        else 0) ≤ if P ⊆ T.1 then 0 else dq + del T.1 := by
    intro T
    by_cases hPT : P ⊆ T.1
    · have hdead : ¬ PairAlive P (greedyStep F S T.1) := by
        simpa [hPT] using (haliveIff T)
      simp [hdead, hPT]
    · have halive' : PairAlive P (greedyStep F S T.1) := by
        exact (haliveIff T).mpr hPT
      simp only [halive', if_true, hPT, if_false]
      rw [fixedPairAvailableCountReal_step_sub F S₀ S P T.1 hS.2]
      simp [del]
  calc
    (S.available.card : ℝ)⁻¹ *
        ∑ T : S.available,
          (if PairAlive P (greedyStep F S T.1) then
              dq - (fixedPairAvailableCountReal S₀ P
                (greedyStep F S T.1) - fixedPairAvailableCountReal S₀ P S)
            else 0) ≤
      (S.available.card : ℝ)⁻¹ *
        ∑ T : S.available, (if P ⊆ T.1 then 0 else dq + del T.1) := by
      gcongr with T
      exact hpoint T
    _ = (S.available.card : ℝ)⁻¹ *
        ((nonPairSelectors S P).card * dq +
          ∑ T ∈ nonPairSelectors S P, (del T : ℝ)) := by
      rw [show (∑ T : S.available,
          (if P ⊆ T.1 then 0 else dq + del T.1)) =
          ∑ T ∈ nonPairSelectors S P, (dq + del T) by
        calc
          (∑ T : S.available,
              (if P ⊆ T.1 then 0 else dq + del T.1)) =
              ∑ T ∈ S.available,
                (if P ⊆ T.1 then 0 else dq + del T) := by
            rw [univ_eq_attach]
            exact sum_attach S.available
              (fun T ↦ if P ⊆ T.1 then 0 else dq + del T)
          _ = ∑ T ∈ nonPairSelectors S P, (dq + del T) := by
            change (∑ T ∈ S.available,
                if P ⊆ T.1 then 0 else dq + del T) =
              ∑ T ∈ S.available with ¬ P ⊆ T.1, (dq + del T)
            rw [sum_filter]
            congr 1
            funext T
            by_cases hPT : P ⊆ T.1 <;> simp [hPT]]
      simp only [sum_add_distrib, sum_const, nsmul_eq_mul, Nat.cast_sum]
    _ ≤ (S.available.card : ℝ)⁻¹ *
        (((D - Delta : ℕ) : ℝ) * dq +
          (((Delta : ℝ) * (2 * Delta : ℕ)) + Kinc)) := by
      apply mul_le_mul_of_nonneg_left
      · have hpairCard :
            (availableTrianglesContainingPair S P).card ≤ Delta :=
          hpair P hP
        have hnonPairCard :
            D - Delta ≤ (nonPairSelectors S P).card := by
          have hfilter : S.available.filter (fun T ↦ P ⊆ T.1) =
              availableTrianglesContainingPair S P := by
            ext T
            simp [availableTrianglesContainingPair]
          have hsplit := Finset.card_filter_add_card_filter_not
            (s := S.available) (fun T ↦ P ⊆ T.1)
          rw [hfilter] at hsplit
          change (availableTrianglesContainingPair S P).card +
              (nonPairSelectors S P).card = S.available.card at hsplit
          omega
        have hmul : ((nonPairSelectors S P).card : ℝ) * dq ≤
            ((D - Delta : ℕ) : ℝ) * dq := by
          have hcardReal : ((D - Delta : ℕ) : ℝ) ≤
              ((nonPairSelectors S P).card : ℝ) := by
            exact_mod_cast hnonPairCard
          exact mul_le_mul_of_nonpos_right hcardReal hdqnonpos
        have hdel := sum_nonPairSelectors_deletions_le_two_mul_add_aggregateCutoff
          hP hS.1 hpair hinc
        have hdelReal : (∑ T ∈ nonPairSelectors S P, (del T : ℝ)) ≤
            ((Delta : ℝ) * (2 * Delta : ℕ)) + Kinc := by
          have hdelCast : (∑ T ∈ nonPairSelectors S P, (del T : ℝ)) ≤
              (((availableTrianglesContainingPair S P).card : ℝ) *
                (2 * Delta : ℕ)) + Kinc := by
            exact_mod_cast hdel
          calc
            _ ≤ (((availableTrianglesContainingPair S P).card : ℝ) *
                (2 * Delta : ℕ)) + Kinc := hdelCast
            _ ≤ ((Delta : ℝ) * (2 * Delta : ℕ)) + Kinc := by gcongr
        exact add_le_add hmul hdelReal
      · positivity
    _ ≤ 0 := by
      have hgapPos : (0 : ℝ) < (D - Delta : ℕ) := by
        exact_mod_cast Nat.sub_pos_of_lt hDgap
      have hinside : ((D - Delta : ℕ) : ℝ) * dq +
          (((Delta : ℝ) * (2 * Delta : ℕ)) + Kinc) ≤ 0 := by
        have hmul := mul_le_mul_of_nonneg_left hDrift hgapPos.le
        have heq : ((D - Delta : ℕ) : ℝ) *
            (-((D - Delta : ℕ) : ℝ)⁻¹ *
              (((Delta : ℝ) * (2 * Delta : ℕ)) + Kinc)) =
            -(((Delta : ℝ) * (2 * Delta : ℕ)) + Kinc) := by
          field_simp
        rw [heq] at hmul
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hinside

end

end Erdos207
