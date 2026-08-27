/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyDeletionObstruction
import ErdosProblems.Erdos207.AvailableThreePairUnion

/-!
# Forced drift of an available pair-extension family

If the next selected triangle contains a fixed pair `P`, every other
available extension of `P` is destroyed immediately.  Hence a pair-extension
family of size `d` contributes at least `d²` ordered deletion incidences.
This is the first self-correcting term in the KSSS edge-extension trajectory.
-/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

/-- Every member of a fixed available pair star is deleted when another
member of that star is selected. -/
lemma mem_greedyDeletedIn_pairStar_of_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {T U : TripleOn V}
    (hS : GreedyInvariant F S)
    (hT : T ∈ availableTrianglesContainingPair S P)
    (hU : U ∈ availableTrianglesContainingPair S P) :
    U ∈ greedyDeletedIn F (availableTrianglesContainingPair S P) S T := by
  have hTavailable := (mem_availableTrianglesContainingPair_iff.mp hT).1
  have hUavailable := (mem_availableTrianglesContainingPair_iff.mp hU).1
  have hshare : U ∈ triplesSharingPair T := by
    rw [mem_triplesSharingPair_iff]
    have hPT := (mem_availableTrianglesContainingPair_iff.mp hT).2
    have hPU := (mem_availableTrianglesContainingPair_iff.mp hU).2
    calc
      2 = P.card := hP.symm
      _ ≤ (T.1 ∩ U.1).card := card_le_card fun x hx ↦
        mem_inter.mpr ⟨hPT hx, hPU hx⟩
  have hdeletedUniv := mem_greedyDeletedIn_univ_of_pairSharing
    hS hTavailable hUavailable hshare
  apply mem_sdiff.mpr
  constructor
  · exact mem_inter.mpr ⟨hUavailable, hU⟩
  · intro hnext
    apply (mem_sdiff.mp hdeletedUniv).2
    exact mem_inter.mpr ⟨(mem_inter.mp hnext).1, mem_univ U⟩

/-- Selecting a member of a pair star deletes the whole current pair star. -/
theorem pairStar_card_le_greedyDeletedIn
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {T : TripleOn V}
    (hS : GreedyInvariant F S)
    (hT : T ∈ availableTrianglesContainingPair S P) :
    (availableTrianglesContainingPair S P).card ≤
      (greedyDeletedIn F (availableTrianglesContainingPair S P) S T).card :=
  card_le_card fun _U hU ↦
    mem_greedyDeletedIn_pairStar_of_mem hP hS hT hU

/-- Ordered deletion-incidence lower bound `d²` for a pair star of size `d`. -/
theorem sq_pairStar_card_le_sum_greedyDeletedIn
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2)
    (hS : GreedyInvariant F S) :
    (availableTrianglesContainingPair S P).card ^ 2 ≤
      ∑ T : S.available,
        (greedyDeletedIn F (availableTrianglesContainingPair S P) S T.1).card := by
  let Q := availableTrianglesContainingPair S P
  have hQsub : Q ⊆ S.available := by
    intro T hT
    exact (mem_availableTrianglesContainingPair_iff.mp hT).1
  calc
    Q.card ^ 2 = ∑ _T ∈ Q, Q.card := by
      simp [pow_two]
    _ ≤ ∑ T ∈ Q, (greedyDeletedIn F Q S T).card := by
      apply sum_le_sum
      intro T hT
      exact pairStar_card_le_greedyDeletedIn hP hS hT
    _ ≤ ∑ T ∈ S.available, (greedyDeletedIn F Q S T).card := by
      exact sum_le_sum_of_subset_of_nonneg hQsub
        fun _T _hT _ ↦ Nat.zero_le _
    _ = ∑ T : S.available,
        (greedyDeletedIn F Q S T.1).card := by
      rw [Finset.univ_eq_attach]
      exact (Finset.sum_attach S.available
        (fun T ↦ (greedyDeletedIn F Q S T).card)).symm

/-- Conditional expected decline forced solely by selection inside the fixed
pair star. -/
theorem greedyKernel_expectationReal_pairStar_increment_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2)
    (hS : GreedyInvariant F S) (hA : S.available.Nonempty) :
    (greedyKernel F S).expectationReal
        (fun S' ↦ greedyAvailableCountReal
            (availableTrianglesContainingPair S P) S' -
          greedyAvailableCountReal
            (availableTrianglesContainingPair S P) S) ≤
      -(S.available.card : ℝ)⁻¹ *
        ((availableTrianglesContainingPair S P).card : ℝ) ^ 2 := by
  rw [greedyKernel_expectationReal_availableCount_increment
    F (availableTrianglesContainingPair S P) S hA]
  apply mul_le_mul_of_nonpos_left
  · exact_mod_cast sq_pairStar_card_le_sum_greedyDeletedIn hP hS
  · exact neg_nonpos.mpr (by positivity)

/-- Targets in `Q` sharing a pair with a proposed selected triangle. -/
def pairSharingTargets
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : TripleSystemOn V) (T : TripleOn V) : TripleSystemOn V :=
  Q.filter fun U ↦ T ∈ triplesSharingPair U

/-- Transpose the ordered pair-sharing incidence relation. -/
theorem sum_card_available_pairSharing_eq_sum_card_pairSharingTargets
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (Q : TripleSystemOn V) :
    ∑ U ∈ Q, (S.available ∩ triplesSharingPair U).card =
      ∑ T ∈ S.available, (pairSharingTargets Q T).card := by
  simp only [card_eq_sum_ones, pairSharingTargets, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro U _hU
  rw [← sum_filter]
  congr 1

/-- Every pair-sharing target in a fixed pair star is actually deleted. -/
theorem pairSharingTargets_subset_greedyDeletedIn_pairStar
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} {T : TripleOn V}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available) :
    pairSharingTargets (availableTrianglesContainingPair S P) T ⊆
      greedyDeletedIn F (availableTrianglesContainingPair S P) S T := by
  intro U hU
  have hUdata := mem_filter.mp hU
  have hUavailable :=
    (mem_availableTrianglesContainingPair_iff.mp hUdata.1).1
  have hshare : U ∈ triplesSharingPair T := by
    rw [mem_triplesSharingPair_iff] at hUdata ⊢
    simpa [inter_comm] using hUdata.2
  have hdeletedUniv := mem_greedyDeletedIn_univ_of_pairSharing
    hS hT hUavailable hshare
  apply mem_sdiff.mpr
  constructor
  · exact mem_inter.mpr ⟨hUavailable, hUdata.1⟩
  · intro hnext
    apply (mem_sdiff.mp hdeletedUniv).2
    exact mem_inter.mpr ⟨(mem_inter.mp hnext).1, mem_univ U⟩

/-- Under a nonempty pair floor `δ`, the full ordered deletion incidence has
the three-pair lower bound, with the exact overlap correction `2d`. -/
theorem pairStar_card_mul_three_pairFloor_le_sum_deletions_add
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} {δ : ℕ}
    (hS : GreedyInvariant F S) (hfloor : HasAvailablePairFloor δ S) :
    (availableTrianglesContainingPair S P).card * (3 * δ) ≤
      (∑ T : S.available,
        (greedyDeletedIn F (availableTrianglesContainingPair S P) S T.1).card) +
      2 * (availableTrianglesContainingPair S P).card := by
  let Q := availableTrianglesContainingPair S P
  have htargets : ∑ T ∈ S.available, (pairSharingTargets Q T).card ≤
      ∑ T ∈ S.available, (greedyDeletedIn F Q S T).card := by
    apply sum_le_sum
    intro T hT
    exact card_le_card
      (pairSharingTargets_subset_greedyDeletedIn_pairStar hS hT)
  have htranspose :=
    sum_card_available_pairSharing_eq_sum_card_pairSharingTargets S Q
  have hlocal : ∑ U ∈ Q, 3 * δ ≤
      ∑ U ∈ Q, ((S.available ∩ triplesSharingPair U).card + 2) := by
    apply sum_le_sum
    intro U hU
    exact three_mul_pairFloor_le_pairSharing_card_add_two hfloor
      (mem_availableTrianglesContainingPair_iff.mp hU).1
  have hsubtype :
      (∑ T ∈ S.available, (greedyDeletedIn F Q S T).card) =
        ∑ T : S.available, (greedyDeletedIn F Q S T.1).card := by
    rw [Finset.univ_eq_attach]
    exact (Finset.sum_attach S.available
      (fun T ↦ (greedyDeletedIn F Q S T).card)).symm
  rw [sum_const, nsmul_eq_mul, sum_add_distrib] at hlocal
  simp only [sum_const, nsmul_eq_mul] at hlocal
  rw [htranspose] at hlocal
  rw [hsubtype] at htargets
  dsimp [Q] at hlocal htargets ⊢
  omega

/-- Subtractive form of the three-pair incidence bound. -/
theorem pairStar_card_mul_three_pairFloor_sub_two_le_sum_deletions
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} {δ : ℕ}
    (hS : GreedyInvariant F S) (hfloor : HasAvailablePairFloor δ S)
    (hδ : 1 ≤ δ) :
    (availableTrianglesContainingPair S P).card * (3 * δ - 2) ≤
      ∑ T : S.available,
        (greedyDeletedIn F (availableTrianglesContainingPair S P) S T.1).card := by
  let d := (availableTrianglesContainingPair S P).card
  let Z := ∑ T : S.available,
    (greedyDeletedIn F (availableTrianglesContainingPair S P) S T.1).card
  have hmain := pairStar_card_mul_three_pairFloor_le_sum_deletions_add
    hS hfloor (P := P)
  change d * (3 * δ - 2) ≤ Z
  change d * (3 * δ) ≤ Z + 2 * d at hmain
  have hsplit : d * (3 * δ - 2) + 2 * d = d * (3 * δ) := by
    calc
      d * (3 * δ - 2) + 2 * d =
          d * (3 * δ - 2) + d * 2 := by omega
      _ = d * ((3 * δ - 2) + 2) := (Nat.mul_add _ _ _).symm
      _ = d * (3 * δ) := by
        congr 1
        omega
  omega

/-- Conditional edge-extension drift with the full three-pair factor. -/
theorem greedyKernel_expectationReal_pairStar_increment_le_threeFloor
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} {δ : ℕ}
    (hS : GreedyInvariant F S) (hA : S.available.Nonempty)
    (hfloor : HasAvailablePairFloor δ S) (hδ : 1 ≤ δ) :
    (greedyKernel F S).expectationReal
        (fun S' ↦ greedyAvailableCountReal
            (availableTrianglesContainingPair S P) S' -
          greedyAvailableCountReal
            (availableTrianglesContainingPair S P) S) ≤
      -(S.available.card : ℝ)⁻¹ *
        (((availableTrianglesContainingPair S P).card : ℝ) *
          (3 * δ - 2 : ℕ)) := by
  rw [greedyKernel_expectationReal_availableCount_increment
    F (availableTrianglesContainingPair S P) S hA]
  apply mul_le_mul_of_nonpos_left
  · exact_mod_cast
      pairStar_card_mul_three_pairFloor_sub_two_le_sum_deletions
        hS hfloor hδ (P := P)
  · exact neg_nonpos.mpr (by positivity)

/-- Available selectors whose greedy step deletes a prescribed target. -/
def deletingSelectors
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : TripleSystemOn V)
    (S : GreedyStateOn V) (U : TripleOn V) : TripleSystemOn V :=
  S.available.filter fun T ↦ U ∈ greedyDeletedIn F Q S T

/-- Transpose the exact deletion incidence relation. -/
theorem sum_card_greedyDeletedIn_eq_sum_card_deletingSelectors
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : TripleSystemOn V)
    (S : GreedyStateOn V) :
    ∑ T ∈ S.available, (greedyDeletedIn F Q S T).card =
      ∑ U ∈ greedyAvailableIn Q S, (deletingSelectors F Q S U).card := by
  simp only [card_eq_sum_ones, deletingSelectors, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro T _hT
  rw [← sum_filter]
  congr 1
  ext U
  simp [greedyDeletedIn]

/-- A deleting selector is either pair-sharing with the target or is a
two-away forbidden completion rooted at the target. -/
theorem deletingSelectors_subset_pairSharing_union_twoAway
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {Q : TripleSystemOn V}
    {S : GreedyStateOn V} (hS : GreedyInvariant F S) (U : TripleOn V) :
    deletingSelectors F Q S U ⊆
      (S.available ∩ triplesSharingPair U) ∪
        twoAwayForbiddenTriangles F S.chosen U := by
  intro T hT
  have hTdata := mem_filter.mp hT
  have hclassification := greedyDeletedIn_subset_pairSharing_union_twoAway
    (Q := Q) hS hTdata.1 hTdata.2
  rcases mem_union.mp hclassification with hshare | htwo
  · apply mem_union.mpr
    left
    apply mem_inter.mpr
    refine ⟨hTdata.1, ?_⟩
    rw [mem_triplesSharingPair_iff] at hshare ⊢
    simpa [inter_comm] using hshare
  · exact mem_union.mpr (Or.inr
      (mem_twoAwayForbiddenTriangles_comm.mp htwo))

/-- Pair and two-away cutoffs bound the number of selectors capable of
deleting one available target. -/
theorem card_deletingSelectors_le_pair_add_twoAway
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {Q : TripleSystemOn V}
    {S : GreedyStateOn V} {Δ K : ℕ}
    (hS : GreedyInvariant F S) (hpair : HasAvailablePairCutoff Δ S)
    (htwo : HasTwoAwayCutoff F K S) {U : TripleOn V}
    (hU : U ∈ S.available) :
    (deletingSelectors F Q S U).card ≤ 3 * Δ + K := by
  calc
    (deletingSelectors F Q S U).card ≤
        (S.available ∩ triplesSharingPair U).card +
          (twoAwayForbiddenTriangles F S.chosen U).card :=
      (card_le_card
        (deletingSelectors_subset_pairSharing_union_twoAway hS U)).trans
        (card_union_le _ _)
    _ ≤ 3 * Δ + K := Nat.add_le_add
      (card_available_inter_triplesSharingPair_le hpair U) (htwo U hU)

/-- The full ordered deletion incidence is at most `d(3Δ+K)` for a fixed
pair star of size `d`. -/
theorem sum_deletions_le_pairStar_card_mul_pairCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} {Δ K : ℕ}
    (hS : GreedyInvariant F S) (hpair : HasAvailablePairCutoff Δ S)
    (htwo : HasTwoAwayCutoff F K S) :
    (∑ T : S.available,
        (greedyDeletedIn F (availableTrianglesContainingPair S P) S T.1).card) ≤
      (availableTrianglesContainingPair S P).card * (3 * Δ + K) := by
  let Q := availableTrianglesContainingPair S P
  have hQsub : Q ⊆ S.available := by
    intro U hU
    exact (mem_availableTrianglesContainingPair_iff.mp hU).1
  have hgreedyQ : greedyAvailableIn Q S = Q := inter_eq_right.mpr hQsub
  have htranspose := sum_card_greedyDeletedIn_eq_sum_card_deletingSelectors
    F Q S
  rw [hgreedyQ] at htranspose
  have hbound : ∑ U ∈ Q, (deletingSelectors F Q S U).card ≤
      ∑ _U ∈ Q, (3 * Δ + K) := by
    apply sum_le_sum
    intro U hU
    exact card_deletingSelectors_le_pair_add_twoAway hS hpair htwo
      (mem_availableTrianglesContainingPair_iff.mp hU).1
  have hsubtype :
      (∑ T ∈ S.available, (greedyDeletedIn F Q S T).card) =
        ∑ T : S.available, (greedyDeletedIn F Q S T.1).card := by
    rw [Finset.univ_eq_attach]
    exact (Finset.sum_attach S.available
      (fun T ↦ (greedyDeletedIn F Q S T).card)).symm
  rw [← htranspose, hsubtype] at hbound
  simpa [Q] using hbound

/-- Conditional edge-extension decline is not faster than the cutoff
envelope `d(3Δ+K)/|A|`. -/
theorem greedyKernel_expectationReal_pairStar_increment_ge_cutoffs
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} {Δ K : ℕ}
    (hS : GreedyInvariant F S) (hA : S.available.Nonempty)
    (hpair : HasAvailablePairCutoff Δ S)
    (htwo : HasTwoAwayCutoff F K S) :
    -(S.available.card : ℝ)⁻¹ *
        (((availableTrianglesContainingPair S P).card : ℝ) *
          (3 * Δ + K : ℕ)) ≤
      (greedyKernel F S).expectationReal
        (fun S' ↦ greedyAvailableCountReal
            (availableTrianglesContainingPair S P) S' -
          greedyAvailableCountReal
            (availableTrianglesContainingPair S P) S) := by
  rw [greedyKernel_expectationReal_availableCount_increment
    F (availableTrianglesContainingPair S P) S hA]
  apply mul_le_mul_of_nonpos_left
  · exact_mod_cast sum_deletions_le_pairStar_card_mul_pairCutoff
      hS hpair htwo (P := P)
  · exact neg_nonpos.mpr (by positivity)

/-- Restricting the test family can only reduce the deletion set. -/
theorem greedyDeletedIn_subset_greedyDeletedIn_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : TripleSystemOn V)
    (S : GreedyStateOn V) (T : TripleOn V) :
    greedyDeletedIn F Q S T ⊆
      greedyDeletedIn F (univ : TripleSystemOn V) S T := by
  intro U hU
  have hold := mem_inter.mp (mem_sdiff.mp hU).1
  apply mem_sdiff.mpr
  constructor
  · simpa [greedyAvailableIn] using hold.1
  · intro hnext
    apply (mem_sdiff.mp hU).2
    exact mem_inter.mpr
      ⟨by simpa [greedyAvailableIn] using hnext, hold.2⟩

/-- Under the two cutoffs, every restricted one-step deletion count is at
most `3Δ+K`. -/
theorem card_greedyDeletedIn_le_pairCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {Q : TripleSystemOn V}
    {S : GreedyStateOn V} {T : TripleOn V} {Δ K : ℕ}
    (hS : GreedyInvariant F S) (hpair : HasAvailablePairCutoff Δ S)
    (htwo : HasTwoAwayCutoff F K S) (hT : T ∈ S.available) :
    (greedyDeletedIn F Q S T).card ≤ 3 * Δ + K :=
  (card_le_card (greedyDeletedIn_subset_greedyDeletedIn_univ F Q S T)).trans
    (card_greedyDeleted_available_le_pairCutoff hS hpair htwo hT)

/-- Conditional second moment of a pair-star decrement under the pair and
two-away cutoffs. -/
theorem greedyKernel_expectationReal_pairStar_sqIncrement_le_cutoffs
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} {Δ K : ℕ}
    (hS : GreedyInvariant F S) (hA : S.available.Nonempty)
    (hpair : HasAvailablePairCutoff Δ S)
    (htwo : HasTwoAwayCutoff F K S) :
    (greedyKernel F S).expectationReal
        (fun S' ↦ (greedyAvailableCountReal
            (availableTrianglesContainingPair S P) S' -
          greedyAvailableCountReal
            (availableTrianglesContainingPair S P) S) ^ 2) ≤
      (S.available.card : ℝ)⁻¹ *
        (((availableTrianglesContainingPair S P).card : ℝ) *
          (3 * Δ + K : ℕ) ^ 2) := by
  rw [greedyKernel_expectationReal_availableCount_sqIncrement
    F (availableTrianglesContainingPair S P) S hA]
  apply mul_le_mul_of_nonneg_left
  · have hsq : ∑ T : S.available,
        (greedyDeletedIn F (availableTrianglesContainingPair S P) S T.1).card ^ 2 ≤
      (3 * Δ + K) * ∑ T : S.available,
          (greedyDeletedIn F (availableTrianglesContainingPair S P) S T.1).card := by
      rw [Finset.mul_sum]
      apply sum_le_sum
      intro T _hT
      have hd := card_greedyDeletedIn_le_pairCutoff
        hS hpair htwo T.2
        (Q := availableTrianglesContainingPair S P)
      nlinarith
    have hsum := sum_deletions_le_pairStar_card_mul_pairCutoff
      hS hpair htwo (P := P)
    have hnat : ∑ T : S.available,
        (greedyDeletedIn F (availableTrianglesContainingPair S P) S T.1).card ^ 2 ≤
        (availableTrianglesContainingPair S P).card * (3 * Δ + K) ^ 2 := by
      calc
        _ ≤ (3 * Δ + K) * ∑ T : S.available,
            (greedyDeletedIn F
              (availableTrianglesContainingPair S P) S T.1).card := hsq
        _ ≤ (3 * Δ + K) *
            ((availableTrianglesContainingPair S P).card *
              (3 * Δ + K)) := Nat.mul_le_mul_left _ hsum
        _ = _ := by ring
    exact_mod_cast hnat
  · positivity

end

end Erdos207
