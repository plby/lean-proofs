/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialGlobalAvailability

/-!
# The global availability upper trajectory

Every selected triple covers three previously uncovered pairs.  Conversely,
an available triple can use only uncovered pairs.  Combining this fact with a
uniform upper bound on the number of available extensions of each pair gives
the time-dependent cubic upper bound on the total number of available
triples.
-/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

/-- The ordinary two-element subsets covered by the chosen triples. -/
def chosenPairFinsets
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) : Finset (Finset V) :=
  S.chosen.biUnion fun T ↦ T.1.powersetCard 2

@[simp]
lemma mem_chosenPairFinsets_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {S : GreedyStateOn V} {P : Finset V} :
    P ∈ chosenPairFinsets S ↔
      ∃ T ∈ S.chosen, P ⊆ T.1 ∧ P.card = 2 := by
  simp [chosenPairFinsets, mem_powersetCard]

/-- A packing covers exactly three distinct ordinary pairs per triple. -/
lemma card_chosenPairFinsets_of_isPackingOn
    {V : Type*} [Fintype V] [DecidableEq V]
    {S : GreedyStateOn V} (hpacking : IsPackingOn S.chosen) :
    (chosenPairFinsets S).card = 3 * S.chosen.card := by
  rw [chosenPairFinsets, card_biUnion]
  · calc
      (∑ T ∈ S.chosen, (T.1.powersetCard 2).card) =
          ∑ _T ∈ S.chosen, 3 := by
        apply sum_congr rfl
        intro T _hT
        rw [card_powersetCard, T.2]
        norm_num
      _ = 3 * S.chosen.card := by simp [Nat.mul_comm]
  · intro T hT U hU hTU
    change Disjoint (T.1.powersetCard 2) (U.1.powersetCard 2)
    rw [disjoint_left]
    intro P hPT hPU
    have hPTdata := mem_powersetCard.mp hPT
    have hPUdata := mem_powersetCard.mp hPU
    have hsub : P ⊆ T.1 ∩ U.1 := fun x hx ↦
      mem_inter.mpr ⟨hPTdata.1 hx, hPUdata.1 hx⟩
    have hcard := card_le_card hsub
    have hinter := hpacking.inter_card_le_one hT hU hTU
    omega

lemma chosenPairFinsets_subset_allPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) :
    chosenPairFinsets S ⊆ (univ : Finset V).powersetCard 2 := by
  intro P hP
  obtain ⟨T, _hT, hPT, hPcard⟩ := mem_chosenPairFinsets_iff.mp hP
  exact mem_powersetCard.mpr ⟨subset_univ P, hPcard⟩

/-- An available triple cannot contain a pair already covered by the chosen
packing. -/
lemma availableTrianglesContainingPair_eq_empty_of_mem_chosenPairFinsets
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (hInv : GreedyInvariant F S) {P : Finset V}
    (hP : P ∈ chosenPairFinsets S) :
    availableTrianglesContainingPair S P = ∅ := by
  ext T
  constructor
  · intro hT
    have hTdata := mem_availableTrianglesContainingPair_iff.mp hT
    obtain ⟨U, hU, hPU, hPcard⟩ := mem_chosenPairFinsets_iff.mp hP
    have hlegal := hInv.2.2 T hTdata.1
    have hTU : T ≠ U := fun h ↦ hlegal.1 (h ▸ hU)
    have hsub : P ⊆ T.1 ∩ U.1 := fun x hx ↦
      mem_inter.mpr ⟨hTdata.2 hx, hPU hx⟩
    have hcard := card_le_card hsub
    have hinter := hlegal.2.1.inter_card_le_one
      (mem_insert_self T S.chosen) (mem_insert_of_mem hU) hTU
    omega
  · simp

/-- Summing pair stars over the ambient two-element subsets counts every
available triple three times. -/
lemma sum_allPairs_card_availableTrianglesContainingPair
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) :
    ∑ P ∈ (univ : Finset V).powersetCard 2,
        (availableTrianglesContainingPair S P).card =
      3 * S.available.card := by
  let e : PairOn V ↪ Finset V := Function.Embedding.subtype _
  have hmap : (univ : Finset (PairOn V)).map e =
      (univ : Finset V).powersetCard 2 := by
    ext P
    simp only [mem_map, mem_univ, true_and, mem_powersetCard]
    constructor
    · rintro ⟨Q, hQP⟩
      subst P
      exact ⟨subset_univ Q.1, Q.2⟩
    · rintro ⟨_hPsub, hPcard⟩
      exact ⟨⟨P, hPcard⟩, rfl⟩
  rw [← hmap, sum_map]
  change (∑ P : PairOn V,
      (availableTrianglesContainingPair S P.1).card) =
    3 * S.available.card
  exact sum_card_availableTrianglesContainingPair S

/-- A pair cutoff and the number of pairs not yet covered control the total
availability. -/
theorem three_mul_available_card_le_uncoveredPairs_mul_pairCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {Delta : ℕ}
    (hInv : GreedyInvariant F S)
    (hpair : HasAvailablePairCutoff Delta S) :
    3 * S.available.card ≤
      (((univ : Finset V).powersetCard 2 \ chosenPairFinsets S).card) *
        Delta := by
  rw [← sum_allPairs_card_availableTrianglesContainingPair S]
  calc
    (∑ P ∈ (univ : Finset V).powersetCard 2,
        (availableTrianglesContainingPair S P).card) ≤
        ∑ P ∈ (univ : Finset V).powersetCard 2,
          if P ∈ chosenPairFinsets S then 0 else Delta := by
      apply sum_le_sum
      intro P hP
      by_cases hPchosen : P ∈ chosenPairFinsets S
      · simp only [hPchosen, if_true]
        rw [availableTrianglesContainingPair_eq_empty_of_mem_chosenPairFinsets
          hInv hPchosen, card_empty]
      · simp only [hPchosen, if_false]
        exact hpair P (mem_powersetCard.mp hP).2
    _ = ∑ P ∈ ((univ : Finset V).powersetCard 2).filter
          (fun P ↦ P ∉ chosenPairFinsets S), Delta := by
      rw [sum_filter]
      apply sum_congr rfl
      intro P _hP
      by_cases hPchosen : P ∈ chosenPairFinsets S <;> simp [hPchosen]
    _ = (((univ : Finset V).powersetCard 2 \ chosenPairFinsets S).card) *
        Delta := by
      simp [sdiff_eq_filter, Nat.mul_comm]

/-- Explicit form of the global availability upper trajectory. -/
theorem three_mul_available_card_le_choose_sub_chosen_mul_pairCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {Delta : ℕ}
    (hInv : GreedyInvariant F S)
    (hpair : HasAvailablePairCutoff Delta S) :
    3 * S.available.card ≤
      (Nat.choose (Fintype.card V) 2 - 3 * S.chosen.card) * Delta := by
  simpa [card_sdiff_of_subset (chosenPairFinsets_subset_allPairs S),
    card_powersetCard, card_univ,
    card_chosenPairFinsets_of_isPackingOn hInv.1] using
      three_mul_available_card_le_uncoveredPairs_mul_pairCutoff hInv hpair

/-- The exact integral consequence of the preceding triple-counting bound.
Keeping the division by three is essential for a sharp upper-availability
schedule: every available triangle is counted once through each of its three
pairs. -/
theorem available_card_le_choose_sub_chosen_mul_pairCutoff_div_three
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {Delta : ℕ}
    (hInv : GreedyInvariant F S)
    (hpair : HasAvailablePairCutoff Delta S) :
    S.available.card ≤
      ((Nat.choose (Fintype.card V) 2 - 3 * S.chosen.card) * Delta) / 3 := by
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).2
  simpa only [Nat.mul_comm] using
    three_mul_available_card_le_choose_sub_chosen_mul_pairCutoff hInv hpair

/-- On a synchronized trajectory starting with no chosen triples, the upper
pair-deviation window yields an explicit time-indexed total-availability
schedule.  The harmless missing factor `3` keeps the bound integral. -/
theorem available_card_le_choose_sub_time_mul_pairCutoff_of_deviations
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    (qUpper : PairOn V → ℕ → ℝ) (i Delta : ℕ) (a : ℝ)
    (htraj : PairTrajectoryInvariant F S₀ S)
    (hchosen₀ : S₀.chosen = ∅)
    (hcard : S.chosen.card = S₀.chosen.card + i)
    (hcap : ∀ P : PairOn V,
      qUpper P i +
          (fixedPairAvailableCountReal S₀ P.1 S₀ - qUpper P 0) + a ≤
        ((Delta + 1 : ℕ) : ℝ))
    (hdev : ∀ P : PairOn V, PairAlive P.1 S →
      fixedPairUpperDeviation (qUpper P) S₀ P.1 i S -
        fixedPairUpperDeviation (qUpper P) S₀ P.1 0 S₀ < a) :
    S.available.card ≤
      (Nat.choose (Fintype.card V) 2 - 3 * i) * Delta := by
  have hpair : HasAvailablePairCutoff Delta S :=
    hasAvailablePairCutoff_of_upperDeviations_lt qUpper i Delta a
      htraj.2 hcap hdev
  have hthree :=
    three_mul_available_card_le_choose_sub_chosen_mul_pairCutoff
      htraj.1 hpair
  rw [hcard, hchosen₀] at hthree
  simp only [card_empty, zero_add] at hthree
  omega

end

end Erdos207
