/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AlivePairJump

/-!
# Conditional variance while a tracked pair survives

Selecting a triangle containing the tracked pair deletes its entire current
pair star, but also kills the pair.  After restricting to successors on which
the pair remains alive, `AlivePairJump` bounds the deletion count by `3 + K`.
Combining that pointwise bound with the transposed deletion-incidence bound
gives a second moment linear, rather than quadratic, in the global deletion
envelope.
-/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

/-- Available selectors which do not themselves cover the tracked pair. -/
def nonPairSelectors
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (P : Finset V) : TripleSystemOn V :=
  S.available.filter fun T ↦ ¬ P ⊆ T.1

/-- The selectors which cover `P` contribute at most `d²` deletion
incidences to its current star of size `d`. -/
theorem sum_pairSelectors_deletions_le_sq_pairStar_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (P : Finset V) :
    (∑ T ∈ S.available.filter (fun T ↦ P ⊆ T.1),
        (greedyDeletedIn F
          (availableTrianglesContainingPair S P) S T).card) ≤
      (availableTrianglesContainingPair S P).card ^ 2 := by
  let Q := availableTrianglesContainingPair S P
  have hfilter : S.available.filter (fun T ↦ P ⊆ T.1) = Q := by
    ext T
    simp [Q, availableTrianglesContainingPair]
  rw [hfilter]
  calc
    ∑ T ∈ Q, (greedyDeletedIn F Q S T).card ≤
        ∑ _T ∈ Q, Q.card := by
          apply sum_le_sum
          intro T _hT
          apply card_le_card
          intro U hU
          exact (mem_inter.mp (mem_sdiff.mp hU).1).2
    _ = Q.card ^ 2 := by simp [pow_two]

/-- Removing the at-most-`d²` incidences caused by selectors in the pair
star leaves a uniform lower bound on deletion incidences over non-pair
selectors. -/
theorem pairStar_card_mul_threeFloor_sub_two_sub_cutoff_le_sum_nonPair
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {δ Δ : ℕ}
    (hS : GreedyInvariant F S) (hfloor : HasAvailablePairFloor δ S)
    (hδ : 1 ≤ δ) (hpair : HasAvailablePairCutoff Δ S) :
    (availableTrianglesContainingPair S P).card * (3 * δ - 2 - Δ) ≤
      ∑ T ∈ nonPairSelectors S P,
        (greedyDeletedIn F
          (availableTrianglesContainingPair S P) S T).card := by
  let d := (availableTrianglesContainingPair S P).card
  let z : TripleOn V → ℕ := fun T ↦
    (greedyDeletedIn F
      (availableTrianglesContainingPair S P) S T).card
  have hfull :=
    pairStar_card_mul_three_pairFloor_sub_two_le_sum_deletions
      hS hfloor hδ (P := P)
  have hpairPart := sum_pairSelectors_deletions_le_sq_pairStar_card F S P
  have hsplit :
      (∑ T : S.available, z T.1) =
        (∑ T ∈ S.available.filter (fun T ↦ P ⊆ T.1), z T) +
          ∑ T ∈ nonPairSelectors S P, z T := by
    have hraw := Finset.sum_filter_add_sum_filter_not
      S.available (fun T ↦ P ⊆ T.1) z
    have hattach : (∑ T : S.available, z T.1) =
        ∑ T ∈ S.available, z T := by
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach S.available z
    rw [hattach]
    simpa only [nonPairSelectors] using hraw.symm
  have hdΔ : d ≤ Δ := hpair P hP
  change d * (3 * δ - 2) ≤ ∑ T : S.available, z T.1 at hfull
  change (∑ T ∈ S.available.filter (fun T ↦ P ⊆ T.1), z T) ≤
    d ^ 2 at hpairPart
  rw [hsplit] at hfull
  change d * (3 * δ - 2 - Δ) ≤
    ∑ T ∈ nonPairSelectors S P, z T
  by_cases hgap : Δ ≤ 3 * δ - 2
  · have hmul :
        d * (3 * δ - 2 - Δ) + d * Δ = d * (3 * δ - 2) := by
      have : (3 * δ - 2 - Δ) + Δ = 3 * δ - 2 := by omega
      calc
        d * (3 * δ - 2 - Δ) + d * Δ =
            d * ((3 * δ - 2 - Δ) + Δ) := (Nat.mul_add _ _ _).symm
        _ = _ := by rw [this]
    nlinarith [Nat.mul_le_mul_left d hdΔ]
  · have hz : 3 * δ - 2 - Δ = 0 := by omega
    simp [hz]

/-- Pair-local form of the survival-masked pointwise square bound. -/
theorem fixedPair_sqIncrement_if_alive_step_le_of_pairCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {T : TripleOn V} {K : ℕ}
    (hS : PairTrajectoryInvariant F S₀ S) (hT : T ∈ S.available)
    (htwo : HasPairTwoAwayCutoff F K S) :
    (if PairAlive P (greedyStep F S T) then
        (fixedPairAvailableCountReal S₀ P (greedyStep F S T) -
          fixedPairAvailableCountReal S₀ P S) ^ 2
      else 0) ≤
      ((3 + K : ℕ) : ℝ) *
        (greedyDeletedIn F (availableTrianglesContainingPair S P) S T).card := by
  by_cases halive : PairAlive P (greedyStep F S T)
  · simp only [halive, if_true]
    rw [fixedPairAvailableCountReal_step_sub F S₀ S P T hS.2, neg_sq]
    have hcard :=
      card_greedyDeletedIn_pairStar_le_three_add_twoAway_of_step_alive_of_pairCutoff
        hP hS.1 hT htwo halive
    have hcardReal :
        ((greedyDeletedIn F (availableTrianglesContainingPair S P) S T).card : ℝ) ≤
          ((3 + K : ℕ) : ℝ) := by
      exact_mod_cast hcard
    have hcardNonneg : (0 : ℝ) ≤
        (greedyDeletedIn F
          (availableTrianglesContainingPair S P) S T).card := by
      positivity
    nlinarith
  · simp only [halive, if_false]
    positivity

/-- On a surviving successor, the square of the fixed-pair decrement is at
most `3 + K` times its deletion count; on a dead successor the masked square
vanishes. -/
theorem fixedPair_sqIncrement_if_alive_step_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {T : TripleOn V} {K : ℕ}
    (hS : PairTrajectoryInvariant F S₀ S) (hT : T ∈ S.available)
    (htwo : HasTwoAwayCutoff F K S) :
    (if PairAlive P (greedyStep F S T) then
        (fixedPairAvailableCountReal S₀ P (greedyStep F S T) -
          fixedPairAvailableCountReal S₀ P S) ^ 2
      else 0) ≤
      ((3 + K : ℕ) : ℝ) *
        (greedyDeletedIn F (availableTrianglesContainingPair S P) S T).card := by
  exact fixedPair_sqIncrement_if_alive_step_le_of_pairCutoff
    hP hS hT htwo.hasPairTwoAwayCutoff

/-- With separate local and global two-away cutoffs, the survival-masked
second moment is `d (3+Kpair)(3Δ+Kglobal) / |A|`. -/
theorem greedyKernel_expectationReal_fixedPair_sqIncrement_if_alive_le_of_pairCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {Δ Kpair Kglobal : ℕ}
    (hS : PairTrajectoryInvariant F S₀ S) (hA : S.available.Nonempty)
    (hpair : HasAvailablePairCutoff Δ S)
    (hpairTwo : HasPairTwoAwayCutoff F Kpair S)
    (htwo : HasTwoAwayCutoff F Kglobal S) :
    (greedyKernel F S).expectationReal (fun S' ↦
        if PairAlive P S' then
          (fixedPairAvailableCountReal S₀ P S' -
            fixedPairAvailableCountReal S₀ P S) ^ 2
        else 0) ≤
      (S.available.card : ℝ)⁻¹ *
        (((availableTrianglesContainingPair S P).card : ℝ) *
          (((3 + Kpair : ℕ) : ℝ) * ((3 * Δ + Kglobal : ℕ) : ℝ))) := by
  rw [greedyKernel_expectationReal_of_nonempty F S hA]
  apply mul_le_mul_of_nonneg_left
  · calc
      ∑ T : S.available,
          (if PairAlive P (greedyStep F S T.1) then
              (fixedPairAvailableCountReal S₀ P (greedyStep F S T.1) -
                fixedPairAvailableCountReal S₀ P S) ^ 2
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
            ((3 * Δ + Kglobal : ℕ) : ℝ)) := by
          apply mul_le_mul_of_nonneg_left
          · exact_mod_cast sum_deletions_le_pairStar_card_mul_pairCutoff
              hS.1 hpair htwo (P := P)
          · positivity
      _ = ((availableTrianglesContainingPair S P).card : ℝ) *
          (((3 + Kpair : ℕ) : ℝ) * ((3 * Δ + Kglobal : ℕ) : ℝ)) := by
          ring
  · positivity

/-- The survival-masked conditional second moment has the sharp envelope
`d (3+K)(3Δ+K) / |A|`.  The catastrophic deletion of the whole pair star
does not enter this estimate. -/
theorem greedyKernel_expectationReal_fixedPair_sqIncrement_if_alive_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {Δ K : ℕ}
    (hS : PairTrajectoryInvariant F S₀ S) (hA : S.available.Nonempty)
    (hpair : HasAvailablePairCutoff Δ S)
    (htwo : HasTwoAwayCutoff F K S) :
    (greedyKernel F S).expectationReal (fun S' ↦
        if PairAlive P S' then
          (fixedPairAvailableCountReal S₀ P S' -
            fixedPairAvailableCountReal S₀ P S) ^ 2
        else 0) ≤
      (S.available.card : ℝ)⁻¹ *
        (((availableTrianglesContainingPair S P).card : ℝ) *
          (((3 + K : ℕ) : ℝ) * ((3 * Δ + K : ℕ) : ℝ))) := by
  exact greedyKernel_expectationReal_fixedPair_sqIncrement_if_alive_le_of_pairCutoff
    hP hS hA hpair htwo.hasPairTwoAwayCutoff htwo

/-- Pair-local form of the survival-masked upper-drift estimate. -/
theorem greedyKernel_expectationReal_fixedPairUpperIncrement_if_alive_le_zero_of_pairCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {Δ δ K : ℕ}
    (hS : PairTrajectoryInvariant F S₀ S) (hA : S.available.Nonempty)
    (hpair : HasAvailablePairCutoff Δ S)
    (htwo : HasPairTwoAwayCutoff F K S)
    (hfloor : HasAvailablePairFloor δ S) (hδ : 1 ≤ δ)
    (halive : PairAlive P S) (hsmall : 3 + K < δ)
    (dq : ℝ) (hdq : dq ≤ 0)
    (hDrift :
      -(S.available.card : ℝ)⁻¹ *
          (((availableTrianglesContainingPair S P).card : ℝ) *
            (3 * δ - 2 - Δ : ℕ)) ≤ dq) :
    (greedyKernel F S).expectationReal (fun S' ↦
        if PairAlive P S' then
          (fixedPairAvailableCountReal S₀ P S' -
            fixedPairAvailableCountReal S₀ P S) - dq
        else 0) ≤ 0 := by
  have hcurrentFloor :
      δ ≤ (availableTrianglesContainingPair S P).card :=
    hfloor P hP halive
  rw [greedyKernel_expectationReal_of_nonempty F S hA]
  let del : TripleOn V → ℕ := fun T ↦
    (greedyDeletedIn F
      (availableTrianglesContainingPair S P) S T).card
  let indicator : TripleOn V → ℝ := fun T ↦
    if ¬ P ⊆ T.1 then (del T : ℝ) else 0
  have hpoint : ∀ T : S.available,
      (if PairAlive P (greedyStep F S T.1) then
          (fixedPairAvailableCountReal S₀ P (greedyStep F S T.1) -
            fixedPairAvailableCountReal S₀ P S) - dq
        else 0) ≤ -indicator T.1 - dq := by
    intro T
    have haliveIff := pairAlive_greedyStep_iff_not_subset_of_floor_of_pairCutoff
      hP hS.1 T.2 htwo hcurrentFloor hsmall
    by_cases hPT : P ⊆ T.1
    · have hdead : ¬ PairAlive P (greedyStep F S T.1) := by
        simpa [hPT] using haliveIff
      simp [hdead, indicator, hPT]
      linarith
    · have halive : PairAlive P (greedyStep F S T.1) :=
        haliveIff.mpr hPT
      simp only [halive, if_true]
      rw [fixedPairAvailableCountReal_step_sub F S₀ S P T.1 hS.2]
      simp [indicator, del, hPT]
  have hindicator :
      (∑ T : S.available, indicator T.1) =
        ∑ T ∈ nonPairSelectors S P, (del T : ℝ) := by
    calc
      (∑ T : S.available, indicator T.1) =
          ∑ T ∈ S.available, indicator T := by
            rw [Finset.univ_eq_attach]
            exact Finset.sum_attach S.available indicator
      _ = ∑ T ∈ nonPairSelectors S P, (del T : ℝ) := by
          rw [← Finset.sum_filter]
          rfl
  have hnonPairNat :=
    pairStar_card_mul_threeFloor_sub_two_sub_cutoff_le_sum_nonPair
      hP hS.1 hfloor hδ hpair
  have hnonPairReal :
      (((availableTrianglesContainingPair S P).card : ℝ) *
        (3 * δ - 2 - Δ : ℕ)) ≤
        ∑ T ∈ nonPairSelectors S P, (del T : ℝ) := by
    exact_mod_cast hnonPairNat
  calc
    (S.available.card : ℝ)⁻¹ *
        ∑ T : S.available,
          (if PairAlive P (greedyStep F S T.1) then
              (fixedPairAvailableCountReal S₀ P (greedyStep F S T.1) -
                fixedPairAvailableCountReal S₀ P S) - dq
            else 0) ≤
        (S.available.card : ℝ)⁻¹ *
          ∑ T : S.available, (-indicator T.1 - dq) := by
            apply mul_le_mul_of_nonneg_left
            · exact sum_le_sum fun T _hT ↦ hpoint T
            · positivity
    _ = (S.available.card : ℝ)⁻¹ *
          (-(∑ T ∈ nonPairSelectors S P, (del T : ℝ)) -
            (S.available.card : ℝ) * dq) := by
          simp only [sum_sub_distrib, sum_neg_distrib, sum_const,
            nsmul_eq_mul, card_univ, Fintype.card_coe, hindicator]
    _ ≤ (S.available.card : ℝ)⁻¹ *
          (-(((availableTrianglesContainingPair S P).card : ℝ) *
              (3 * δ - 2 - Δ : ℕ)) -
            (S.available.card : ℝ) * dq) := by
          apply mul_le_mul_of_nonneg_left
          · linarith
          · positivity
    _ = -(S.available.card : ℝ)⁻¹ *
          (((availableTrianglesContainingPair S P).card : ℝ) *
            (3 * δ - 2 - Δ : ℕ)) - dq := by
          have hcardPos : (0 : ℝ) < S.available.card := by
            exact_mod_cast card_pos.mpr hA
          field_simp
    _ ≤ 0 := sub_nonpos.mpr hDrift

/-- The survival-masked upper-deviation increment has nonpositive drift when
the target decreases no faster than the deletion incidence left after the
pair-killing selectors are removed. -/
theorem greedyKernel_expectationReal_fixedPairUpperIncrement_if_alive_le_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {Δ δ K : ℕ}
    (hS : PairTrajectoryInvariant F S₀ S) (hA : S.available.Nonempty)
    (hpair : HasAvailablePairCutoff Δ S)
    (htwo : HasTwoAwayCutoff F K S)
    (hfloor : HasAvailablePairFloor δ S) (hδ : 1 ≤ δ)
    (halive : PairAlive P S) (hsmall : 3 + K < δ)
    (dq : ℝ) (hdq : dq ≤ 0)
    (hDrift :
      -(S.available.card : ℝ)⁻¹ *
          (((availableTrianglesContainingPair S P).card : ℝ) *
            (3 * δ - 2 - Δ : ℕ)) ≤ dq) :
    (greedyKernel F S).expectationReal (fun S' ↦
        if PairAlive P S' then
          (fixedPairAvailableCountReal S₀ P S' -
            fixedPairAvailableCountReal S₀ P S) - dq
        else 0) ≤ 0 := by
  exact
    greedyKernel_expectationReal_fixedPairUpperIncrement_if_alive_le_zero_of_pairCutoff
      hP hS hA hpair htwo.hasPairTwoAwayCutoff hfloor hδ halive hsmall dq hdq hDrift

end

end Erdos207
