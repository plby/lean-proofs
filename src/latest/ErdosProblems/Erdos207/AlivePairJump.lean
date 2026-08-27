/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.StoppedPairExtensionConcentration
import ErdosProblems.Erdos207.PairTwoAwayCutoff

/-!
# Small jumps while a tracked pair remains alive

The large pair-star deletion occurs only when the selected triangle covers
the tracked pair; that transition kills the pair.  Conditional on the pair
remaining alive, pair-collision deletions from its star are indexed by one of
the three vertices of the selected triangle.  Hence there are at most three,
plus the separately bounded two-away deletions.
-/

namespace Erdos207

open Finset

noncomputable section

/-- At most one triple contains a prescribed three-element vertex set. -/
theorem card_universeTriplesContainingPair_le_one_of_card_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : Finset V) (hR : R.card = 3) :
    (universeTriplesContainingPair R).card ≤ 1 := by
  rw [card_le_one]
  intro T hT U hU
  apply Subtype.ext
  have hRT : R ⊆ T.1 := mem_universeTriplesContainingPair_iff.mp hT
  have hRU : R ⊆ U.1 := mem_universeTriplesContainingPair_iff.mp hU
  have hRT' : R = T.1 := eq_of_subset_of_card_le hRT (by rw [hR, T.2])
  have hRU' : R = U.1 := eq_of_subset_of_card_le hRU (by rw [hR, U.2])
  exact hRT'.symm.trans hRU'

/-- If a selected triangle does not contain `P`, at most its three vertices
can index pair-sharing targets in the `P`-star. -/
theorem card_pairSharingTargets_pairStar_le_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (P : Finset V) (hP : P.card = 2)
    (T : TripleOn V) (hPT : ¬ P ⊆ T.1) :
    (pairSharingTargets (availableTrianglesContainingPair S P) T).card ≤ 3 := by
  let cover : TripleSystemOn V :=
    (T.1 \ P).biUnion fun x ↦ universeTriplesContainingPair (insert x P)
  have hsubset :
      pairSharingTargets (availableTrianglesContainingPair S P) T ⊆ cover := by
    intro U hU
    have hdata := mem_filter.mp hU
    have hPU : P ⊆ U.1 :=
      (mem_availableTrianglesContainingPair_iff.mp hdata.1).2
    have hdiffCard : (U.1 \ P).card = 1 := by
      rw [card_sdiff_of_subset hPU, U.2, hP]
    have hdiffNonempty : (U.1 \ P).Nonempty := card_pos.mp (by omega)
    let x := hdiffNonempty.choose
    have hxDiff : x ∈ U.1 \ P := hdiffNonempty.choose_spec
    have hxU : x ∈ U.1 := (mem_sdiff.mp hxDiff).1
    have hxP : x ∉ P := (mem_sdiff.mp hxDiff).2
    have hxT : x ∈ T.1 := by
      by_contra hxnotT
      have hinterSub : U.1 ∩ T.1 ⊆ P ∩ T.1 := by
        intro y hy
        have hyU := (mem_inter.mp hy).1
        have hyT := (mem_inter.mp hy).2
        have hyP : y ∈ P := by
          by_contra hynotP
          have hyDiff : y ∈ U.1 \ P := mem_sdiff.mpr ⟨hyU, hynotP⟩
          have hxy : y = x := by
            exact Finset.card_le_one.mp
              (by omega : (U.1 \ P).card ≤ 1) y hyDiff x hxDiff
          exact hxnotT (hxy ▸ hyT)
        exact mem_inter.mpr ⟨hyP, hyT⟩
      have hinterProper : P ∩ T.1 ⊂ P := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨inter_subset_left, ?_⟩
        intro heq
        apply hPT
        intro y hyP
        have : y ∈ P ∩ T.1 := by simpa only [heq] using hyP
        exact (mem_inter.mp this).2
      have hinterCard : (P ∩ T.1).card < 2 := by
        simpa only [hP] using card_lt_card hinterProper
      have hshare : 2 ≤ (U.1 ∩ T.1).card := by
        rw [mem_triplesSharingPair_iff] at hdata
        exact hdata.2
      exact (not_lt_of_ge hshare)
        ((card_le_card hinterSub).trans_lt hinterCard)
    apply mem_biUnion.mpr
    refine ⟨x, mem_sdiff.mpr ⟨hxT, hxP⟩, ?_⟩
    apply mem_universeTriplesContainingPair_iff.mpr
    exact insert_subset hxU hPU
  calc
    (pairSharingTargets (availableTrianglesContainingPair S P) T).card ≤
        cover.card := card_le_card hsubset
    _ ≤ ∑ x ∈ T.1 \ P,
        (universeTriplesContainingPair (insert x P)).card := card_biUnion_le
    _ ≤ ∑ _x ∈ T.1 \ P, 1 := by
      apply sum_le_sum
      intro x hx
      have hxP : x ∉ P := (mem_sdiff.mp hx).2
      apply card_universeTriplesContainingPair_le_one_of_card_three
      rw [card_insert_of_notMem hxP, hP]
    _ = (T.1 \ P).card := by simp
    _ ≤ T.1.card := card_le_card (sdiff_subset)
    _ = 3 := T.2

/-- If selecting `T` leaves the tracked pair alive, then `T` cannot contain
that pair. -/
theorem not_pair_subset_selected_of_step_pairAlive
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {T : TripleOn V}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    (halive : PairAlive P (greedyStep F S T)) : ¬ P ⊆ T.1 := by
  intro hPT
  have hTstar : T ∈ availableTrianglesContainingPair S P :=
    mem_availableTrianglesContainingPair_iff.mpr ⟨hT, hPT⟩
  obtain ⟨U, hU⟩ := halive
  have hUold : U ∈ availableTrianglesContainingPair S P :=
    availableTrianglesContainingPair_step_subset F S P T hU
  have hdeleted := mem_greedyDeletedIn_pairStar_of_mem
    hP hS hTstar hUold
  exact (mem_sdiff.mp hdeleted).2
    (mem_inter.mpr
      ⟨(mem_availableTrianglesContainingPair_iff.mp hU).1, hUold⟩)

/-- If the selected triangle does not contain the tracked pair, deletion from
its pair star is at most `3 + K`. -/
theorem card_greedyDeletedIn_pairStar_le_three_add_twoAway_of_not_subset_of_pairCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {T : TripleOn V} {K : ℕ}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    (htwo : HasPairTwoAwayCutoff F K S)
    (hPT : ¬ P ⊆ T.1) :
    (greedyDeletedIn F (availableTrianglesContainingPair S P) S T).card ≤
      3 + K := by
  let Q := availableTrianglesContainingPair S P
  have hsub : greedyDeletedIn F Q S T ⊆
      pairSharingTargets Q T ∪
        (Q ∩ nonPairTwoAwayForbiddenTriangles F S.chosen T) := by
    intro U hU
    have hUQ := (mem_sdiff.mp hU).1 |> (mem_inter.mp ·) |>.2
    have hobstruction := greedyDeletedIn_subset_pairSharing_union_twoAway
      hS hT hU
    rw [mem_union] at hobstruction ⊢
    rcases hobstruction with hshare | htwoAway
    · left
      apply mem_filter.mpr
      refine ⟨hUQ, ?_⟩
      rw [mem_triplesSharingPair_iff] at hshare ⊢
      simpa [inter_comm] using hshare
    · by_cases hshare : U ∈ triplesSharingPair T
      · left
        apply mem_filter.mpr
        refine ⟨hUQ, ?_⟩
        rw [mem_triplesSharingPair_iff] at hshare ⊢
        simpa [inter_comm] using hshare
      · right
        exact mem_inter.mpr ⟨hUQ, mem_sdiff.mpr ⟨htwoAway, hshare⟩⟩
  calc
    (greedyDeletedIn F Q S T).card ≤
        (pairSharingTargets Q T ∪
          (Q ∩ nonPairTwoAwayForbiddenTriangles F S.chosen T)).card :=
        card_le_card hsub
    _ ≤ (pairSharingTargets Q T).card +
        (Q ∩ nonPairTwoAwayForbiddenTriangles F S.chosen T).card :=
      card_union_le _ _
    _ ≤ 3 + K := Nat.add_le_add
      (card_pairSharingTargets_pairStar_le_three S P hP T
        hPT)
      (htwo T hT P hP hPT)

/-- The global cutoff specializes to the pair-local deletion bound. -/
theorem card_greedyDeletedIn_pairStar_le_three_add_twoAway_of_not_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {T : TripleOn V} {K : ℕ}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    (htwo : HasTwoAwayCutoff F K S)
    (hPT : ¬ P ⊆ T.1) :
    (greedyDeletedIn F (availableTrianglesContainingPair S P) S T).card ≤
      3 + K := by
  exact
    card_greedyDeletedIn_pairStar_le_three_add_twoAway_of_not_subset_of_pairCutoff
      hP hS hT htwo.hasPairTwoAwayCutoff hPT

/-- Alive-to-alive deletion from one pair star is at most `3 + K`. -/
theorem card_greedyDeletedIn_pairStar_le_three_add_twoAway_of_step_alive_of_pairCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {T : TripleOn V} {K : ℕ}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    (htwo : HasPairTwoAwayCutoff F K S)
    (halive : PairAlive P (greedyStep F S T)) :
    (greedyDeletedIn F (availableTrianglesContainingPair S P) S T).card ≤
      3 + K := by
  exact
    card_greedyDeletedIn_pairStar_le_three_add_twoAway_of_not_subset_of_pairCutoff
      hP hS hT htwo
        (not_pair_subset_selected_of_step_pairAlive hP hS hT halive)

/-- The global cutoff specializes the alive-to-alive pair-star bound. -/
theorem card_greedyDeletedIn_pairStar_le_three_add_twoAway_of_step_alive
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {T : TripleOn V} {K : ℕ}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    (htwo : HasTwoAwayCutoff F K S)
    (halive : PairAlive P (greedyStep F S T)) :
    (greedyDeletedIn F (availableTrianglesContainingPair S P) S T).card ≤
      3 + K := by
  exact
    card_greedyDeletedIn_pairStar_le_three_add_twoAway_of_step_alive_of_pairCutoff
      hP hS hT htwo.hasPairTwoAwayCutoff halive

/-- If the current pair star has floor `δ > 3 + K`, every selection not
covering the tracked pair leaves that pair alive. -/
theorem pairAlive_greedyStep_of_not_subset_of_floor_of_pairCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {T : TripleOn V} {K δ : ℕ}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    (htwo : HasPairTwoAwayCutoff F K S)
    (hfloor : δ ≤ (availableTrianglesContainingPair S P).card)
    (hsmall : 3 + K < δ) (hPT : ¬ P ⊆ T.1) :
    PairAlive P (greedyStep F S T) := by
  let Q := availableTrianglesContainingPair S P
  have hdeleted :=
    card_greedyDeletedIn_pairStar_le_three_add_twoAway_of_not_subset_of_pairCutoff
      hP hS hT htwo hPT
  have hcard := greedyDeletedIn_card_add_step_card F Q S T
  have hstep : (greedyStep F S T).available ⊆ S.available :=
    greedyStep_available_subset F S T
  have hQsub : Q ⊆ S.available := by
    intro U hU
    exact (mem_availableTrianglesContainingPair_iff.mp hU).1
  have hnew : greedyAvailableIn Q (greedyStep F S T) =
      availableTrianglesContainingPair (greedyStep F S T) P := by
    exact greedyAvailableIn_initialPairStar_eq_current hstep
  have hold : greedyAvailableIn Q S = Q := inter_eq_right.mpr hQsub
  rw [hnew, hold] at hcard
  apply card_pos.mp
  dsimp only [Q] at hcard
  omega

/-- The global cutoff specializes the pair-local survival lemma. -/
theorem pairAlive_greedyStep_of_not_subset_of_floor
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {T : TripleOn V} {K δ : ℕ}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    (htwo : HasTwoAwayCutoff F K S)
    (hfloor : δ ≤ (availableTrianglesContainingPair S P).card)
    (hsmall : 3 + K < δ) (hPT : ¬ P ⊆ T.1) :
    PairAlive P (greedyStep F S T) := by
  exact pairAlive_greedyStep_of_not_subset_of_floor_of_pairCutoff
    hP hS hT htwo.hasPairTwoAwayCutoff hfloor hsmall hPT

/-- Above the strict survival floor `3 + K`, a supported greedy step leaves
the tracked pair alive exactly when the selected triangle does not cover it. -/
theorem pairAlive_greedyStep_iff_not_subset_of_floor
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {T : TripleOn V} {K δ : ℕ}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    (htwo : HasTwoAwayCutoff F K S)
    (hfloor : δ ≤ (availableTrianglesContainingPair S P).card)
    (hsmall : 3 + K < δ) :
    PairAlive P (greedyStep F S T) ↔ ¬ P ⊆ T.1 := by
  constructor
  · exact not_pair_subset_selected_of_step_pairAlive hP hS hT
  · exact pairAlive_greedyStep_of_not_subset_of_floor
      hP hS hT htwo hfloor hsmall

/-- Pair-local form of the exact survival criterion. -/
theorem pairAlive_greedyStep_iff_not_subset_of_floor_of_pairCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {T : TripleOn V} {K δ : ℕ}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    (htwo : HasPairTwoAwayCutoff F K S)
    (hfloor : δ ≤ (availableTrianglesContainingPair S P).card)
    (hsmall : 3 + K < δ) :
    PairAlive P (greedyStep F S T) ↔ ¬ P ⊆ T.1 := by
  constructor
  · exact not_pair_subset_selected_of_step_pairAlive hP hS hT
  · exact pairAlive_greedyStep_of_not_subset_of_floor_of_pairCutoff
      hP hS hT htwo hfloor hsmall

/-- The fixed initial pair-count observable has a small negative jump on
alive-to-alive transitions. -/
theorem greedyKernel_fixedPair_alive_increment_lower_of_pairCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S S' : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {K : ℕ}
    (hS : PairTrajectoryInvariant F S₀ S) (hA : S.available.Nonempty)
    (htwo : HasPairTwoAwayCutoff F K S)
    (hmass : 0 < (greedyKernel F S).mass S') (halive : PairAlive P S') :
    -((3 + K : ℕ) : ℝ) ≤
      fixedPairAvailableCountReal S₀ P S' -
        fixedPairAvailableCountReal S₀ P S := by
  obtain ⟨T, hT, rfl⟩ :=
    greedyKernel_supported_step_of_nonempty F S hA _ hmass
  rw [fixedPairAvailableCountReal_step_sub F S₀ S P T hS.2]
  have hcard :=
    card_greedyDeletedIn_pairStar_le_three_add_twoAway_of_step_alive_of_pairCutoff
      hP hS.1 hT htwo halive
  have hcardReal :
      ((greedyDeletedIn F (availableTrianglesContainingPair S P) S T).card : ℝ) ≤
        ((3 + K : ℕ) : ℝ) := by
    exact_mod_cast hcard
  linarith

/-- The global cutoff specializes the pair-local alive jump bound. -/
theorem greedyKernel_fixedPair_alive_increment_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S S' : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {K : ℕ}
    (hS : PairTrajectoryInvariant F S₀ S) (hA : S.available.Nonempty)
    (htwo : HasTwoAwayCutoff F K S)
    (hmass : 0 < (greedyKernel F S).mass S') (halive : PairAlive P S') :
    -((3 + K : ℕ) : ℝ) ≤
      fixedPairAvailableCountReal S₀ P S' -
        fixedPairAvailableCountReal S₀ P S := by
  exact greedyKernel_fixedPair_alive_increment_lower_of_pairCutoff
    hP hS hA htwo.hasPairTwoAwayCutoff hmass halive

/-- A nonincreasing lower target therefore has upper jump `3 + K` while the
tracked pair survives. -/
theorem fixedPairLowerDeviation_alive_increment_le_of_pairCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S S' : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {K i : ℕ} {q : ℕ → ℝ}
    (hS : PairTrajectoryInvariant F S₀ S) (hA : S.available.Nonempty)
    (htwo : HasPairTwoAwayCutoff F K S)
    (hq : q (i + 1) - q i ≤ 0)
    (hmass : 0 < (greedyKernel F S).mass S') (halive : PairAlive P S') :
    fixedPairLowerDeviation q S₀ P (i + 1) S' -
        fixedPairLowerDeviation q S₀ P i S ≤ ((3 + K : ℕ) : ℝ) := by
  have hinc := greedyKernel_fixedPair_alive_increment_lower_of_pairCutoff
    hP hS hA htwo hmass halive
  simp only [fixedPairLowerDeviation]
  linarith

/-- The global cutoff specializes the pair-local lower-deviation jump bound. -/
theorem fixedPairLowerDeviation_alive_increment_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S S' : GreedyStateOn V}
    {P : Finset V} (hP : P.card = 2) {K i : ℕ} {q : ℕ → ℝ}
    (hS : PairTrajectoryInvariant F S₀ S) (hA : S.available.Nonempty)
    (htwo : HasTwoAwayCutoff F K S)
    (hq : q (i + 1) - q i ≤ 0)
    (hmass : 0 < (greedyKernel F S).mass S') (halive : PairAlive P S') :
    fixedPairLowerDeviation q S₀ P (i + 1) S' -
        fixedPairLowerDeviation q S₀ P i S ≤ ((3 + K : ℕ) : ℝ) := by
  exact fixedPairLowerDeviation_alive_increment_le_of_pairCutoff
    hP hS hA htwo.hasPairTwoAwayCutoff hq hmass halive

end

end Erdos207
