/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.GreedyStable

/-!
# Outer dyadic-bin bookkeeping for the CFP greedy process

This module closes the finite bookkeeping gap between the stable source
thresholds and the later structural witness construction.  It constructs
the consecutive threshold bins from first-crossing times, keeps the possible
prefix below the first source threshold explicit, and packages the selected
reserve together with the remaining source set.

The `HApproximation` family needed by preprocessing remains an input.  No
Freiman statement or approximation family is postulated here.
-/

namespace Erdos186.CFP.Greedy

open scoped BigOperators
open GrowthLemmas

/-- The uniform consecutive-threshold factor furnished by the stable
H-approximation comparison. -/
def stableDyadicRatio (maxRank scaleDen : ℕ) : ℕ :=
  2 * (6 * scaleDen) ^ maxRank * (4 * (4 * scaleDen) ^ maxRank) + 1

theorem stableDyadicRatio_pos (maxRank scaleDen : ℕ) :
    0 < stableDyadicRatio maxRank scaleDen := by
  simp [stableDyadicRatio]

/-- Named-constant form of the stable consecutive-threshold estimate. -/
theorem positiveDyadicThreshold_succ_le_stableDyadicRatio
    {A : Finset ℤ} {deletionBudget D n scaleNum scaleDen h dA : ℕ}
    (hzeroA : 0 ∉ A)
    (hstable : Stability.WeaklyStableMinimalFor
      (insert 0 A) deletionBudget D n)
    (hinterval : ∀ z ∈ insert 0 A, 0 ≤ z ∧ z < (n : ℤ))
    (WA : HDimension.HApproximation
      (insert 0 A) (2 ^ h) dA scaleNum scaleDen)
    (hdA : 0 < dA) (hdAD : dA ≤ D) (hfoldn : 2 ^ h ≤ n)
    (haccessible : ∀ B : Finset ℤ, B ⊆ A →
      A.card ≤ B.card + deletionBudget →
      ∃ dB : ℕ, 0 < dB ∧ dB ≤ D ∧
        ∃ _WB : HDimension.HApproximation
            (insert 0 B) (2 ^ h) dB scaleNum scaleDen,
          (2 * scaleDen) ^ dB * (2 ^ h + 1) ^ (dB - 1) <
            (scaleNum * 2 ^ h) ^ dB) :
    positiveDyadicThreshold A deletionBudget (h + 1) ≤
      stableDyadicRatio D scaleDen *
        positiveDyadicThreshold A deletionBudget h := by
  simpa only [stableDyadicRatio] using
    positiveDyadicThreshold_succ_le_of_approximations
      hzeroA hstable hinterval WA hdA hdAD hfoldn haccessible

/-! ## Monotonicity of the two processes being binned -/

/-- Stability relative to the original core's minimal boxes implies the
canonical minimal-box stability of every contained survivor.  This is the
fixed-reference adapter needed after random partitioning: minimal bounding
box volume is monotone under inclusion. -/
theorem weaklyStableMinimalFor_of_fixed_minimalBox
    {W B : Finset ℤ} {deletionBudget maxRank n : ℕ}
    (hBW : B ⊆ W)
    (hstable : Stability.WeaklyStableFor B
      (Stability.minimalBoxFamily W) deletionBudget maxRank (n ^ 2)) :
    Stability.WeaklyStableMinimalFor B deletionBudget maxRank n := by
  apply hstable.mono_boxVolume
  intro d
  cases d with
  | zero => rfl
  | succ d =>
      have hd : 0 < d + 1 := Nat.succ_pos d
      simpa only [Stability.minimalBoxFamily_eq_dBoundingBox B hd,
        Stability.minimalBoxFamily_eq_dBoundingBox W hd]
        using BoundingBox.dBoundingBox_volume_mono (d + 1) hd hBW

/-- Subset sums are monotone throughout a bounded greedy run. -/
theorem sums_subset_of_le {A : Finset ℤ} {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ A.card) :
    sums A i ⊆ sums A j := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ j hij ih =>
      exact (ih (by omega)).trans (sums_mono_step (by omega))

/-- Cardinality form of monotonicity of the greedy subset-sum process. -/
theorem card_sums_mono {A : Finset ℤ} {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ A.card) :
    (sums A i).card ≤ (sums A j).card :=
  Finset.card_le_card (sums_subset_of_le hij hj)

/-- The minimum high-fold cardinality is monotone in the fold parameter. -/
theorem minimumMultifoldCardinality_mono_fold
    (A : Finset ℤ) (deletionBudget : ℕ) :
    Monotone (minimumMultifoldCardinality A deletionBudget) := by
  intro fold₁ fold₂ hfold
  obtain ⟨B, hBA, hBcard, hBmin⟩ :=
    exists_largeSubset_card_multifold_eq_minimum A deletionBudget fold₂
  calc
    minimumMultifoldCardinality A deletionBudget fold₁ ≤
        (multifoldSumset fold₁ (insert 0 B)).card :=
      minimumMultifoldCardinality_le hBA hBcard
    _ ≤ (multifoldSumset fold₂ (insert 0 B)).card := by
      apply Finset.card_le_card
      exact multifoldSumset_mono_index (by simp) hfold
    _ = minimumMultifoldCardinality A deletionBudget fold₂ := hBmin

/-- The rounded dyadic thresholds form a nondecreasing sequence. -/
theorem positiveDyadicThreshold_mono
    (A : Finset ℤ) (deletionBudget : ℕ) :
    Monotone (positiveDyadicThreshold A deletionBudget) := by
  intro h₁ h₂ hh
  simp only [positiveDyadicThreshold, dyadicThreshold, foldThreshold]
  apply Nat.add_le_add_right
  apply Nat.div_le_div_right
  apply minimumMultifoldCardinality_mono_fold
  exact Nat.pow_le_pow_right (by omega : 0 < 2) hh

/-! ## First crossings and the canonical finite bins -/

/-- The first index at most `steps` at which `threshold` is reached.  If it
is never reached before the endpoint, the endpoint itself is returned. -/
noncomputable def firstCrossing
    (c : ℕ → ℕ) (steps threshold : ℕ) : ℕ :=
  Nat.find (show ∃ j, j = steps ∨ threshold ≤ c j from ⟨steps, Or.inl rfl⟩)

theorem firstCrossing_spec (c : ℕ → ℕ) (steps threshold : ℕ) :
    firstCrossing c steps threshold = steps ∨
      threshold ≤ c (firstCrossing c steps threshold) := by
  exact Nat.find_spec
    (show ∃ j, j = steps ∨ threshold ≤ c j from ⟨steps, Or.inl rfl⟩)

theorem firstCrossing_le (c : ℕ → ℕ) (steps threshold : ℕ) :
    firstCrossing c steps threshold ≤ steps := by
  apply Nat.find_min'
  exact Or.inl rfl

theorem lt_firstCrossing {c : ℕ → ℕ} {steps threshold j : ℕ}
    (hj : j < firstCrossing c steps threshold) :
    c j < threshold := by
  have hnot := Nat.find_min
    (show ∃ k, k = steps ∨ threshold ≤ c k from ⟨steps, Or.inl rfl⟩) hj
  omega

theorem threshold_le_at_firstCrossing_of_lt
    {c : ℕ → ℕ} {steps threshold : ℕ}
    (hcross : firstCrossing c steps threshold < steps) :
    threshold ≤ c (firstCrossing c steps threshold) := by
  rcases firstCrossing_spec c steps threshold with h | h
  · omega
  · exact h

theorem firstCrossing_mono_threshold (c : ℕ → ℕ) (steps : ℕ) :
    Monotone (firstCrossing c steps) := by
  intro lower upper hlu
  apply Nat.find_min'
  rcases firstCrossing_spec c steps upper with h | h
  · exact Or.inl h
  · exact Or.inr (hlu.trans h)

theorem firstCrossing_eq_zero_of_le {c : ℕ → ℕ}
    {steps threshold : ℕ} (h : threshold ≤ c 0) :
    firstCrossing c steps threshold = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Nat.find_min'
  exact Or.inr h

theorem firstCrossing_eq_steps_of_end_lt
    {c : ℕ → ℕ} {steps threshold : ℕ}
    (hmono : ∀ i j, i ≤ j → j ≤ steps → c i ≤ c j)
    (hend : c steps < threshold) :
    firstCrossing c steps threshold = steps := by
  apply le_antisymm (firstCrossing_le c steps threshold)
  by_contra hnot
  have hcross : firstCrossing c steps threshold < steps := by omega
  have hat := threshold_le_at_firstCrossing_of_lt hcross
  have hle := hmono _ _ hcross.le (Nat.le_refl steps)
  omega

/-- Canonical start of dyadic threshold bin `h`. -/
noncomputable def dyadicBinStart
    (A : Finset ℤ) (deletionBudget steps h : ℕ) : ℕ :=
  firstCrossing (fun j ↦ (sums A j).card) steps
    (positiveDyadicThreshold A deletionBudget h)

/-- Canonical length of dyadic threshold bin `h`. -/
noncomputable def dyadicBinLength
    (A : Finset ℤ) (deletionBudget steps h : ℕ) : ℕ :=
  dyadicBinStart A deletionBudget steps (h + 1) -
    dyadicBinStart A deletionBudget steps h

theorem dyadicBinStart_mono (A : Finset ℤ)
    (deletionBudget steps : ℕ) :
    Monotone (dyadicBinStart A deletionBudget steps) := by
  intro h₁ h₂ hh
  apply firstCrossing_mono_threshold
  exact positiveDyadicThreshold_mono A deletionBudget hh

theorem dyadicBinStart_le
    (A : Finset ℤ) (deletionBudget steps h : ℕ) :
    dyadicBinStart A deletionBudget steps h ≤ steps :=
  firstCrossing_le _ _ _

theorem dyadicBin_block_end
    (A : Finset ℤ) (deletionBudget steps h : ℕ) :
    dyadicBinStart A deletionBudget steps h +
        dyadicBinLength A deletionBudget steps h =
      dyadicBinStart A deletionBudget steps (h + 1) := by
  exact Nat.add_sub_of_le
    (dyadicBinStart_mono A deletionBudget steps (Nat.le_succ h))

theorem dyadicBin_block_end_le_steps
    (A : Finset ℤ) (deletionBudget steps h : ℕ) :
    dyadicBinStart A deletionBudget steps h +
        dyadicBinLength A deletionBudget steps h ≤ steps := by
  rw [dyadicBin_block_end]
  exact dyadicBinStart_le _ _ _ _

theorem dyadicBin_mem {A : Finset ℤ}
    {deletionBudget steps h i : ℕ} (hsteps : steps ≤ A.card)
    (hi : i < dyadicBinLength A deletionBudget steps h) :
    positiveDyadicThreshold A deletionBudget h ≤
        (sums A (dyadicBinStart A deletionBudget steps h + i)).card ∧
      (sums A (dyadicBinStart A deletionBudget steps h + i)).card <
        positiveDyadicThreshold A deletionBudget (h + 1) := by
  let start := dyadicBinStart A deletionBudget steps h
  let next := dyadicBinStart A deletionBudget steps (h + 1)
  have hstartNext : start ≤ next :=
    dyadicBinStart_mono A deletionBudget steps (Nat.le_succ h)
  have hindexNext : start + i < next := by
    dsimp only [dyadicBinLength] at hi
    omega
  have hnextSteps : next ≤ steps := dyadicBinStart_le _ _ _ _
  have hindexSteps : start + i < steps := hindexNext.trans_le hnextSteps
  have hstartSteps : start < steps := by omega
  constructor
  · have hat : positiveDyadicThreshold A deletionBudget h ≤
        (sums A start).card := by
      exact threshold_le_at_firstCrossing_of_lt hstartSteps
    exact hat.trans (card_sums_mono (Nat.le_add_right start i)
      (hindexSteps.le.trans hsteps))
  · exact lt_firstCrossing hindexNext

theorem sum_dyadicBinLength
    (A : Finset ℤ) (deletionBudget steps levels : ℕ) :
    (∑ h ∈ Finset.range levels,
        dyadicBinLength A deletionBudget steps h) =
      dyadicBinStart A deletionBudget steps levels -
        dyadicBinStart A deletionBudget steps 0 := by
  exact Finset.sum_range_tsub
    (dyadicBinStart_mono A deletionBudget steps) levels

/-! ## The outer-bin estimate and reserve/remainder package -/

/-- A canonical threshold-bin run.  `prefix` is the number of initial greedy
steps below the first positive source threshold. -/
structure OuterDyadicRun (A : Finset ℤ)
    (deletionBudget steps terminalLevel ratio : ℕ) where
  steps_le_card : steps ≤ A.card
  steps_le_budget : steps ≤ deletionBudget
  terminal_upper : (sums A steps).card <
    positiveDyadicThreshold A deletionBudget (terminalLevel + 1)
  threshold_ratio : ∀ h ≤ terminalLevel,
    positiveDyadicThreshold A deletionBudget (h + 1) ≤
      ratio * positiveDyadicThreshold A deletionBudget h

namespace OuterDyadicRun

variable {A : Finset ℤ} {deletionBudget steps terminalLevel ratio : ℕ}
    (R : OuterDyadicRun A deletionBudget steps terminalLevel ratio)

/-- The unbinned prefix below the first source threshold. -/
noncomputable def initialPrefix
    (_R : OuterDyadicRun A deletionBudget steps terminalLevel ratio) : ℕ :=
  dyadicBinStart A deletionBudget steps 0

/-- The points chosen by the greedy process form the future reserve. -/
noncomputable def reserve
    (_R : OuterDyadicRun A deletionBudget steps terminalLevel ratio) : Finset ℤ :=
  selected A steps

/-- The points not chosen by the greedy process form the structural source. -/
noncomputable def remainder
    (_R : OuterDyadicRun A deletionBudget steps terminalLevel ratio) : Finset ℤ :=
  available A steps

include R

theorem initialPrefix_le_steps : R.initialPrefix ≤ steps :=
  dyadicBinStart_le A deletionBudget steps 0

theorem initialPrefix_eq_zero
    (hfirst : positiveDyadicThreshold A deletionBudget 0 ≤ 1) :
    R.initialPrefix = 0 := by
  apply firstCrossing_eq_zero_of_le
  simpa using hfirst

theorem terminal_start_eq_steps :
    dyadicBinStart A deletionBudget steps (terminalLevel + 1) = steps := by
  apply firstCrossing_eq_steps_of_end_lt
  · intro i j hij hj
    exact card_sums_mono hij (hj.trans R.steps_le_card)
  · exact R.terminal_upper

theorem cover :
    steps = R.initialPrefix +
      ∑ h ∈ Finset.range (terminalLevel + 1),
        dyadicBinLength A deletionBudget steps h := by
  rw [sum_dyadicBinLength, R.terminal_start_eq_steps]
  exact (Nat.add_sub_of_le R.initialPrefix_le_steps).symm

theorem active_length_le :
    steps - R.initialPrefix ≤ 16 * ratio * 2 ^ terminalLevel := by
  have hlength : ∀ h ≤ terminalLevel,
      dyadicBinLength A deletionBudget steps h ≤
        (8 * ratio) * 2 ^ h := by
    intro h hh
    by_cases hz : dyadicBinLength A deletionBudget steps h = 0
    · simp [hz]
    · have hpos : 0 < dyadicBinLength A deletionBudget steps h :=
        Nat.pos_of_ne_zero hz
      have hrun :=
        greedy_threshold_run_length_le_of_positiveDyadicThreshold
          hpos
          ((dyadicBin_block_end_le_steps A deletionBudget steps h).trans
            R.steps_le_card)
          ((dyadicBin_block_end_le_steps A deletionBudget steps h).trans
            R.steps_le_budget)
          (R.threshold_ratio h hh)
          (fun i hi ↦ dyadicBin_mem R.steps_le_card hi)
      calc
        dyadicBinLength A deletionBudget steps h ≤
            4 * ratio * 2 ^ (h + 1) := hrun
        _ = (8 * ratio) * 2 ^ h := by rw [pow_succ]; ring
  have hsum : steps - R.initialPrefix =
      ∑ h ∈ Finset.range (terminalLevel + 1),
        dyadicBinLength A deletionBudget steps h := by
    rw [sum_dyadicBinLength, R.terminal_start_eq_steps]
    rfl
  calc
    steps - R.initialPrefix =
        ∑ h ∈ Finset.range (terminalLevel + 1),
          dyadicBinLength A deletionBudget steps h := hsum
    _ ≤ (8 * ratio) * (2 ^ (terminalLevel + 1) - 1) :=
      sum_bin_lengths_le _ hlength
    _ ≤ (8 * ratio) * 2 ^ (terminalLevel + 1) :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = 16 * ratio * 2 ^ terminalLevel := by rw [pow_succ]; ring

/-- Full outer-bin estimate, with the unavoidable below-threshold prefix
shown separately. -/
theorem steps_le_prefix_add :
    steps ≤ R.initialPrefix + 16 * ratio * 2 ^ terminalLevel := by
  have hsplit : steps = R.initialPrefix + (steps - R.initialPrefix) :=
    (Nat.add_sub_of_le R.initialPrefix_le_steps).symm
  calc
    steps = R.initialPrefix + (steps - R.initialPrefix) := hsplit
    _ ≤ R.initialPrefix + 16 * ratio * 2 ^ terminalLevel :=
      Nat.add_le_add_left R.active_length_le R.initialPrefix

/-- Exact-cover specialization when the first source threshold is already
reached by the initial singleton subset-sum set. -/
theorem steps_le_of_first_threshold
    (hfirst : positiveDyadicThreshold A deletionBudget 0 ≤ 1) :
    steps ≤ 16 * ratio * 2 ^ terminalLevel := by
  simpa [R.initialPrefix_eq_zero hfirst] using R.steps_le_prefix_add

theorem reserve_subset : R.reserve ⊆ A := selected_subset A steps

theorem reserve_card : R.reserve.card = steps := card_selected_eq R.steps_le_card

theorem remainder_eq : R.remainder = A \ R.reserve := rfl

theorem remainder_subset : R.remainder ⊆ A := Finset.sdiff_subset

theorem reserve_disjoint_remainder : Disjoint R.reserve R.remainder := by
  rw [R.remainder_eq]
  exact Finset.disjoint_sdiff

theorem reserve_union_remainder : R.reserve ∪ R.remainder = A := by
  rw [R.remainder_eq, Finset.union_sdiff_of_subset R.reserve_subset]

theorem remainder_card : R.remainder.card = A.card - steps :=
  card_available_eq R.steps_le_card

end OuterDyadicRun

end Erdos186.CFP.Greedy

namespace Erdos186.CFP

/-! ## Preprocessing joined to the canonical greedy run -/

/-- The checked output of preprocessing together with one complete greedy
run on the nonzero part of the stable core.  The exact preprocessing loss
and the possible below-threshold greedy prefix remain visible. -/
structure PreprocessedGreedyStage (A : Finset ℤ)
    (stableBudget maxRank n C0 scaleNum scaleDen totalLoss : ℕ) where
  weakCore : Finset ℤ
  core : Finset ℤ
  relevant : Finset ℕ
  boxesProper : Stability.RelevantBoxesProper weakCore relevant
  core_subset_weakCore : core ⊆ weakCore
  weakCore_subset_source : weakCore ⊆ A
  zero_mem_core : 0 ∈ core
  source_card_le : A.card ≤ core.card + totalLoss
  stable : Stability.StronglyStableFor core
    (Stability.minimalBoxFamily weakCore) stableBudget maxRank (n ^ 2)
    relevant (Stability.minimalIdentificationFamily boxesProper) C0
  steps : ℕ
  terminalLevel : ℕ
  ratio : ℕ
  run : Greedy.OuterDyadicRun (core.erase 0) stableBudget steps
    terminalLevel ratio

namespace PreprocessedGreedyStage

variable {A : Finset ℤ}
    {stableBudget maxRank n C0 scaleNum scaleDen totalLoss : ℕ}
    (S : PreprocessedGreedyStage A stableBudget maxRank n C0
      scaleNum scaleDen totalLoss)

/-- The unanchored source on which the greedy process runs. -/
noncomputable def greedySource
    (_S : PreprocessedGreedyStage A stableBudget maxRank n C0
      scaleNum scaleDen totalLoss) : Finset ℤ :=
  _S.core.erase 0

/-- The selected elements, ready to be one member of the reserve family
consumed by `enhancedCFPWitness_of_disjoint_reserveFamily`. -/
noncomputable def reserve
    (_S : PreprocessedGreedyStage A stableBudget maxRank n C0
      scaleNum scaleDen totalLoss) : Finset ℤ :=
  _S.run.reserve

/-- The unselected nonzero elements of the stable core. -/
noncomputable def remainder
    (_S : PreprocessedGreedyStage A stableBudget maxRank n C0
      scaleNum scaleDen totalLoss) : Finset ℤ :=
  _S.run.remainder

/-- The remaining structural source, with the distinguished zero restored. -/
noncomputable def anchoredRemainder
    (_S : PreprocessedGreedyStage A stableBudget maxRank n C0
      scaleNum scaleDen totalLoss) : Finset ℤ :=
  insert 0 _S.remainder

include S

theorem greedySource_eq : S.greedySource = S.core.erase 0 := rfl

theorem reserve_subset_greedySource : S.reserve ⊆ S.greedySource :=
  S.run.reserve_subset

theorem reserve_subset_core : S.reserve ⊆ S.core := by
  exact S.reserve_subset_greedySource.trans (Finset.erase_subset _ _)

theorem reserve_subset_source : S.reserve ⊆ A := by
  exact S.reserve_subset_core.trans
    (S.core_subset_weakCore.trans S.weakCore_subset_source)

theorem reserve_card : S.reserve.card = S.steps := S.run.reserve_card

theorem zero_not_mem_reserve : 0 ∉ S.reserve := by
  intro hzero
  exact Finset.notMem_erase 0 S.core (S.reserve_subset_greedySource hzero)

theorem remainder_subset_greedySource : S.remainder ⊆ S.greedySource :=
  S.run.remainder_subset

theorem remainder_subset_core : S.remainder ⊆ S.core := by
  exact S.remainder_subset_greedySource.trans (Finset.erase_subset _ _)

theorem zero_not_mem_remainder : 0 ∉ S.remainder := by
  intro hzero
  exact Finset.notMem_erase 0 S.core (S.remainder_subset_greedySource hzero)

theorem anchoredRemainder_subset_core : S.anchoredRemainder ⊆ S.core := by
  exact Finset.insert_subset S.zero_mem_core S.remainder_subset_core

theorem anchoredRemainder_subset_source : S.anchoredRemainder ⊆ A := by
  exact S.anchoredRemainder_subset_core.trans
    (S.core_subset_weakCore.trans S.weakCore_subset_source)

theorem reserve_disjoint_anchoredRemainder :
    Disjoint S.reserve S.anchoredRemainder := by
  rw [Finset.disjoint_left]
  intro x hx hxa
  rcases Finset.mem_insert.mp hxa with rfl | hxrem
  · exact S.zero_not_mem_reserve hx
  · exact Finset.disjoint_left.mp S.run.reserve_disjoint_remainder hx hxrem

theorem reserve_union_anchoredRemainder :
    S.reserve ∪ S.anchoredRemainder = S.core := by
  have hsplit : S.reserve ∪ S.remainder = S.greedySource :=
    S.run.reserve_union_remainder
  calc
    S.reserve ∪ S.anchoredRemainder =
        insert 0 (S.reserve ∪ S.remainder) := by
      ext x
      simp only [anchoredRemainder, Finset.mem_union, Finset.mem_insert]
      tauto
    _ = insert 0 S.greedySource := by rw [hsplit]
    _ = insert 0 (S.core.erase 0) := rfl
    _ = S.core := Finset.insert_erase S.zero_mem_core

theorem remainder_card :
    S.remainder.card = (S.core.erase 0).card - S.steps :=
  S.run.remainder_card

theorem core_card_eq_anchoredRemainder_add_steps :
    S.core.card = S.anchoredRemainder.card + S.steps := by
  have hcoreErase : (S.core.erase 0).card + 1 = S.core.card :=
    Finset.card_erase_add_one S.zero_mem_core
  have hrem : S.remainder.card = (S.core.erase 0).card - S.steps :=
    S.remainder_card
  have hsteps : S.steps ≤ (S.core.erase 0).card := S.run.steps_le_card
  have hanchor : S.anchoredRemainder.card = S.remainder.card + 1 := by
    rw [anchoredRemainder, Finset.card_insert_of_notMem S.zero_not_mem_remainder]
  omega

/-- The preprocessing loss and the selected reserve are the only losses in
the surviving anchored structural source. -/
theorem source_card_le_anchoredRemainder_add_loss :
    A.card ≤ S.anchoredRemainder.card + (totalLoss + S.steps) := by
  have hsource := S.source_card_le
  rw [S.core_card_eq_anchoredRemainder_add_steps] at hsource
  omega

/-- Substitute the completed outer-bin estimate into the total survivor
loss. -/
theorem source_card_le_anchoredRemainder_add_outerBound :
    A.card ≤ S.anchoredRemainder.card +
      (totalLoss +
        (S.run.initialPrefix + 16 * S.ratio * 2 ^ S.terminalLevel)) := by
  exact S.source_card_le_anchoredRemainder_add_loss.trans
    (Nat.add_le_add_left
      (Nat.add_le_add_left S.run.steps_le_prefix_add totalLoss)
      S.anchoredRemainder.card)

theorem steps_le_initialPrefix_add :
    S.steps ≤ S.run.initialPrefix +
      16 * S.ratio * 2 ^ S.terminalLevel :=
  S.run.steps_le_prefix_add

end PreprocessedGreedyStage

/-! ## End-to-end finite constructor -/

/-- The exact approximation input consumed by `preprocessing_lemma238`,
named here so the outer bookkeeping theorem can expose a readable boundary.
The construction of this family is deliberately left to the H-dimension
part of the proof. -/
abbrev PreprocessingApproximationInput (A : Finset ℤ)
    (stableBudget maxRank n C0 scaleNum scaleDen : ℕ) : Prop :=
  ∀ {W : Finset ℤ}, W ⊆ A → 0 ∈ W →
    Stability.WeaklyStableMinimalFor W (2 * stableBudget) maxRank n →
    ∃ (relevant : Finset ℕ)
      (_hproper : Stability.RelevantBoxesProper W relevant)
      (hAt : {d // d ∈ relevant} → ℕ),
      (∀ d : {d // d ∈ relevant},
        Nonempty (HDimension.HApproximation W (hAt d) d.1
          scaleNum scaleDen)) ∧
      (∀ d : {d // d ∈ relevant}, d.1 ≤ maxRank) ∧
      (∀ d : {d // d ∈ relevant}, hAt d ≤ n) ∧
      (∀ d : {d // d ∈ relevant},
        4 * (6 * scaleDen) ^ maxRank * (4 * scaleDen) ^ maxRank ≤ hAt d) ∧
      (∀ {B : Finset ℤ}, B ⊆ W →
        W.card ≤ B.card +
          (stableBudget / C0) *
            (maxRank * Nat.log 2
              (4 * (6 * scaleDen) ^ maxRank *
                (4 * scaleDen) ^ maxRank) + 1) →
        0 ∈ B → ∀ d : {d // d ∈ relevant},
          ∃ e : ℕ, 0 < e ∧ e ≤ maxRank ∧
            ∃ _V : HDimension.HApproximation B (hAt d) e
                scaleNum scaleDen,
              (2 * scaleDen) ^ e * (hAt d + 1) ^ (e - 1) <
                (scaleNum * hAt d) ^ e) ∧
      (stableBudget / C0) *
        (maxRank * Nat.log 2
          (4 * (6 * scaleDen) ^ maxRank *
            (4 * scaleDen) ^ maxRank)) ≤ stableBudget

/-- The remaining analytic boundary after preprocessing: for every concrete
stable core returned by Lemma 2.38, provide the endpoint and consecutive
threshold ratio of its greedy run.  `OuterDyadicRun` constructs all bin
starts and lengths internally. -/
abbrev StableCoreGreedyInput (A : Finset ℤ)
    (stableBudget maxRank n C0 : ℕ) : Prop :=
  ∀ (W B : Finset ℤ) (relevant : Finset ℕ)
    (hproper : Stability.RelevantBoxesProper W relevant),
    B ⊆ W → W ⊆ A → 0 ∈ B →
    Stability.StronglyStableFor B (Stability.minimalBoxFamily W)
      stableBudget maxRank (n ^ 2) relevant
      (Stability.minimalIdentificationFamily hproper) C0 →
    ∃ steps terminalLevel ratio : ℕ,
      Nonempty
        (Greedy.OuterDyadicRun (B.erase 0) stableBudget steps
          terminalLevel ratio)

/-- Join CFP preprocessing to the completely constructed dyadic-bin run.
Every set, bin, selected reserve, and loss inequality in the result is
concrete; only the H-dimension family and the stable-core terminal/ratio
input remain as explicit proof parameters. -/
theorem exists_preprocessedGreedyStage {A : Finset ℤ}
    {stableBudget maxRank n C0 scaleNum scaleDen totalLoss : ℕ}
    (hzero : 0 ∈ A) (hC0 : 0 < C0)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (happrox : PreprocessingApproximationInput A stableBudget maxRank n C0
      scaleNum scaleDen)
    (hloss : (2 * stableBudget) *
        Preprocessing.boxPotential A maxRank + stableBudget ≤ totalLoss)
    (hgreedy : StableCoreGreedyInput A stableBudget maxRank n C0) :
    Nonempty (PreprocessedGreedyStage A stableBudget maxRank n C0
      scaleNum scaleDen totalLoss) := by
  classical
  obtain ⟨W, B, relevant, hproper, hBW, hWA, hzeroB, hcard, hstable⟩ :=
    Preprocessing.preprocessing_lemma238 hzero hC0 hA happrox
  obtain ⟨steps, terminalLevel, ratio, hrun⟩ :=
    hgreedy W B relevant hproper hBW hWA hzeroB hstable
  let run := Classical.choice hrun
  refine ⟨{
    weakCore := W
    core := B
    relevant := relevant
    boxesProper := hproper
    core_subset_weakCore := hBW
    weakCore_subset_source := hWA
    zero_mem_core := hzeroB
    source_card_le := ?_
    stable := hstable
    steps := steps
    terminalLevel := terminalLevel
    ratio := ratio
    run := run }⟩
  apply hcard.trans
  simpa only [Nat.add_assoc] using Nat.add_le_add_left hloss B.card

/-- Uniform numerical specialization of the preceding constructor.  This
is the exact `100 * beta^2 * t` loss calculation from CFP Lemma 2.38,
joined to the canonical outer dyadic bins. -/
theorem exists_preprocessedGreedyStage_hundred_beta_loss
    {A : Finset ℤ} {n m beta t C0 scaleNum scaleDen : ℕ}
    (hbeta : 1 ≤ beta) (hzero : 0 ∈ A) (hC0 : 0 < C0)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ))
    (hlog : Nat.log 2 n + 1 ≤ beta * (Nat.log 2 m + 1))
    (happrox : PreprocessingApproximationInput A
      (t / (Nat.log 2 m + 1)) (beta + 1) n C0 scaleNum scaleDen)
    (hgreedy : StableCoreGreedyInput A
      (t / (Nat.log 2 m + 1)) (beta + 1) n C0) :
    Nonempty
      (PreprocessedGreedyStage A (t / (Nat.log 2 m + 1))
        (beta + 1) n C0 scaleNum scaleDen (100 * beta ^ 2 * t)) := by
  apply exists_preprocessedGreedyStage hzero hC0 hA happrox
  · exact Preprocessing.preprocessing_loss_le_hundred_beta_sq
      hbeta hzero hA hlog
  · exact hgreedy

end Erdos186.CFP
