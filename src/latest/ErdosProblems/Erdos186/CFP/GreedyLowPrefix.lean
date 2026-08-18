/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.GreedyBookkeeping
import Mathlib.Data.Nat.Log

/-!
# The low-scale prefix of the CFP greedy process

Before the greedy subset-sum process reaches the positive threshold at a
fixed dyadic fold, the source minimum supplies the high-fold hypothesis at
every step.  Grouping `2^(h+1)` consecutive steps and telescoping the
one-step growth inequality shows that every complete block doubles the
number of subset sums.  Consequently the first crossing has only
logarithmically many complete blocks.
-/

namespace Erdos186.CFP.Greedy

open GrowthLemmas

/-- A complete block of `2^(h+1)` steps below the level-`h` threshold
doubles the current subset-sum cardinality. -/
theorem two_mul_card_sums_le_card_sums_add_dyadicBlock
    {A : Finset ℤ} {deletionBudget h start crossing : ℕ}
    (hcrossCard : crossing ≤ A.card)
    (hcrossBudget : crossing ≤ deletionBudget)
    (hblock : start + 2 ^ (h + 1) ≤ crossing)
    (hbelow : ∀ j < crossing,
      (sums A j).card < positiveDyadicThreshold A deletionBudget h) :
    2 * (sums A start).card ≤
      (sums A (start + 2 ^ (h + 1))).card := by
  let q := 2 ^ (h + 1)
  have hq : 0 < q := pow_pos (by omega) _
  have hacc := threshold_run_accumulation
    (fun j ↦ (sums A j).card) start q (sums A start).card q
    (by
      intro i hi
      exact Finset.card_le_card (sums_mono_step (by
        dsimp only [q] at hi ⊢
        omega)))
    (by
      intro i hi
      exact card_sums_mono (Nat.le_add_right start i) (by
        dsimp only [q] at hi ⊢
        omega))
    (by
      intro i hi
      have hij : start + i < crossing := by
        dsimp only [q] at hi ⊢
        omega
      have hfold := dyadicHighFold_of_card_sums_lt_positiveThreshold
        (A := A) (j := start + i) (deletionBudget := deletionBudget)
        (h := h) (hij.trans_le hcrossCard).le
        (hij.trans_le hcrossBudget).le (hbelow _ hij)
      have hgrowth := card_sums_le_two_mul_mul_increment
        (A := A) (j := start + i) (k := 2 ^ h)
        (hij.trans_le hcrossCard) hfold
      simpa only [q, pow_succ, mul_comm (2 ^ h) 2,
        mul_assoc] using hgrowth)
  have hscaled :
      q * (2 * (sums A start).card) ≤
        q * (sums A (start + q)).card := by
    calc
      q * (2 * (sums A start).card) =
          q * (sums A start).card + q * (sums A start).card := by ring
      _ ≤ q * (sums A (start + q)).card := by
        simpa only [Nat.add_comm] using hacc
  have hcancel := Nat.le_of_mul_le_mul_left hscaled hq
  simpa only [q] using hcancel

/-- After `blocks` complete dyadic blocks below a first crossing, the
subset-sum set has cardinality at least `2^blocks`. -/
theorem two_pow_le_card_sums_at_dyadicBlocks
    {A : Finset ℤ} {deletionBudget steps h crossing : ℕ}
    (hcross : crossing =
      dyadicBinStart A deletionBudget steps h)
    (hstepsCard : steps ≤ A.card)
    (hstepsBudget : steps ≤ deletionBudget) :
    ∀ blocks : ℕ, 2 ^ (h + 1) * blocks ≤ crossing →
      2 ^ blocks ≤
        (sums A (2 ^ (h + 1) * blocks)).card := by
  intro blocks
  induction blocks with
  | zero =>
      intro _
      simp
  | succ blocks ih =>
      intro hblocks
      have hcrossSteps : crossing ≤ steps := by
        rw [hcross]
        exact dyadicBinStart_le A deletionBudget steps h
      have hprevious : 2 ^ (h + 1) * blocks ≤ crossing :=
        (Nat.mul_le_mul_left _ (Nat.le_succ blocks)).trans hblocks
      have ih' := ih hprevious
      have hdouble := two_mul_card_sums_le_card_sums_add_dyadicBlock
        (A := A) (deletionBudget := deletionBudget) (h := h)
        (start := 2 ^ (h + 1) * blocks) (crossing := crossing)
        (hcrossSteps.trans hstepsCard) (hcrossSteps.trans hstepsBudget)
        (by simpa only [Nat.mul_succ] using hblocks)
        (by
          intro j hj
          rw [hcross] at hj
          exact lt_firstCrossing hj)
      calc
        2 ^ (blocks + 1) = 2 * 2 ^ blocks := by rw [pow_succ']
        _ ≤ 2 * (sums A (2 ^ (h + 1) * blocks)).card := by gcongr
        _ ≤ (sums A
            (2 ^ (h + 1) * blocks + 2 ^ (h + 1))).card := hdouble
        _ = (sums A (2 ^ (h + 1) * (blocks + 1))).card := by
          rw [Nat.mul_succ]

/-- The first crossing of a level-`h` positive source threshold has at
most `2^(h+1)` times one plus the binary logarithm of that threshold many
greedy steps.  This is the low-prefix estimate used before the consecutive
threshold-bin argument starts. -/
theorem dyadicBinStart_le_dyadicBlock_mul_log
    {A : Finset ℤ} {deletionBudget steps h : ℕ}
    (hstepsCard : steps ≤ A.card)
    (hstepsBudget : steps ≤ deletionBudget) :
    dyadicBinStart A deletionBudget steps h ≤
      2 ^ (h + 1) *
        (Nat.log 2 (positiveDyadicThreshold A deletionBudget h) + 1) := by
  let crossing := dyadicBinStart A deletionBudget steps h
  let q := 2 ^ (h + 1)
  let threshold := positiveDyadicThreshold A deletionBudget h
  by_cases hcrossing : crossing = 0
  · simp [crossing, hcrossing]
  · have hcrossingPos : 0 < crossing := Nat.pos_of_ne_zero hcrossing
    let blocks := (crossing - 1) / q
    have hq : 0 < q := by
      dsimp only [q]
      positivity
    have hdivMul : blocks * q ≤ crossing - 1 := by
      dsimp only [blocks]
      exact Nat.div_mul_le_self _ _
    have hblockCross : q * blocks ≤ crossing := by
      rw [Nat.mul_comm]
      exact hdivMul.trans (Nat.sub_le _ _)
    have hpow := two_pow_le_card_sums_at_dyadicBlocks
      (A := A) (deletionBudget := deletionBudget) (steps := steps)
      (h := h) (crossing := crossing) rfl hstepsCard hstepsBudget
      blocks hblockCross
    have hindexLt : q * blocks < crossing := by
      rw [Nat.mul_comm]
      omega
    have hcardLt : (sums A (q * blocks)).card < threshold := by
      dsimp only [crossing, threshold]
      exact lt_firstCrossing hindexLt
    have hblocksLog : blocks ≤ Nat.log 2 threshold := by
      apply Nat.le_log_of_pow_le (by omega)
      exact hpow.trans hcardLt.le
    have hmodLt : (crossing - 1) % q < q := Nat.mod_lt _ hq
    have hdecomp := Nat.div_add_mod (crossing - 1) q
    have hcrossingBound : crossing ≤ q * (blocks + 1) := by
      change q * ((crossing - 1) / q) + (crossing - 1) % q =
        crossing - 1 at hdecomp
      rw [Nat.mul_succ]
      change crossing ≤ q * ((crossing - 1) / q) + q
      omega
    calc
      crossing ≤ q * (blocks + 1) := hcrossingBound
      _ ≤ q * (Nat.log 2 threshold + 1) := by gcongr
      _ = 2 ^ (h + 1) *
          (Nat.log 2 (positiveDyadicThreshold A deletionBudget h) + 1) := rfl

/-- Shifted form of the dyadic-bin estimate.  It starts the active bin
count at an arbitrary `low` level; the unaccounted low-scale part is exactly
the first crossing of the level-`low` threshold. -/
theorem steps_le_shiftedDyadicPrefix_add
    {A : Finset ℤ}
    {deletionBudget steps low terminal ratio : ℕ}
    (hlowTerminal : low < terminal)
    (hstepsCard : steps ≤ A.card)
    (hstepsBudget : steps ≤ deletionBudget)
    (hterminal : (sums A steps).card <
      positiveDyadicThreshold A deletionBudget terminal)
    (hratio : ∀ h, low ≤ h → h < terminal →
      positiveDyadicThreshold A deletionBudget (h + 1) ≤
        ratio * positiveDyadicThreshold A deletionBudget h) :
    steps ≤ dyadicBinStart A deletionBudget steps low +
      16 * ratio * 2 ^ terminal := by
  have hterminalStart :
      dyadicBinStart A deletionBudget steps terminal = steps := by
    apply firstCrossing_eq_steps_of_end_lt
    · intro i j hij hj
      exact card_sums_mono hij (hj.trans hstepsCard)
    · exact hterminal
  have hlength : ∀ h ∈ Finset.Ico low terminal,
      dyadicBinLength A deletionBudget steps h ≤
        (8 * ratio) * 2 ^ h := by
    intro h hh
    have hlow : low ≤ h := (Finset.mem_Ico.mp hh).1
    have hhigh : h < terminal := (Finset.mem_Ico.mp hh).2
    by_cases hz : dyadicBinLength A deletionBudget steps h = 0
    · simp [hz]
    · have hpos : 0 < dyadicBinLength A deletionBudget steps h :=
        Nat.pos_of_ne_zero hz
      have hrun :=
        greedy_threshold_run_length_le_of_positiveDyadicThreshold
          hpos
          ((dyadicBin_block_end_le_steps A deletionBudget steps h).trans
            hstepsCard)
          ((dyadicBin_block_end_le_steps A deletionBudget steps h).trans
            hstepsBudget)
          (hratio h hlow hhigh)
          (fun i hi ↦ dyadicBin_mem hstepsCard hi)
      calc
        dyadicBinLength A deletionBudget steps h ≤
            4 * ratio * 2 ^ (h + 1) := hrun
        _ = (8 * ratio) * 2 ^ h := by rw [pow_succ]; ring
  have hstartZeroLow :
      dyadicBinStart A deletionBudget steps 0 ≤
        dyadicBinStart A deletionBudget steps low :=
    dyadicBinStart_mono A deletionBudget steps (Nat.zero_le low)
  have hstartLowTerminal :
      dyadicBinStart A deletionBudget steps low ≤
        dyadicBinStart A deletionBudget steps terminal :=
    dyadicBinStart_mono A deletionBudget steps hlowTerminal.le
  have hshiftedSum :
      steps - dyadicBinStart A deletionBudget steps low =
        ∑ h ∈ Finset.Ico low terminal,
          dyadicBinLength A deletionBudget steps h := by
    have hsplit := Finset.sum_range_add_sum_Ico
      (fun h ↦ dyadicBinLength A deletionBudget steps h)
      hlowTerminal.le
    rw [sum_dyadicBinLength, sum_dyadicBinLength,
      hterminalStart] at hsplit
    omega
  have hsumBound :
      (∑ h ∈ Finset.Ico low terminal,
          dyadicBinLength A deletionBudget steps h) ≤
        16 * ratio * 2 ^ terminal := by
    calc
      (∑ h ∈ Finset.Ico low terminal,
          dyadicBinLength A deletionBudget steps h) ≤
          ∑ h ∈ Finset.Ico low terminal, (8 * ratio) * 2 ^ h := by
        exact Finset.sum_le_sum fun h hh ↦ hlength h hh
      _ ≤ ∑ h ∈ Finset.range terminal, (8 * ratio) * 2 ^ h := by
        apply Finset.sum_le_sum_of_subset
        intro h hh
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hh).2
      _ = (8 * ratio) * (2 ^ terminal - 1) := by
        rw [← Finset.mul_sum, sum_range_two_pow]
      _ ≤ (8 * ratio) * 2 ^ terminal :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ ≤ 16 * ratio * 2 ^ terminal := by gcongr <;> omega
  have hprefixSteps :
      dyadicBinStart A deletionBudget steps low ≤ steps :=
    dyadicBinStart_le A deletionBudget steps low
  calc
    steps = dyadicBinStart A deletionBudget steps low +
        (steps - dyadicBinStart A deletionBudget steps low) :=
      (Nat.add_sub_of_le hprefixSteps).symm
    _ ≤ dyadicBinStart A deletionBudget steps low +
        16 * ratio * 2 ^ terminal := by
      exact Nat.add_le_add_left (hshiftedSum.le.trans hsumBound) _

/-- Contrapositive crossing form of `steps_le_shiftedDyadicPrefix_add`.
If the cap is larger than the low prefix plus the shifted active-bin budget,
then the terminal threshold has already been reached. -/
theorem positiveDyadicThreshold_le_card_sums_of_shiftedPrefix_lt
    {A : Finset ℤ}
    {deletionBudget steps low terminal ratio : ℕ}
    (hlowTerminal : low < terminal)
    (hstepsCard : steps ≤ A.card)
    (hstepsBudget : steps ≤ deletionBudget)
    (hratio : ∀ h, low ≤ h → h < terminal →
      positiveDyadicThreshold A deletionBudget (h + 1) ≤
        ratio * positiveDyadicThreshold A deletionBudget h)
    (hlarge : dyadicBinStart A deletionBudget steps low +
      16 * ratio * 2 ^ terminal < steps) :
    positiveDyadicThreshold A deletionBudget terminal ≤
      (sums A steps).card := by
  by_contra hnot
  have hterminal : (sums A steps).card <
      positiveDyadicThreshold A deletionBudget terminal := by omega
  have hbound := steps_le_shiftedDyadicPrefix_add hlowTerminal hstepsCard
    hstepsBudget hterminal hratio
  omega

end Erdos186.CFP.Greedy

#print axioms
  Erdos186.CFP.Greedy.dyadicBinStart_le_dyadicBlock_mul_log
