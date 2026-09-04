/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos55.WeakScales

/-!
# The sparse family of blue windows

At a selected weak scale `J n`, every blue summand in the target range comes
either from the current blue window or from a single finite prefix containing
all earlier selected windows.  This file packages that dichotomy and the
cardinality estimate which makes the final diagonal coloring work.
-/

namespace Erdos55

open scoped BigOperators

theorem scaleProduct_mono {i j : ℕ} (hij : i ≤ j) :
    i * 2 ^ i ≤ j * 2 ^ j := by
  exact Nat.mul_le_mul hij (Nat.pow_le_pow_right (by omega) hij)

/-- Membership in at least one of the selected blue windows. -/
def selectedBlue (A : Set ℕ) (J : ℕ → ℕ) (a : ℕ) : Prop :=
  ∃ n, a ∈ blueWindow A (J n)

/-- The Boolean bit used by the final rank-and-bit coloring. -/
noncomputable def selectedBlueBit (A : Set ℕ) (J : ℕ → ℕ) (a : ℕ) : Bool :=
  by
    classical
    exact decide (selectedBlue A J a)

@[simp] theorem selectedBlueBit_eq_true {A : Set ℕ} {J : ℕ → ℕ} {a : ℕ} :
    selectedBlueBit A J a = true ↔ selectedBlue A J a := by
  simp [selectedBlueBit]

@[simp] theorem selectedBlueBit_eq_false {A : Set ℕ} {J : ℕ → ℕ} {a : ℕ} :
    selectedBlueBit A J a = false ↔ ¬selectedBlue A J a := by
  simp [selectedBlueBit]

/-- The hue-specific prefix containing all selected windows before `n`. -/
noncomputable def earlierHuePrefix (A : Set ℕ) (h s : ℕ) (J : ℕ → ℕ) :
    ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 => rankHuePrefix A h s (J n * 2 ^ J n)

/-- A dyadic-count exponent bounding the preceding prefix. -/
noncomputable def earlierExponent (A : Set ℕ) (J : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => dyadicCount A (2 * J n)

theorem rankHuePrefix_subset_rankPrefix {A : Set ℕ} (hA : A.Infinite)
    (h s N : ℕ) : rankHuePrefix A h s N ⊆ rankPrefix A N := by
  intro a ha
  rw [mem_rankHuePrefix_iff hA] at ha
  exact (mem_rankPrefix_iff hA).mpr ⟨ha.1, ha.2.1⟩

theorem card_earlierHuePrefix_le_exponent {A : Set ℕ} (hA : A.Infinite)
    (h s : ℕ) (J : ℕ → ℕ) (n : ℕ) :
    (earlierHuePrefix A h s J n).card ≤ earlierExponent A J n := by
  cases n with
  | zero => simp [earlierHuePrefix, earlierExponent]
  | succ n =>
      have hscale : J n * 2 ^ J n ≤ 2 ^ (2 * J n) := by
        have hself : J n ≤ 2 ^ J n := Nat.le_of_lt (J n).lt_two_pow_self
        calc
          J n * 2 ^ J n ≤ 2 ^ J n * 2 ^ J n := Nat.mul_le_mul_right _ hself
          _ = 2 ^ (2 * J n) := by
            rw [← pow_add]
            congr 1
            omega
      calc
        (earlierHuePrefix A h s J (n + 1)).card ≤
            (rankPrefix A (J n * 2 ^ J n)).card := by
          apply Finset.card_le_card
          exact rankHuePrefix_subset_rankPrefix hA _ _ _
        _ ≤ (rankPrefix A (2 ^ (2 * J n))).card := by
          exact Finset.card_le_card (rankPrefix_mono hA hscale)
        _ = earlierExponent A J (n + 1) := by
          simp [earlierExponent, dyadicCount]

theorem card_subsetSumValues_le_two_pow (S : Finset ℕ) :
    (subsetSumValues S).card ≤ 2 ^ S.card := by
  unfold subsetSumValues
  calc
    (S.powerset.image fun t ↦ ∑ x ∈ t, x).card ≤ S.powerset.card := Finset.card_image_le
    _ = 2 ^ S.card := Finset.card_powerset S

theorem card_subsetSumValues_earlier_le {A : Set ℕ} (hA : A.Infinite)
    (h s : ℕ) (J : ℕ → ℕ) (n : ℕ) :
    (subsetSumValues (earlierHuePrefix A h s J n)).card ≤
      2 ^ earlierExponent A J n := by
  calc
    (subsetSumValues (earlierHuePrefix A h s J n)).card ≤
        2 ^ (earlierHuePrefix A h s J n).card :=
      card_subsetSumValues_le_two_pow _
    _ ≤ 2 ^ earlierExponent A J n :=
      Nat.pow_le_pow_right (by omega) (card_earlierHuePrefix_le_exponent hA h s J n)

theorem blueHueRepresented_subset_blueRepresented
    {A : Set ℕ} {h s j : ℕ} (hs : s < h) :
    blueHueRepresented A h s j ⊆ blueRepresented A h j := by
  intro x hx
  unfold blueRepresented
  exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_range.mpr hs, hx⟩

/-- Current-window subset sums, with the empty sum restored. -/
noncomputable def currentBlueOptions (A : Set ℕ) (h s j : ℕ) : Finset ℕ :=
  insert 0 (blueHueRepresented A h s j)

theorem card_currentBlueOptions_le {A : Set ℕ} {h s j : ℕ}
    (hs : s < h) (hweak : ¬BlueStrong A h j) :
    (currentBlueOptions A h s j).card ≤ 2 ^ j := by
  have hhue : (blueHueRepresented A h s j).card ≤
      (blueRepresented A h j).card :=
    Finset.card_le_card (blueHueRepresented_subset_blueRepresented hs)
  have hglobal : (blueRepresented A h j).card < 2 ^ j := by
    simpa [BlueStrong] using hweak
  calc
    (currentBlueOptions A h s j).card ≤
        (blueHueRepresented A h s j).card + 1 := by
      simpa [currentBlueOptions] using
        (Finset.card_insert_le 0 (blueHueRepresented A h s j))
    _ ≤ 2 ^ j := by omega

/-- All values which the counting argument permits for one blue hue. -/
noncomputable def blueHuePossible (A : Set ℕ) (h s : ℕ) (J : ℕ → ℕ)
    (n : ℕ) : Finset ℕ :=
  Finset.image₂ (fun x y : ℕ ↦ x + y)
    (subsetSumValues (earlierHuePrefix A h s J n))
    (currentBlueOptions A h s (J n))

theorem card_blueHuePossible_le {A : Set ℕ} (hA : A.Infinite)
    {h s : ℕ} (hs : s < h) {J : ℕ → ℕ} {n : ℕ}
    (hweak : ¬BlueStrong A h (J n)) :
    (blueHuePossible A h s J n).card ≤
      2 ^ earlierExponent A J n * 2 ^ J n := by
  calc
    (blueHuePossible A h s J n).card ≤
        (subsetSumValues (earlierHuePrefix A h s J n)).card *
          (currentBlueOptions A h s (J n)).card := by
      simpa [blueHuePossible] using
        (Finset.card_image₂_le (fun x y : ℕ ↦ x + y)
          (subsetSumValues (earlierHuePrefix A h s J n))
          (currentBlueOptions A h s (J n)))
    _ ≤ 2 ^ earlierExponent A J n * 2 ^ J n :=
      Nat.mul_le_mul (card_subsetSumValues_earlier_le hA h s J n)
        (card_currentBlueOptions_le hs hweak)

/-- Union of the possible blue values over all hues. -/
noncomputable def bluePossible (A : Set ℕ) (h : ℕ) (J : ℕ → ℕ)
    (n : ℕ) : Finset ℕ :=
  (Finset.range h).biUnion fun s ↦ blueHuePossible A h s J n

theorem card_bluePossible_le {A : Set ℕ} (hA : A.Infinite)
    {h : ℕ} {J : ℕ → ℕ} {n : ℕ}
    (hweak : ¬BlueStrong A h (J n)) :
    (bluePossible A h J n).card ≤
      h * (2 ^ earlierExponent A J n * 2 ^ J n) := by
  classical
  calc
    (bluePossible A h J n).card ≤
        ∑ s ∈ Finset.range h, (blueHuePossible A h s J n).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ Finset.range h,
        (2 ^ earlierExponent A J n * 2 ^ J n) := by
      apply Finset.sum_le_sum
      intro s hs
      exact card_blueHuePossible_le hA (Finset.mem_range.mp hs) hweak
    _ = h * (2 ^ earlierExponent A J n * 2 ^ J n) := by simp

theorem sparseWeakSequence_size_gap {P : ℕ → Prop}
    (hunbounded : ∀ b, ∃ j, b < j ∧ P j) (A : Set ℕ) (h n : ℕ) :
    16 * h * 2 ^ earlierExponent A (sparseWeakSequence hunbounded A h) n <
      sparseWeakSequence hunbounded A h n := by
  cases n with
  | zero =>
      simpa [earlierExponent] using sparseWeakSequence_zero_gt hunbounded A h
  | succ n =>
      have hnext := sparseWeakSequence_succ_gt hunbounded A h n
      exact (le_max_right
        (sparseWeakSequence hunbounded A h n *
          2 ^ sparseWeakSequence hunbounded A h n)
        (16 * h * 2 ^ dyadicCount A
          (2 * sparseWeakSequence hunbounded A h n))).trans_lt (by
            simpa [earlierExponent, sparseBound] using hnext)

theorem card_bluePossible_mul_sixteen_lt {A : Set ℕ} (hA : A.Infinite)
    {h : ℕ} {P : ℕ → Prop}
    (hunbounded : ∀ b, ∃ j, b < j ∧ P j) {n : ℕ}
    (hweak : ¬BlueStrong A h (sparseWeakSequence hunbounded A h n)) :
    16 * (bluePossible A h (sparseWeakSequence hunbounded A h) n).card <
      sparseWeakSequence hunbounded A h n *
        2 ^ sparseWeakSequence hunbounded A h n := by
  let J := sparseWeakSequence hunbounded A h
  have hcard := card_bluePossible_le hA (J := J) (n := n) hweak
  have hgap := sparseWeakSequence_size_gap hunbounded A h n
  have hmul := (Nat.mul_lt_mul_right (by positivity : 0 < 2 ^ J n)).mpr hgap
  calc
    16 * (bluePossible A h J n).card ≤
        16 * (h * (2 ^ earlierExponent A J n * 2 ^ J n)) :=
      Nat.mul_le_mul_left 16 hcard
    _ = (16 * h * 2 ^ earlierExponent A J n) * 2 ^ J n := by ring
    _ < J n * 2 ^ J n := hmul

/-- The interval from which one integer will be omitted at each weak scale. -/
noncomputable def targetInterval (j : ℕ) : Finset ℕ :=
  Finset.Ioc (redThreshold j) (j * 2 ^ j)

theorem targetInterval_card_eq {j : ℕ} (hj : 8 ≤ j) :
    (targetInterval j).card = 2 ^ (j - 1) * (j - 8) := by
  have hjpos : 0 < j := by omega
  have hp : 2 ^ j = 2 * 2 ^ (j - 1) := by
    conv_lhs => rw [show j = (j - 1) + 1 by omega, pow_succ]
    omega
  have hcoef : j + 8 ≤ 2 * j := by omega
  unfold targetInterval redThreshold
  rw [Nat.card_Ioc]
  rw [hp]
  calc
    j * (2 * 2 ^ (j - 1)) - 2 ^ (j - 1) * (j + 8) =
        2 ^ (j - 1) * (2 * j) - 2 ^ (j - 1) * (j + 8) := by ring_nf
    _ = 2 ^ (j - 1) * (2 * j - (j + 8)) := by
      rw [Nat.mul_sub_left_distrib]
    _ = 2 ^ (j - 1) * (j - 8) := by
      congr 1
      omega

theorem scale_lt_sixteen_mul_target_card {j : ℕ} (hj : 16 < j) :
    j * 2 ^ j < 16 * (targetInterval j).card := by
  have hp : 2 ^ j = 2 * 2 ^ (j - 1) := by
    conv_lhs => rw [show j = (j - 1) + 1 by omega, pow_succ]
    omega
  rw [targetInterval_card_eq (by omega), hp]
  have hcoef : 2 * j < 16 * (j - 8) := by omega
  have hmul := (Nat.mul_lt_mul_left (by positivity : 0 < 2 ^ (j - 1))).mpr hcoef
  simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul

end Erdos55
