/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos55.StrongScales

/-!
# Weak scales and a sparse weak subsequence

Since fewer than `1/8` of the scales are red-strong and fewer than `3/4`
are blue-strong, weak scales have positive lower density.  We only need the
consequence that they are unbounded.  The selected subsequence is made even
sparser than in CFP: the next index dominates both the preceding blue window
and the number of all subset choices from the preceding prefix.
-/

namespace Erdos55

def WeakScale (A : Set ℕ) (h j : ℕ) : Prop :=
  ¬RedStrong A h j ∧ ¬BlueStrong A h j

noncomputable def weakScales (A : Set ℕ) (h i : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 i).filter (WeakScale A h)

theorem eventually_weakScales_card_gt_eighth_of_quadratic
    {A : Set ℕ} (hA : A.Infinite) (hApos : IsPositiveNatSet A)
    {h K : ℕ} (hh : 0 < h) (hK : 1 ≤ K) {β : ℝ} (hβ : 0 ≤ β)
    (hβsmall : 8192 * β ≤ h)
    (hquad : ∀ k, K ≤ k →
      (dyadicCount A k : ℝ) ≤ β * (k : ℝ) ^ 2) :
    ∃ I : ℕ, K ≤ I ∧ ∀ i, I ≤ i →
      (i : ℝ) / 8 < ((weakScales A h i).card : ℝ) := by
  classical
  have hredSmall : 128 * β ≤ (h : ℝ) := by nlinarith
  obtain ⟨IR, hKIR, hred⟩ :=
    eventually_redStrong_card_lt_eighth_of_quadratic
      hA hApos hh hK hβ hredSmall hquad
  obtain ⟨IB, hKIB, hblue⟩ :=
    eventually_blueStrong_card_lt_three_quarters_of_quadratic
      hA hApos hh hK hβsmall hquad
  refine ⟨max IR IB, hKIR.trans (le_max_left _ _), ?_⟩
  intro i hi
  have hri := hred i ((le_max_left IR IB).trans hi)
  have hbi := hblue i ((le_max_right IR IB).trans hi)
  let R := redStrongScales A h i
  let B := blueStrongScales A h i
  let W := weakScales A h i
  have hR : R ⊆ Finset.Icc 1 i := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hB : B ⊆ Finset.Icc 1 i := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hU : R ∪ B ⊆ Finset.Icc 1 i := Finset.union_subset hR hB
  have hWeq : W = Finset.Icc 1 i \ (R ∪ B) := by
    ext j
    simp only [W, weakScales, Finset.mem_filter, WeakScale, Finset.mem_Icc,
      Finset.mem_sdiff, Finset.mem_union, R, redStrongScales, B, blueStrongScales]
    tauto
  have hpart : W.card + (R ∪ B).card = (Finset.Icc 1 i).card := by
    rw [hWeq, Finset.card_sdiff_add_card_eq_card hU]
  have hunion : (R ∪ B).card ≤ R.card + B.card := Finset.card_union_le _ _
  have hIcc : (Finset.Icc 1 i).card = i := by simp
  have hpartR : (W.card : ℝ) + ((R ∪ B).card : ℝ) = i := by
    exact_mod_cast hpart.trans hIcc
  have hunionR : ((R ∪ B).card : ℝ) ≤ R.card + B.card := by
    exact_mod_cast hunion
  change (i : ℝ) / 8 < (W.card : ℝ)
  nlinarith

theorem weakScale_unbounded_of_quadratic
    {A : Set ℕ} (hA : A.Infinite) (hApos : IsPositiveNatSet A)
    {h K : ℕ} (hh : 0 < h) (hK : 1 ≤ K) {β : ℝ} (hβ : 0 ≤ β)
    (hβsmall : 8192 * β ≤ h)
    (hquad : ∀ k, K ≤ k →
      (dyadicCount A k : ℝ) ≤ β * (k : ℝ) ^ 2) :
    ∀ b : ℕ, ∃ j : ℕ, b < j ∧ WeakScale A h j := by
  classical
  obtain ⟨I, hKI, hweak⟩ :=
    eventually_weakScales_card_gt_eighth_of_quadratic
      hA hApos hh hK hβ hβsmall hquad
  intro b
  let i := max I (8 * (b + 1))
  have hIi : I ≤ i := le_max_left _ _
  have hib : 8 * (b + 1) ≤ i := le_max_right _ _
  have hcard := hweak i hIi
  have hbcard : b < (weakScales A h i).card := by
    have hibR : (8 : ℝ) * (b + 1) ≤ i := by exact_mod_cast hib
    have hbR : (b : ℝ) < (weakScales A h i).card := by nlinarith
    exact_mod_cast hbR
  by_contra hnone
  have hnone' : ∀ j, b < j → ¬WeakScale A h j := by
    intro j hbj hj
    exact hnone ⟨j, hbj, hj⟩
  have hsub : weakScales A h i ⊆ Finset.Icc 1 b := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    have hjpos := (Finset.mem_Icc.mp hj'.1).1
    have hjle : j ≤ b := by
      by_contra hbj
      exact (hnone' j (Nat.lt_of_not_ge hbj)) hj'.2
    exact Finset.mem_Icc.mpr ⟨hjpos, hjle⟩
  have hle : (weakScales A h i).card ≤ b := by
    calc
      (weakScales A h i).card ≤ (Finset.Icc 1 b).card := Finset.card_le_card hsub
      _ ≤ b := by simp
  omega

noncomputable def chooseAbove {P : ℕ → Prop}
    (hunbounded : ∀ b, ∃ j, b < j ∧ P j) (b : ℕ) : ℕ := by
  classical
  exact Nat.find (hunbounded b)

theorem chooseAbove_spec {P : ℕ → Prop}
    (hunbounded : ∀ b, ∃ j, b < j ∧ P j) (b : ℕ) :
    b < chooseAbove hunbounded b ∧ P (chooseAbove hunbounded b) :=
  by
    classical
    exact Nat.find_spec (hunbounded b)

/-- The size that the next selected weak scale must dominate. -/
noncomputable def sparseBound (A : Set ℕ) (h j : ℕ) : ℕ :=
  max (j * 2 ^ j) (16 * h * 2 ^ dyadicCount A (2 * j))

noncomputable def sparseWeakSequence {P : ℕ → Prop}
    (hunbounded : ∀ b, ∃ j, b < j ∧ P j) (A : Set ℕ) (h : ℕ) : ℕ → ℕ
  | 0 => chooseAbove hunbounded (16 * h)
  | n + 1 => chooseAbove hunbounded
      (sparseBound A h (sparseWeakSequence hunbounded A h n))

theorem sparseWeakSequence_mem {P : ℕ → Prop}
    (hunbounded : ∀ b, ∃ j, b < j ∧ P j) (A : Set ℕ) (h n : ℕ) :
    P (sparseWeakSequence hunbounded A h n) := by
  cases n with
  | zero => exact (chooseAbove_spec hunbounded (16 * h)).2
  | succ n =>
      exact (chooseAbove_spec hunbounded
        (sparseBound A h (sparseWeakSequence hunbounded A h n))).2

theorem sparseWeakSequence_zero_gt {P : ℕ → Prop}
    (hunbounded : ∀ b, ∃ j, b < j ∧ P j) (A : Set ℕ) (h : ℕ) :
    16 * h < sparseWeakSequence hunbounded A h 0 :=
  (chooseAbove_spec hunbounded (16 * h)).1

theorem sparseWeakSequence_succ_gt {P : ℕ → Prop}
    (hunbounded : ∀ b, ∃ j, b < j ∧ P j) (A : Set ℕ) (h n : ℕ) :
    sparseBound A h (sparseWeakSequence hunbounded A h n) <
      sparseWeakSequence hunbounded A h (n + 1) :=
  (chooseAbove_spec hunbounded
    (sparseBound A h (sparseWeakSequence hunbounded A h n))).1

theorem sparseWeakSequence_strictMono {P : ℕ → Prop}
    (hunbounded : ∀ b, ∃ j, b < j ∧ P j) (A : Set ℕ) (h : ℕ) :
    StrictMono (sparseWeakSequence hunbounded A h) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hnext := sparseWeakSequence_succ_gt hunbounded A h n
  calc
    sparseWeakSequence hunbounded A h n ≤
        sparseWeakSequence hunbounded A h n *
          2 ^ sparseWeakSequence hunbounded A h n := by
      exact Nat.le_mul_of_pos_right _ (by positivity)
    _ ≤ sparseBound A h (sparseWeakSequence hunbounded A h n) := le_max_left _ _
    _ < sparseWeakSequence hunbounded A h (n + 1) := hnext

end Erdos55
