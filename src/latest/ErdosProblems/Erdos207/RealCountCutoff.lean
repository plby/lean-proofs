/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RandomConfigurationCountTails

/-! # Integer cutoffs for strict real-valued count failures -/

namespace Erdos207

open scoped NNReal

noncomputable section

def strictCountCutoff (a : ℝ≥0) : ℕ := ⌊(a : ℝ)⌋₊ + 1

theorem lt_strictCountCutoff (a : ℝ≥0) : (a : ℝ) < strictCountCutoff a := by
  simpa only [strictCountCutoff, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (a : ℝ)

theorem natCast_gt_iff_strictCountCutoff_le (a : ℝ≥0) (n : ℕ) :
    a < (n : ℝ≥0) ↔ strictCountCutoff a ≤ n := by
  have hfloor : ⌊(a : ℝ)⌋₊ < n ↔ (a : ℝ) < n := Nat.floor_lt a.coe_nonneg
  constructor
  · intro h
    have hR : (a : ℝ) < n := by exact_mod_cast h
    exact Nat.succ_le_of_lt (hfloor.mpr hR)
  · intro h
    have hR : (a : ℝ) < n := hfloor.mp (Nat.lt_of_succ_le h)
    exact_mod_cast hR

theorem FiniteLaw.probability_natCast_gt_le_dyadic
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : FiniteLaw Ω) (count : Ω → ℕ) (mu a : ℝ≥0) (s : ℕ)
    (htail : ∀ k : ℕ, 4 * (mu : ℝ) ≤ k → 4 * s ≤ k →
      L.probability (fun ω ↦ k ≤ count ω) ≤ ((2 : ℝ≥0) ^ s)⁻¹)
    (hmean : 4 * mu ≤ a) (hsize : (4 * s : ℕ) ≤ (a : ℝ≥0)) :
    L.probability (fun ω ↦ a < (count ω : ℝ≥0)) ≤ ((2 : ℝ≥0) ^ s)⁻¹ := by
  have hcut := lt_strictCountCutoff a
  have hmeanR : 4 * (mu : ℝ) ≤ a := by exact_mod_cast hmean
  have hsizeR : ((4 * s : ℕ) : ℝ) ≤ a := by exact_mod_cast hsize
  have hsizeK : 4 * s ≤ strictCountCutoff a := by
    exact_mod_cast hsizeR.trans hcut.le
  have heq : (fun ω ↦ a < (count ω : ℝ≥0)) = (fun ω ↦ strictCountCutoff a ≤ count ω) := by
    funext ω
    exact propext (natCast_gt_iff_strictCountCutoff_le a (count ω))
  rw [heq]
  exact htail (strictCountCutoff a) (hmeanR.trans hcut.le) hsizeK

theorem independentBits_probability_filter_card_gt_le_dyadic
    {I : Type*} [Fintype I] [DecidableEq I] (S : Finset I)
    (p a : ℝ≥0) (hp : p ≤ 1) (s : ℕ)
    (hmean : 4 * (p * S.card) ≤ a) (hsize : (4 * s : ℕ) ≤ (a : ℝ≥0)) :
    (FiniteLaw.independentBits (fun _ : I ↦ p) (fun _ ↦ hp)).probability
      (fun ω ↦ a < ((S.filter fun x ↦ ω x = true).card : ℝ≥0)) ≤ ((2 : ℝ≥0) ^ s)⁻¹ := by
  apply FiniteLaw.probability_natCast_gt_le_dyadic _ _ (p * S.card) a s ?_ hmean hsize
  intro k hk hs
  exact independentBits_probability_filter_card_ge_le_dyadic S p hp k s
    (by simpa only [NNReal.coe_mul, NNReal.coe_natCast] using hk) hs

end

end Erdos207
