/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GainDefectWeightSplit
import ErdosProblems.Erdos207.AbsorberCommonThreatWeight

/-! # The complete fixed-order uniform fourth nibble-moment weight bound -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem gainDefectExceptionalWeight_absorberInduced_uniform_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q r s z : ℕ) (B : TripleSystemOn V) (T : TripleOn V) (H : TripleSystemOn V)
    (hr4 : 4 ≤ r) (hr : r ≤ q) (hz : 1 ≤ z) :
    gainDefectExceptionalWeight (absorberInducedConfigurationsOn q r B)
      (absorberInducedConfigurationsOn q s B) T z H (Fintype.card V + 1 : ℝ≥0)⁻¹ ≤
      commonThreatExceptionalWeightBound q B * (Fintype.card V + 1 : ℝ≥0) ^ (z - 1) := by
  by_cases hrs : r = s
  · subst s
    refine (gainDefectExceptionalWeight_absorberInduced_le q r z B T H hr4 hz).trans ?_
    have hc : 2 * pairExactBankExtensionCoefficient q B + 2 ^ (r ^ 3) * (r + 1) ≤
        2 * pairExactBankExtensionCoefficient q B + 2 ^ (q ^ 3) * (q + 1) := by
      apply Nat.add_le_add_left
      apply Nat.mul_le_mul
      · exact pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ)) (pow_le_pow_left₀ zero_le hr 3)
      · omega
    have hc' : ((2 * pairExactBankExtensionCoefficient q B + 2 ^ (r ^ 3) * (r + 1) : ℕ) : ℝ≥0) ≤
        (2 * pairExactBankExtensionCoefficient q B + 2 ^ (q ^ 3) * (q + 1) : ℕ) := by
      exact_mod_cast hc
    apply mul_le_mul_of_nonneg_right _ zero_le
    exact mul_le_mul (pow_le_pow_right' (by norm_num : (1 : ℝ≥0) ≤ 2) (by omega))
      hc' zero_le zero_le
  · rw [gainDefectExceptionalWeight_eq_zero_of_orders_ne
      (absorberInducedConfigurationsOn q r B) (absorberInducedConfigurationsOn q s B)
      T z r s H _ absorberInducedConfigurationsOn_fixed_card
      absorberInducedConfigurationsOn_fixed_card hrs]
    exact zero_le

def gainDefectWeightBound
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (B : TripleSystemOn V) : ℝ≥0 :=
  gainDefectGoodWeightBound q B + gainDefectReverseGoodWeightBound q B +
    commonThreatExceptionalWeightBound q B

theorem extensionWeight_gainDefect_absorberInduced_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q r s z : ℕ) (B : TripleSystemOn V) (T : TripleOn V) (H : TripleSystemOn V)
    (hr4 : 4 ≤ r) (hr : r ≤ q) (hs : s ≤ q) (hz : 1 ≤ z) :
    extensionWeight (fun w : GainDefectWitness
      (absorberInducedConfigurationsOn q r B) (absorberInducedConfigurationsOn q s B) T z ↦ w.remainder)
      (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) H ≤
        gainDefectWeightBound q B * (Fintype.card V + 1 : ℝ≥0) ^ (z - 1) := by
  refine (extensionWeight_gainDefect_le_split
    (absorberInducedConfigurationsOn q r B) (absorberInducedConfigurationsOn q s B)
    T z H r s _ hz absorberInducedConfigurationsOn_fixed_card
    absorberInducedConfigurationsOn_fixed_card).trans ?_
  calc
    _ ≤ (gainDefectGoodWeightBound q B * (Fintype.card V + 1 : ℝ≥0) ^ (z - 1) +
        gainDefectReverseGoodWeightBound q B * (Fintype.card V + 1 : ℝ≥0) ^ (z - 1)) +
        commonThreatExceptionalWeightBound q B * (Fintype.card V + 1 : ℝ≥0) ^ (z - 1) :=
      add_le_add (add_le_add
        (gainDefectGoodWeight_absorberInduced_le q r s z B T H hr hs hz)
        (gainDefectReverseGoodWeight_absorberInduced_le q r s z B T H hr hs hz))
        (gainDefectExceptionalWeight_absorberInduced_uniform_le q r s z B T H hr4 hr hz)
    _ = _ := by rw [gainDefectWeightBound]; ring

theorem gainDefect_absorberInduced_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (q r s z : ℕ) (B : TripleSystemOn V) (T : TripleOn V)
    (hr4 : 4 ≤ r) (hr : r ≤ q) (hs : s ≤ q) (hz : 1 ≤ z) :
    HasExtensionBound (fun w : GainDefectWitness
      (absorberInducedConfigurationsOn q r B) (absorberInducedConfigurationsOn q s B) T z ↦ w.remainder)
      (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹)
      (gainDefectWeightBound q B * (Fintype.card V + 1 : ℝ≥0) ^ (z - 1)) := by
  intro H
  exact extensionWeight_gainDefect_absorberInduced_le q r s z B T H hr4 hr hs hz

end

end Erdos207
