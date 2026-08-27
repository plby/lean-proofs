/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CommonThreatExceptionalWeight

/-! # The complete uniform third nibble-moment weight bound -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def commonThreatExceptionalWeightBound
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (B : TripleSystemOn V) : ℝ≥0 :=
  (2 : ℝ≥0) ^ q *
    (2 * pairExactBankExtensionCoefficient q B + 2 ^ (q ^ 3) * (q + 1) : ℕ)

theorem commonThreatExceptionalWeight_absorberInduced_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q r s : ℕ) (B : TripleSystemOn V) (T T' : TripleOn V) (H : TripleSystemOn V)
    (hr4 : 4 ≤ r) (hr : r ≤ q) :
    commonThreatExceptionalWeight (absorberInducedConfigurationsOn q r B)
      (absorberInducedConfigurationsOn q s B) T T' H (Fintype.card V + 1 : ℝ≥0)⁻¹ ≤
      commonThreatExceptionalWeightBound q B := by
  by_cases hrs : r = s
  · subst s
    refine (commonThreatExceptionalWeight_le_omissionWeight
      (absorberInducedConfigurationsOn q r B) T T' H (r - 2)
      (Fintype.card V + 1 : ℝ≥0)⁻¹ absorberInducedConfigurationsOn_fixed_card).trans ?_
    have hw := equalRemainderOmissionWeight_absorberInduced_le q r 1 B T T' hr4 le_rfl
    simp only [Nat.sub_self, pow_zero, mul_one] at hw
    refine hw.trans ?_
    have hc : 2 * pairExactBankExtensionCoefficient q B + 2 ^ (r ^ 3) * (r + 1) ≤
        2 * pairExactBankExtensionCoefficient q B + 2 ^ (q ^ 3) * (q + 1) := by
      apply Nat.add_le_add_left
      apply Nat.mul_le_mul
      · exact pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ)) (pow_le_pow_left₀ zero_le hr 3)
      · omega
    have hc' : ((2 * pairExactBankExtensionCoefficient q B + 2 ^ (r ^ 3) * (r + 1) : ℕ) : ℝ≥0) ≤
        (2 * pairExactBankExtensionCoefficient q B + 2 ^ (q ^ 3) * (q + 1) : ℕ) := by
      exact_mod_cast hc
    exact mul_le_mul (pow_le_pow_right' (by norm_num : (1 : ℝ≥0) ≤ 2) (by omega))
      hc' zero_le zero_le
  · rw [commonThreatExceptionalWeight_eq_zero_of_orders_ne
      (absorberInducedConfigurationsOn q r B) (absorberInducedConfigurationsOn q s B)
      T T' H r s _ absorberInducedConfigurationsOn_fixed_card
      absorberInducedConfigurationsOn_fixed_card hrs]
    exact zero_le

def commonThreatWeightBound
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (B : TripleSystemOn V) : ℝ≥0 :=
  2 * commonThreatGoodWeightBound q B + commonThreatExceptionalWeightBound q B

theorem extensionWeight_commonThreat_absorberInduced_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q r s : ℕ) (B : TripleSystemOn V) (T T' : TripleOn V) (H : TripleSystemOn V)
    (hr4 : 4 ≤ r) (hr : r ≤ q) (hs : s ≤ q) :
    extensionWeight (fun w : CommonThreatWitness
      (absorberInducedConfigurationsOn q r B) (absorberInducedConfigurationsOn q s B) T T' ↦ w.remainder)
      (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) H ≤ commonThreatWeightBound q B := by
  refine (extensionWeight_commonThreat_le_split
    (absorberInducedConfigurationsOn q r B) (absorberInducedConfigurationsOn q s B)
    T T' H r s _ absorberInducedConfigurationsOn_fixed_card
    absorberInducedConfigurationsOn_fixed_card).trans ?_
  calc
    _ ≤ (commonThreatGoodWeightBound q B + commonThreatGoodWeightBound q B) +
        commonThreatExceptionalWeightBound q B :=
      add_le_add (add_le_add
        (commonThreatGoodWeight_absorberInduced_le q r s B T T' H hr hs)
        (commonThreatGoodWeight_absorberInduced_le q s r B T' T H hs hr))
        (commonThreatExceptionalWeight_absorberInduced_le q r s B T T' H hr4 hr)
    _ = _ := by rw [commonThreatWeightBound]; ring

theorem commonThreat_absorberInduced_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (q r s : ℕ) (B : TripleSystemOn V) (T T' : TripleOn V)
    (hr4 : 4 ≤ r) (hr : r ≤ q) (hs : s ≤ q) :
    HasExtensionBound (fun w : CommonThreatWitness
      (absorberInducedConfigurationsOn q r B) (absorberInducedConfigurationsOn q s B) T T' ↦ w.remainder)
      (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) (commonThreatWeightBound q B) := by
  intro H
  exact extensionWeight_commonThreat_absorberInduced_le q r s B T T' H hr4 hr hs

end

end Erdos207
