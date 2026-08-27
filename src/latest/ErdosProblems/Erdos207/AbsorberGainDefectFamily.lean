/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberGainDefectWeight
import ErdosProblems.Erdos207.GainDefectFamilyUnion
import ErdosProblems.Erdos207.AbsorberCommonThreatFamily

/-! # Full second-family fourth-moment extension bound -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def absorberGainDefectWeightBound
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (B : TripleSystemOn V) : ℝ≥0 :=
  (q + 1 : ℝ≥0) * gainDefectWeightBound q B

theorem absorberGainDefect_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (q r z : ℕ) (B : TripleSystemOn V) (T : TripleOn V)
    (hr4 : 4 ≤ r) (hr : r ≤ q) (hz : 1 ≤ z) :
    HasExtensionBound (fun w : GainDefectWitness
      (absorberInducedConfigurationsOn q r B) (absorberNontrivialInducedFamily q B) T z ↦ w.remainder)
      (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹)
      (absorberGainDefectWeightBound q B * (Fintype.card V + 1 : ℝ≥0) ^ (z - 1)) := by
  have h := gainDefect_secondUnion_hasExtensionBound (absorberInducedConfigurationsOn q r B)
    (fun s : (Icc 4 q : Finset ℕ) ↦ absorberInducedConfigurationsOn q s.1 B) T z
    (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (fun _ ↦ gainDefectWeightBound q B * (Fintype.card V + 1 : ℝ≥0) ^ (z - 1))
    (fun s ↦ gainDefect_absorberInduced_hasExtensionBound q r s.1 z B T hr4 hr
      (mem_Icc.mp s.2).2 hz)
  intro H
  refine (h H).trans ?_
  have hc : (Icc 4 q).card ≤ q + 1 := by simp only [Nat.card_Icc]; omega
  have hc' : ((Icc 4 q).card : ℝ≥0) ≤ q + 1 := by exact_mod_cast hc
  simp only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
  calc
    _ ≤ (q + 1 : ℝ≥0) * (gainDefectWeightBound q B * (Fintype.card V + 1 : ℝ≥0) ^ (z - 1)) :=
      mul_le_mul_of_nonneg_right hc' zero_le
    _ = _ := by rw [absorberGainDefectWeightBound]; ring

theorem absorberGainDefect_remainder_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q r z : ℕ) (B : TripleSystemOn V) (T : TripleOn V) (hr : r ≤ q)
    (w : GainDefectWitness (absorberInducedConfigurationsOn q r B)
      (absorberNontrivialInducedFamily q B) T z) : w.remainder.card ≤ 2 * q := by
  obtain ⟨s, _, hs, hsecond⟩ := mem_absorberNontrivialInducedFamily.mp w.second_mem
  rw [w.remainder_card, absorberInducedConfigurationsOn_fixed_card _ w.first_mem,
    absorberInducedConfigurationsOn_fixed_card _ hsecond]
  omega

end

end Erdos207
