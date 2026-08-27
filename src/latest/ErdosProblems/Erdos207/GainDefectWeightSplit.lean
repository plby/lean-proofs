/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GainDefectGoodWeight
import ErdosProblems.Erdos207.GainDefectReverseGoodWeight
import ErdosProblems.Erdos207.GainDefectExceptionalWeight

/-! # The full fourth-moment extension weight splits into three proved classes -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem extensionWeight_gainDefect_le_split
    {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z : ℕ) (H : Finset W) (r s : ℕ) (p : ℝ≥0)
    (hz : 1 ≤ z) (hF : ∀ E ∈ F, E.card = r - 2) (hG : ∀ E ∈ G, E.card = s - 2) :
    extensionWeight (fun w : GainDefectWitness F G T z ↦ w.remainder) (fun _ ↦ p) H ≤
      gainDefectGoodWeight F G T z H r s p + gainDefectReverseGoodWeight F G T z H r s p +
        gainDefectExceptionalWeight F G T z H p := by
  classical
  simp only [extensionWeight, setWeight, prod_const, gainDefectGoodWeight,
    gainDefectReverseGoodWeight, gainDefectExceptionalWeight, gainDefectExceptionalClass, sum_filter]
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro w _
  by_cases hH : H ⊆ w.remainder
  · simp only [hH, if_true, true_and]
    rcases w.exposure_three_way_split H hH hz r s
      (hF w.first w.first_mem) (hG w.second w.second_mem) with h | h | h
    · have hg : (w.exposureCode H).IsGood H r s := h
      rw [if_pos hg]
      exact (le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le)
    · rw [if_pos h]
      exact (le_add_of_nonneg_left zero_le).trans (le_add_of_nonneg_right zero_le)
    · have he : w.ForwardExceptional H ∧ H.card = 1 ∧ T ∉ w.second ∧
          w.second \ H = w.first.erase T := ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩
      rw [if_pos he]
      exact le_add_of_nonneg_left zero_le
  · simp only [hH, if_false, false_and]
    exact zero_le

end

end Erdos207
