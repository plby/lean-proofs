/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceGainReverseClass
import ErdosProblems.Erdos207.SourceGainForwardBound

/-! # Reverse gain exposure pays for both source orders with the same power -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem sourceGainReverseClass_good_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell q r s a b : ℕ}
    {W : Vortex V ell} {F G : ForbiddenFamilyOn V} {y z y' z' : ℝ≥0}
    (hF : SourceVortexWellSpread W r F y z) (hG : SourceVortexWellSpread W s G y' z')
    (hr : r ≤ q) (hs : s ≤ q) (ha : 1 ≤ a) (T : TripleOn V) (H Q : TripleSystemOn V)
    (hbudget : s + 4 ≤ vortexRootExponent r b + vortexRootExponent s Q.card)
    (w : ℝ≥0) (hw : 1 ≤ w) :
    ∑ u : sourceGainReverseClass W F G T a H Q b,
      setWeight (vortexTripleWeight W w) (u.1.remainder \ H) ≤
        sourceCommonClassCoefficient ell q w z' z * (W.terminalSize : ℝ≥0) ^ (a - 1) := by
  classical
  by_cases hne : (sourceGainReverseClass W F G T a H Q b).Nonempty
  · obtain ⟨u, hu⟩ := hne
    have hd := (mem_filter.mp (mem_filter.mp hu).1).2
    have hQ : Q.Nonempty := by
      obtain ⟨U, hU⟩ := hd.2.1.2.2
      rw [← hd.2.2.1]
      exact ⟨U, mem_union_left _ hU⟩
    have hQcard : Q.card ≤ s - 2 := by
      rw [← hd.2.2.1, ← (hG.uniform u.second u.second_mem).1]
      exact card_le_card (u.reverseSecondRoot_subset H hd.1 hd.2.1)
    let f := r - 2 - (a + 1)
    have hf : f ≤ 2 * q := by dsimp only [f]; omega
    have hbudget' : s + 4 ≤ vortexRootExponent r u.reverseFirstRoot.card +
        vortexRootExponent s (u.reverseSecondRoot H).card := by
      simpa only [hd.2.2.1, hd.2.2.2] using hbudget
    have hexp : (s - vortexRootExponent s Q.card) + (r - vortexRootExponent r b) ≤ f + (a - 1) := by
      have h := u.reverse_exponents_le_remainder_add H hd.1 hd.2.1 ha r s
        (hF.uniform u.first u.first_mem).1 (hG.uniform u.second u.second_mem).1 hbudget'
      rw [hd.2.2.1, hd.2.2.2, u.remainder_sdiff_eq_left_of_forwardExceptional H hd.2.1,
        u.leftRemainder_card, (hF.uniform u.first u.first_mem).1] at h
      dsimp only [f]
      omega
    let C : ℝ≥0 := (((f + 1) ^ (2 * ell + 1) : ℕ) : ℝ≥0) *
      (2 : ℝ≥0) ^ (2 * (s - 2) + (r - 2) + 1) * z' * z * w ^ f
    have hn : (1 : ℝ≥0) ≤ W.terminalSize := by exact_mod_cast hF.terminal_nonempty
    exact (sourceGainReverseClass_weight_le hF hG T H Q hQ hQcard w).trans
      ((source_weight_power_ratio_le (W.terminalSize : ℝ≥0) C _ f (a - 1) hn hexp).trans
        (mul_le_mul_of_nonneg_right (source_two_family_coefficient_le ell q s r 1 f
          hs hr (by omega) hf w z' z hw) zero_le))
  · have : IsEmpty (sourceGainReverseClass W F G T a H Q b) := ⟨fun u ↦ hne ⟨u.1, u.2⟩⟩
    simp only [Fintype.sum_empty, zero_le]

end

end Erdos207
