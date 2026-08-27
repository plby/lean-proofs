/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceGainForwardClass
import ErdosProblems.Erdos207.SourceCommonExposureBound
import ErdosProblems.Erdos207.GainDefectExponentBudget

/-! # The forward gain weight retains exactly the omitted-size power -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem source_weight_power_ratio_le (n C : ℝ≥0) (e f d : ℕ) (hn : 1 ≤ n) (he : e ≤ f + d) :
    C * n ^ e / n ^ f ≤ C * n ^ d := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  apply (div_le_iff₀ (pow_pos hnpos f)).mpr
  calc
    _ ≤ C * n ^ (f + d) := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn he) zero_le
    _ = _ := by rw [pow_add]; ring

theorem source_two_family_coefficient_le
    (ell q r s b f : ℕ) (hr : r ≤ q) (hs : s ≤ q) (hb : b ≤ 2 * q + 1) (hf : f ≤ 2 * q)
    (w z z' : ℝ≥0) (hw : 1 ≤ w) :
    (((f + 1) ^ (2 * ell + 1) : ℕ) : ℝ≥0) *
      (2 : ℝ≥0) ^ (2 * (r - 2) + (s - 2) + b) * z * z' * w ^ f ≤
      sourceCommonClassCoefficient ell q w z z' := by
  have hprofile : (((f + 1) ^ (2 * ell + 1) : ℕ) : ℝ≥0) ≤
      (((2 * q + 1) ^ (2 * ell + 1) : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.pow_le_pow_left (by omega : f + 1 ≤ 2 * q + 1) (2 * ell + 1)
  have htwo : (2 : ℝ≥0) ^ (2 * (r - 2) + (s - 2) + b) ≤ 2 ^ (6 * q + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  exact mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' hprofile htwo) le_rfl) le_rfl)
    (pow_le_pow_right₀ hw hf)

theorem sourceGainForwardClass_good_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell q r s a b k : ℕ}
    {W : Vortex V ell} {F G : ForbiddenFamilyOn V} {y z y' z' : ℝ≥0}
    (hF : SourceVortexWellSpread W r F y z) (hG : SourceVortexWellSpread W s G y' z')
    (hr : r ≤ q) (hs : s ≤ q) (ha : 1 ≤ a) (T : TripleOn V) (H Q Q' : TripleSystemOn V)
    (hQ' : Q'.card ≤ 2 * q + 1)
    (hbudget : H.card + k + 8 ≤ vortexRootExponent r Q.card + vortexRootExponent s b)
    (w : ℝ≥0) (hw : 1 ≤ w) :
    ∑ u : sourceGainForwardClass W F G T a H Q Q' b k,
      setWeight (vortexTripleWeight W w) (u.1.remainder \ H) ≤
        sourceCommonClassCoefficient ell q w z z' * (W.terminalSize : ℝ≥0) ^ (a - 1) := by
  classical
  by_cases hne : (sourceGainForwardClass W F G T a H Q Q' b k).Nonempty
  · obtain ⟨u, hu⟩ := hne
    have hd := (mem_filter.mp (mem_filter.mp hu).1).2
    have hQ : Q.Nonempty := by
      rw [← hd.2.1]
      exact ⟨T, mem_insert_self _ _⟩
    have hQcard : Q.card ≤ r - 2 := by
      rw [← hd.2.1, ← (hF.uniform u.first u.first_mem).1]
      exact card_le_card (u.firstExposureRoot_subset H)
    let f := (r - 2 - (a + 1)) + (s - 4) - k - H.card
    have hf : f ≤ 2 * q := by dsimp only [f]; omega
    have hbudget' : H.card + (u.leftRemainder ∩ u.rightRemainder).card + 8 ≤
        vortexRootExponent r (u.firstExposureRoot H).card + vortexRootExponent s (u.secondExposureRoot H).card := by
      simpa only [hd.2.1, hd.2.2.2.1, hd.2.2.2.2] using hbudget
    have hexp : (r - vortexRootExponent r Q.card) + (s - vortexRootExponent s b) ≤ f + (a - 1) := by
      have h := u.forward_exponents_le_remainder_add H hd.1 ha r s
        (hF.uniform u.first u.first_mem).1 (hG.uniform u.second u.second_mem).1 hbudget'
      rw [hd.2.1, hd.2.2.2.1, u.remainder_sdiff_card H hd.1,
        (hF.uniform u.first u.first_mem).1, (hG.uniform u.second u.second_mem).1,
        hd.2.2.2.2] at h
      dsimp only [f]
      omega
    let C : ℝ≥0 := (((f + 1) ^ (2 * ell + 1) : ℕ) : ℝ≥0) *
      (2 : ℝ≥0) ^ (2 * (r - 2) + (s - 2) + Q'.card) * z * z' * w ^ f
    have hn : (1 : ℝ≥0) ≤ W.terminalSize := by exact_mod_cast hF.terminal_nonempty
    exact (sourceGainForwardClass_weight_le hF hG T H Q Q' hQ hQcard w).trans
      ((source_weight_power_ratio_le (W.terminalSize : ℝ≥0) C _ f (a - 1) hn hexp).trans
        (mul_le_mul_of_nonneg_right (source_two_family_coefficient_le ell q r s Q'.card f
          hr hs hQ' hf w z z' hw) zero_le))
  · haveI : IsEmpty (sourceGainForwardClass W F G T a H Q Q' b k) := ⟨fun u ↦ hne ⟨u.1, u.2⟩⟩
    simp only [Fintype.sum_empty, zero_le]

end

end Erdos207
