/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Tactic

/-! # Positive selector-denominator budgets for the coupled process -/

namespace Erdos207

theorem coupled_selector_denominator_lower
    {L x e M D k : ℝ} (hL : 0 < L) (hx : 0 < x)
    (he : e ≤ x / 4) (hM : |M - L * x / 3| ≤ L * e / 3)
    (hD : D ≤ k * x) (hk : 12 * k ≤ L) :
    L * x / 6 ≤ M - D := by
  have hm := (abs_le.mp hM).1
  have he' := mul_le_mul_of_nonneg_left he hL.le
  have hk' := mul_le_mul_of_nonneg_right hk hx.le
  nlinarith only [hm, he', hk', hD]

theorem coupled_selector_denominator_error
    {L x e M D k : ℝ} (hD0 : 0 ≤ D) (hk0 : 0 ≤ k)
    (hM : |M - L * x / 3| ≤ L * e / 3)
    (hD : D ≤ k * x) (hxe : x ≤ L * e) :
    |M - D - L * x / 3| ≤ (1 / 3 + k) * L * e := by
  have hd : D ≤ k * (L * e) := hD.trans (mul_le_mul_of_nonneg_left hxe hk0)
  have hid : M - D - L * x / 3 = (M - L * x / 3) - D := by ring
  rw [hid]
  calc
    |(M - L * x / 3) - D| ≤ |M - L * x / 3| + |D| := abs_sub _ _
    _ ≤ L * e / 3 + D := by rw [abs_of_nonneg hD0]; exact add_le_add hM le_rfl
    _ ≤ (1 / 3 + k) * L * e := by nlinarith only [hd]

theorem coupled_pair_denominator_budget
    {L x e M u : ℝ} (hL : 24 ≤ L) (hx : 0 < x)
    (he : e ≤ x / 4) (hu0 : 0 ≤ u)
    (hu : |u - x| ≤ e) (hM : |M - L * x / 3| ≤ L * e / 3)
    (hxe : x ≤ L * e) :
    L * x / 6 ≤ M - u ∧ |M - u - L * x / 3| ≤ (7 / 3) * L * e := by
  have hu' : u ≤ 2 * x := by have h := (abs_le.mp hu).2; linarith
  constructor
  · exact coupled_selector_denominator_lower (by linarith) hx he hM hu' (by linarith)
  · convert coupled_selector_denominator_error hu0 (by norm_num : (0 : ℝ) ≤ 2)
      hM hu' hxe using 1
    ring

end Erdos207
