import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open Filter
open scoped Topology

/-- A counting function which is little-o of `sqrt n` is eventually below any
fixed positive linear slope, in an exact natural cross-multiplied form. -/
theorem eventually_mul_count_le_of_isLittleO_sqrt
    (p : ℕ → Prop) [DecidablePred p]
    (h : (fun n : ℕ => (Nat.count p n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ)))
    (K : ℕ) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop, K * Nat.count p n ≤ n := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hcpos : (0 : ℝ) < 1 / (2 * (K : ℝ)) := by positivity
  have hb := h.bound hcpos
  filter_upwards [hb, eventually_ge_atTop 1] with n hn hn1
  have hncount : (Nat.count p n : ℝ) ≤
      (1 / (2 * (K : ℝ))) * Real.sqrt (n : ℝ) := by
    simpa only [Real.norm_natCast, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (Nat.count p n : ℝ) by positivity),
      abs_of_nonneg (Real.sqrt_nonneg _)] using hn
  have hsqrt : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      nlinarith
  have hmul := mul_le_mul_of_nonneg_left hncount hKR.le
  have hcast : ((K * Nat.count p n : ℕ) : ℝ) ≤ (n : ℝ) := by
    norm_num only [Nat.cast_mul]
    have hid : (K : ℝ) * (1 / (2 * (K : ℝ))) = 1 / 2 := by
      field_simp
    rw [← mul_assoc, hid] at hmul
    nlinarith
  exact_mod_cast hcast

end Erdos489
