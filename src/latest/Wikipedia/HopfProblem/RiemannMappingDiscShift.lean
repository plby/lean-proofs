/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

module
public import Mathlib.Analysis.Complex.UnitDisc.Basic

/-!
# Shift on the unit disc

This file ports the unit-disc shift API needed by the Riemann mapping theorem from
Yury Kudryashov's Mathlib development, commit
`d43061d911b1aeae0788591da437a3b115098962`:

<https://raw.githubusercontent.com/urkud/mathlib4/d43061d911b1aeae0788591da437a3b115098962/Mathlib/Analysis/Complex/UnitDisc/Shift.lean>.

`Complex.UnitDisc.shift z` is the automorphism of the unit disc that sends `0` to `z`
and preserves the diameter joining `0` to `z`. The port retains the original algebraic
construction and adds continuity in the input point. Unneeded composition and rotation
formulas are omitted.
-/

open Set Function Metric
open scoped ComplexConjugate

noncomputable section

namespace Complex.UnitDisc

public section

lemma shift_den_ne_zero (z w : 𝔻) : 1 + conj (z : ℂ) * w ≠ 0 :=
  (star z * w).one_add_coe_ne_zero

lemma shift_den_ne_zero' (z w : 𝔻) : 1 + z * conj (w : ℂ) ≠ 0 :=
  (z * star w).one_add_coe_ne_zero

end

theorem norm_shiftFun_le (z w : 𝔻) :
    ‖(z + w : ℂ) / (1 + conj ↑z * w)‖ ≤
      (‖(z : ℂ)‖ + ‖(w : ℂ)‖) / (1 + ‖(z : ℂ)‖ * ‖(w : ℂ)‖) := by
  have hz := z.sq_norm_lt_one
  have hw := w.sq_norm_lt_one
  have hzw : z.re * w.re + z.im * w.im ≤ ‖(z : ℂ)‖ * ‖(w : ℂ)‖ := by
    rw [norm_def, norm_def, ← Real.sqrt_mul, normSq_apply, normSq_apply]
    · apply Real.le_sqrt_of_sq_le
      linear_combination (norm := {apply le_of_eq; simp; ring})
        sq_nonneg (z.re * w.im - z.im * w.re)
    · apply normSq_nonneg
  rw [norm_div, div_le_div_iff₀, ← sq_le_sq₀]
  · rw [← sub_nonneg] at hzw
    simp [mul_pow, RCLike.norm_sq_eq_def, add_sq] at hz hw ⊢
    linear_combination 2 * mul_nonneg hzw
      (mul_nonneg (sub_nonneg.2 hz.le) (sub_nonneg.2 hw.le))
  any_goals positivity
  simpa using shift_den_ne_zero z w

/-- Auxiliary definition for `shift` below. -/
def shiftFun (z w : 𝔻) : 𝔻 :=
  mk ((z + w : ℂ) / (1 + conj ↑z * w)) <| by
    refine (norm_shiftFun_le _ _).trans_lt ?_
    rw [div_lt_one (by positivity)]
    nlinarith only [z.norm_lt_one, w.norm_lt_one]

theorem coe_shiftFun (z w : 𝔻) :
    (shiftFun z w : ℂ) = (z + w) / (1 + conj ↑z * w) := rfl

theorem shiftFun_eq_iff {z w u : 𝔻} :
    shiftFun z w = u ↔ (z + w : ℂ) = u + u * conj ↑z * w := by
  rw [← coe_inj, coe_shiftFun, div_eq_iff (shift_den_ne_zero _ _)]
  ring_nf

theorem shiftFun_neg_apply_shiftFun (z w : 𝔻) : shiftFun (-z) (shiftFun z w) = w := by
  rw [shiftFun_eq_iff, coe_shiftFun, add_div_eq_mul_add_div, ← mul_div_assoc,
    add_div_eq_mul_add_div]
  · simp; ring
  all_goals exact shift_den_ne_zero z w

public section

/-- The automorphism of the unit disc that sends zero to `z`. -/
def shift (z : 𝔻) : 𝔻 ≃ 𝔻 where
  toFun := shiftFun z
  invFun := shiftFun (-z)
  left_inv := shiftFun_neg_apply_shiftFun _
  right_inv := by
    intro w
    simpa using shiftFun_neg_apply_shiftFun (-z) w

/-- The explicit complex-coordinate formula for the disc shift. -/
theorem coe_shift (z w : 𝔻) : (shift z w : ℂ) = (z + w) / (1 + conj ↑z * w) := by rfl

theorem shift_eq_iff {z w u : 𝔻} : shift z w = u ↔ (z + w : ℂ) = u + u * conj ↑z * w :=
  shiftFun_eq_iff

theorem symm_shift (z : 𝔻) : (shift z).symm = shift (-z) := by
  ext1
  rfl

@[simp]
theorem star_shift (z w : 𝔻) : star (shift z w) = shift (star z) (star w) :=
  coe_injective <| by simp [coe_shift]

theorem norm_shift_swap (z w : 𝔻) : ‖(shift z w : ℂ)‖ = ‖(shift w z : ℂ)‖ := by
  rw [coe_shift, norm_div, ← norm_conj (1 + _)]
  simp [coe_shift, add_comm, mul_comm]

theorem neg_shift (z w : 𝔻) : -shift z w = shift (-z) (-w) := by
  ext1
  simp [coe_shift, ← neg_add_rev, add_comm, neg_div]

@[simp]
theorem shift_zero : shift 0 = .refl 𝔻 := by
  ext z
  simp [coe_shift]

@[simp]
theorem shift_apply_zero (z : 𝔻) : shift z 0 = z := by simp [shift_eq_iff]

@[simp]
theorem shift_eq_zero_iff {z w : 𝔻} : shift z w = 0 ↔ w = -z := by
  rw [← Equiv.eq_symm_apply, symm_shift, shift_apply_zero]

@[simp]
theorem shift_apply_neg_self (z : 𝔻) : shift z (-z) = 0 := by simp

@[simp]
theorem shift_neg_apply_self (z : 𝔻) : shift (-z) z = 0 := by simp

@[simp]
theorem shift_neg_apply_shift (z w : 𝔻) : shift (-z) (shift z w) = w := by
  rw [← symm_shift, Equiv.symm_apply_apply]

@[simp]
theorem shift_apply_shift_neg (z w : 𝔻) : shift z (shift (-z) w) = w := by
  simpa using shift_neg_apply_shift (-z) w

/-- Each disc shift is continuous. -/
@[fun_prop]
theorem continuous_shift (z : 𝔻) : Continuous (shift z) := by
  rw [isEmbedding_coe.continuous_iff]
  change Continuous (fun w : 𝔻 ↦ (shift z w : ℂ))
  simp only [coe_shift]
  exact (continuous_const.add continuous_coe).div
    (continuous_const.add (continuous_const.mul continuous_coe))
    (shift_den_ne_zero z)

end

end UnitDisc

end Complex
