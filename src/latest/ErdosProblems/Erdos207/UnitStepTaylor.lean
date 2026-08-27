/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! # Explicit one-step Taylor error from two mean-value inequalities -/

namespace Erdos207

theorem unitStep_taylor_error_le
    (f f₁ f₂ : ℝ → ℝ) (t C : ℝ) (hC : 0 ≤ C)
    (h₁ : ∀ u ∈ Set.Icc t (t + 1), HasDerivAt f (f₁ u) u)
    (h₂ : ∀ u ∈ Set.Icc t (t + 1), HasDerivAt f₁ (f₂ u) u)
    (hb : ∀ u ∈ Set.Icc t (t + 1), |f₂ u| ≤ C) :
    |f (t + 1) - f t - f₁ t| ≤ C := by
  have hvar : ∀ u ∈ Set.Icc t (t + 1), |f₁ u - f₁ t| ≤ C := by
    intro u hu
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun x hx ↦ (h₂ x hx).hasDerivWithinAt)
      (fun x hx ↦ show ‖f₂ x‖ ≤ C by
        simpa only [Real.norm_eq_abs] using (hb x (Set.Ico_subset_Icc_self hx))) u hu
    have hlen : u - t ≤ 1 := by have hx := hu.2; linarith
    exact (show |f₁ u - f₁ t| ≤ C * (u - t) by
      simpa only [Real.norm_eq_abs] using h).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hlen hC)
  let g := fun u ↦ f u - f₁ t * (u - t)
  have hg : ∀ u ∈ Set.Icc t (t + 1), HasDerivAt g (f₁ u - f₁ t) u := by
    intro u hu
    simpa only [mul_one] using! (h₁ u hu).sub (((hasDerivAt_id u).sub_const t).const_mul (f₁ t))
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun u hu ↦ (hg u hu).hasDerivWithinAt)
    (fun u hu ↦ show ‖f₁ u - f₁ t‖ ≤ C by
      simpa only [Real.norm_eq_abs] using (hvar u (Set.Ico_subset_Icc_self hu)))
    (t + 1) (show t + 1 ∈ Set.Icc t (t + 1) from ⟨by linarith, le_rfl⟩)
  have he : g (t + 1) - g t = f (t + 1) - f t - f₁ t := by dsimp [g]; ring
  simpa only [Real.norm_eq_abs, he, add_sub_cancel_left, mul_one] using h

end Erdos207
