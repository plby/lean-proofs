/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Tactic

/-! # Product-form budgets for configurations and their error scales -/

namespace Erdos207

theorem configuration_monomial_le
    (d c : ℕ) {a b t E M w : ℝ} (hcd : c ≤ d)
    (ha : 0 ≤ a) (ht : 0 ≤ t) (htE : t ≤ E)
    (hM : 0 ≤ M) (hMw : M ≤ E * w) (hw : 0 ≤ w)
    (hab : a * E ^ d ≤ b) :
    (d.choose c : ℝ) * a * t ^ c * M ^ (d - c) ≤
      (d.choose c : ℝ) * b * w ^ (d - c) := by
  have hE : 0 ≤ E := ht.trans htE
  calc
    _ ≤ (d.choose c : ℝ) * a * E ^ c * (E * w) ^ (d - c) := by gcongr
    _ = (d.choose c : ℝ) * (a * E ^ d) * w ^ (d - c) := by
      have hpow : E ^ c * E ^ (d - c) = E ^ d := by
        rw [← pow_add, Nat.add_sub_of_le hcd]
      rw [mul_pow]
      calc
        _ = (d.choose c : ℝ) * a * (E ^ c * E ^ (d - c)) * w ^ (d - c) := by ring
        _ = _ := by rw [hpow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg _)) (pow_nonneg hw _)

theorem power_scaled_error_product
    (z r : ℕ) {y D w W x e : ℝ}
    (hD : 0 ≤ D) (hw : 0 ≤ w) (hW : 0 ≤ W) (hx : 0 ≤ x) (he : 0 ≤ e)
    (hy : y ≤ D * w ^ (z + r)) (hwx : w ≤ W * x) :
    y * e ≤ D * W ^ r * x ^ r * (e * w ^ z) := by
  calc
    _ ≤ (D * w ^ (z + r)) * e := mul_le_mul_of_nonneg_right hy he
    _ = D * w ^ r * (e * w ^ z) := by rw [pow_add]; ring
    _ ≤ D * (W * x) ^ r * (e * w ^ z) := by gcongr
    _ = _ := by rw [mul_pow]; ring

theorem actual_configuration_product_budget
    {v y e h x F : ℝ} (he : 0 ≤ e) (hh : 0 ≤ h)
    (hve : |v - y| ≤ h) (hye : y * e ≤ F * x * h) (hex : e ≤ x) :
    v * e ≤ (F + 1) * x * h := by
  have hv : v ≤ y + h := by have ht := (abs_le.mp hve).2; linarith
  have hv' := mul_le_mul_of_nonneg_right hv he
  have hh' := mul_le_mul_of_nonneg_left hex hh
  nlinarith only [hv', hh', hye]

theorem configuration_target_product_budget
    {alpha beta y₀ y₁ H e x h F₀ F₁ C : ℝ}
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hy₀ : 0 ≤ y₀) (hy₁ : 0 ≤ y₁) (he : 0 ≤ e) (hx : 0 ≤ x) (hC : 0 ≤ C)
    (hprev : y₀ * e ≤ F₀ * x ^ 2 * h) (hcurr : y₁ * e ≤ F₁ * x * h)
    (hH : |H| ≤ C * x) :
    |alpha * y₀ - beta * y₁ * H| * e ≤
      (alpha * F₀ + beta * F₁ * C) * x ^ 2 * h := by
  have ht : |alpha * y₀ - beta * y₁ * H| ≤ alpha * y₀ + beta * y₁ * |H| := by
    calc
      _ ≤ |alpha * y₀| + |beta * y₁ * H| := abs_sub _ _
      _ = _ := by rw [abs_mul (beta * y₁), abs_of_nonneg (mul_nonneg halpha hy₀),
        abs_of_nonneg (mul_nonneg hbeta hy₁)]
  calc
    _ ≤ (alpha * y₀ + beta * y₁ * |H|) * e := mul_le_mul_of_nonneg_right ht he
    _ ≤ (alpha * y₀ + beta * y₁ * (C * x)) * e := by gcongr
    _ = alpha * (y₀ * e) + (beta * C * x) * (y₁ * e) := by ring
    _ ≤ alpha * (F₀ * x ^ 2 * h) + (beta * C * x) * (F₁ * x * h) :=
      add_le_add (mul_le_mul_of_nonneg_left hprev halpha)
        (mul_le_mul_of_nonneg_left hcurr (by positivity))
    _ = _ := by ring

end Erdos207
