/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PowerProductCurvature
import ErdosProblems.Erdos207.PowerDerivativeBounds

/-! # Clock-scaled curvature of the polynomial configuration product -/

namespace Erdos207

def powerProductCurvatureCoefficient (c m : ℕ) (C₁ C₂ : ℝ) : ℝ :=
  (c : ℝ) * (c - 1 : ℕ) + 2 * c * m * C₁ +
    (m : ℝ) * (m - 1 : ℕ) * C₁ ^ 2 + m * C₂

theorem powerProductCurvature_mul_clock_sq_le
    (c m : ℕ) (A A₁ A₂ : ℝ → ℝ) (t M E C₁ C₂ : ℝ)
    (ht : 0 ≤ t) (htE : t ≤ E) (hA : 0 ≤ A t) (hAM : A t ≤ M)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hA₁ : |A₁ t| * E ≤ M * C₁) (hA₂ : |A₂ t| * E ^ 2 ≤ M * C₂) :
    |powerProductCurvature c m A A₁ A₂ t| * E ^ 2 ≤
      E ^ c * M ^ m * powerProductCurvatureCoefficient c m C₁ C₂ := by
  let F₀ := t ^ c
  let F₁ := (c : ℝ) * t ^ (c - 1)
  let F₂ := (c : ℝ) * (c - 1 : ℕ) * t ^ (c - 2)
  let G₀ := A t ^ m
  let G₁ := (m : ℝ) * A t ^ (m - 1) * A₁ t
  let G₂ := (m : ℝ) * (m - 1 : ℕ) * A t ^ (m - 2) * A₁ t ^ 2
  let G₃ := (m : ℝ) * A t ^ (m - 1) * A₂ t
  have hE : 0 ≤ E := ht.trans htE
  have hM : 0 ≤ M := hA.trans hAM
  have hf0 : |F₀| ≤ E ^ c := by
    rw [abs_of_nonneg (pow_nonneg ht c)]
    exact pow_le_pow_left₀ ht htE c
  have hg0 : |G₀| ≤ M ^ m := by
    rw [abs_of_nonneg (pow_nonneg hA m)]
    exact pow_le_pow_left₀ hA hAM m
  have hf1 : |F₁| * E ≤ (c : ℝ) * E ^ c := monomial_slope_mul_clock_le c t E ht htE
  have hf2 : |F₂| * E ^ 2 ≤ (c : ℝ) * (c - 1 : ℕ) * E ^ c :=
    monomial_curvature_mul_clock_sq_le c t E ht htE
  have hg1 : |G₁| * E ≤ (m : ℝ) * M ^ m * C₁ :=
    power_slope_mul_clock_le m (A t) (A₁ t) M E C₁ hA hAM hE hC₁ hA₁
  have hg2 : |G₂| * E ^ 2 ≤ (m : ℝ) * (m - 1 : ℕ) * M ^ m * C₁ ^ 2 :=
    power_quadraticSlope_mul_clock_sq_le m (A t) (A₁ t) M E C₁ hA hAM hE hC₁ hA₁
  have hg3 : |G₃| * E ^ 2 ≤ (m : ℝ) * M ^ m * C₂ :=
    power_slope_mul_clock_le m (A t) (A₂ t) M (E ^ 2) C₂ hA hAM (sq_nonneg E) hC₂ hA₂
  have hid : powerProductCurvature c m A A₁ A₂ t = F₂ * G₀ + 2 * (F₁ * G₁) + F₀ * G₂ + F₀ * G₃ := by
    dsimp only [powerProductCurvature, F₀, F₁, F₂, G₀, G₁, G₂, G₃]
    ring
  have habs : |powerProductCurvature c m A A₁ A₂ t| ≤
      |F₂| * |G₀| + 2 * (|F₁| * |G₁|) + |F₀| * |G₂| + |F₀| * |G₃| := by
    rw [hid]
    calc
      _ ≤ |F₂ * G₀| + |2 * (F₁ * G₁)| + |F₀ * G₂| + |F₀ * G₃| :=
        (abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ = _ := by simp only [abs_mul, show |(2 : ℝ)| = 2 by norm_num]
  calc
    _ ≤ (|F₂| * |G₀| + 2 * (|F₁| * |G₁|) + |F₀| * |G₂| + |F₀| * |G₃|) * E ^ 2 :=
      mul_le_mul_of_nonneg_right habs (sq_nonneg E)
    _ = (|F₂| * E ^ 2) * |G₀| + 2 * ((|F₁| * E) * (|G₁| * E)) +
        |F₀| * (|G₂| * E ^ 2) + |F₀| * (|G₃| * E ^ 2) := by ring
    _ ≤ ((c : ℝ) * (c - 1 : ℕ) * E ^ c) * M ^ m +
        2 * (((c : ℝ) * E ^ c) * ((m : ℝ) * M ^ m * C₁)) +
        E ^ c * ((m : ℝ) * (m - 1 : ℕ) * M ^ m * C₁ ^ 2) +
        E ^ c * ((m : ℝ) * M ^ m * C₂) := by
      apply add_le_add
      · apply add_le_add
        · exact add_le_add (mul_le_mul hf2 hg0 (abs_nonneg _) (by positivity))
            (mul_le_mul_of_nonneg_left (mul_le_mul hf1 hg1 (by positivity) (by positivity)) (by norm_num))
        · exact mul_le_mul hf0 hg2 (by positivity) (by positivity)
      · exact mul_le_mul hf0 hg3 (by positivity) (by positivity)
    _ = _ := by dsimp only [powerProductCurvatureCoefficient]; ring

end Erdos207
