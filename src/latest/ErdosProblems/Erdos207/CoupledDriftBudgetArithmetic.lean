/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Tactic

/-! # Explicit scale cancellation in the coupled drift errors -/

namespace Erdos207

theorem div_le_coupled_scale
    {L x R N D h : ℝ} (hL : 0 < L) (hx : 0 < x)
    (hR : L * x / 6 ≤ R) (hD : 0 ≤ D) (hh : 0 ≤ h)
    (hN : N ≤ D * x * h) :
    N / R ≤ 6 * D * h / L := by
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hR
  rw [div_le_div_iff₀ hRpos hL]
  calc
    N * L ≤ D * x * h * L := mul_le_mul_of_nonneg_right hN hL.le
    _ = (6 * D * h) * (L * x / 6) := by ring
    _ ≤ (6 * D * h) * R := mul_le_mul_of_nonneg_left hR (by positivity)

theorem div_mul_le_coupled_scale
    {L x R N D h : ℝ} (hL : 0 < L) (hx : 0 < x)
    (hR : L * x / 6 ≤ R) (hD : 0 ≤ D) (hh : 0 ≤ h)
    (hN : N ≤ D * L * x ^ 2 * h) :
    N / (R * (L * x / 3)) ≤ 18 * D * h / L := by
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hR
  rw [div_le_div_iff₀ (by positivity) hL]
  calc
    N * L ≤ D * L * x ^ 2 * h * L := mul_le_mul_of_nonneg_right hN hL.le
    _ = (18 * D * h) * ((L * x / 6) * (L * x / 3)) := by ring
    _ ≤ (18 * D * h) * (R * (L * x / 3)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hR (by positivity)) (by positivity)

theorem coupled_three_term_error_budget
    {L x R h N₀ N₁ N₂ D₀ D₁ D₂ : ℝ}
    (hL : 0 < L) (hx : 0 < x) (hR : L * x / 6 ≤ R) (hh : 0 ≤ h)
    (hD₀ : 0 ≤ D₀) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hN₀ : N₀ ≤ D₀ * x * h) (hN₁ : N₁ ≤ D₁ * x * h)
    (hN₂ : N₂ ≤ D₂ * L * x ^ 2 * h) :
    N₀ / R + N₁ / R + N₂ / (R * (L * x / 3)) ≤
      (6 * D₀ + 6 * D₁ + 18 * D₂) * h / L := by
  calc
    _ ≤ 6 * D₀ * h / L + 6 * D₁ * h / L + 18 * D₂ * h / L :=
      add_le_add (add_le_add (div_le_coupled_scale hL hx hR hD₀ hh hN₀)
        (div_le_coupled_scale hL hx hR hD₁ hh hN₁))
        (div_mul_le_coupled_scale hL hx hR hD₂ hh hN₂)
    _ = _ := by ring

theorem pair_drift_error_coupled_scale
    {L x e u R H k C delta : ℝ}
    (hL : 0 < L) (hx : 0 < x) (he : 0 ≤ e) (hu0 : 0 ≤ u)
    (hu : u ≤ 2 * x) (hR : L * x / 6 ≤ R)
    (hk : 0 ≤ k) (hC : 0 ≤ C) (hdelta : 0 ≤ delta) (hH : |H| ≤ C * x) :
    u * (k * e) / R + e * (|H| + |u| + |x|) / R +
      |x * (H - x)| * (delta * L * e) / (R * (L * x / 3)) ≤
        (12 * k + 6 * (C + 3) + 18 * delta * (C + 1)) * e / L := by
  have hN₀ : u * (k * e) ≤ (2 * k) * x * e := by
    calc
      _ ≤ (2 * x) * (k * e) := mul_le_mul_of_nonneg_right hu (by positivity)
      _ = _ := by ring
  have hN₁ : e * (|H| + |u| + |x|) ≤ (C + 3) * x * e := by
    rw [abs_of_nonneg hu0, abs_of_pos hx]
    have hh : |H| + u + x ≤ (C + 3) * x := by nlinarith only [hH, hu]
    calc
      _ ≤ e * ((C + 3) * x) := mul_le_mul_of_nonneg_left hh he
      _ = _ := by ring
  have hN₂ : |x * (H - x)| * (delta * L * e) ≤
      (delta * (C + 1)) * L * x ^ 2 * e := by
    have hh : |H - x| ≤ (C + 1) * x := by
      calc
        _ ≤ |H| + |x| := abs_sub _ _
        _ ≤ C * x + x := by rw [abs_of_pos hx]; exact add_le_add hH le_rfl
        _ = _ := by ring
    rw [abs_mul, abs_of_pos hx]
    calc
      _ ≤ (x * ((C + 1) * x)) * (delta * L * e) := by gcongr
      _ = _ := by ring
  convert coupled_three_term_error_budget hL hx hR he
    (by positivity : 0 ≤ 2 * k) (by positivity : 0 ≤ C + 3)
    (by positivity : 0 ≤ delta * (C + 1)) hN₀ hN₁ hN₂ using 1 <;> ring

theorem configuration_drift_error_coupled_scale
    {L x e h R v alpha beta H epsilonH J Z eprev epsilonA target
      F G k ell W C delta T : ℝ}
    (hL : 0 < L) (hx : 0 < x) (hh : 0 ≤ h) (hv : 0 ≤ v)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hF : 0 ≤ F) (hG : 0 ≤ G) (hk : 0 ≤ k) (hell : 0 ≤ ell)
    (hW : 0 ≤ W) (hC : 0 ≤ C) (hdelta : 0 ≤ delta) (hT : 0 ≤ T)
    (hR : L * x / 6 ≤ R)
    (hve : v * e ≤ F * x * h) (hZ : Z ≤ G * x * h)
    (hHerror : epsilonH ≤ k * e) (hJ : J ≤ ell * e)
    (hprev : eprev ≤ W * x * h) (hH : |H| ≤ C * x)
    (hAerror : epsilonA ≤ delta * L * e)
    (htarget : |target| * e ≤ T * x ^ 2 * h) :
    (2 * Z + v * (beta * epsilonH + J)) / R +
      (alpha * eprev + beta * |H| * h) / R +
        |target| * epsilonA / (R * (L * x / 3)) ≤
      (6 * (2 * G + F * (beta * k + ell)) + 6 * (alpha * W + beta * C) +
        18 * (delta * T)) * h / L := by
  have hfac : beta * epsilonH + J ≤ (beta * k + ell) * e := by
    have hb := mul_le_mul_of_nonneg_left hHerror hbeta
    nlinarith only [hb, hJ]
  have hvloss : v * (beta * epsilonH + J) ≤ F * (beta * k + ell) * x * h := by
    calc
      _ ≤ v * ((beta * k + ell) * e) := mul_le_mul_of_nonneg_left hfac hv
      _ = (beta * k + ell) * (v * e) := by ring
      _ ≤ (beta * k + ell) * (F * x * h) :=
        mul_le_mul_of_nonneg_left hve (by positivity)
      _ = _ := by ring
  have hN₀ : 2 * Z + v * (beta * epsilonH + J) ≤
      (2 * G + F * (beta * k + ell)) * x * h := by
    have hz := mul_le_mul_of_nonneg_left hZ (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [hz, hvloss]
  have hN₁ : alpha * eprev + beta * |H| * h ≤ (alpha * W + beta * C) * x * h := by
    have hp := mul_le_mul_of_nonneg_left hprev halpha
    have hl := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hH hbeta) hh
    nlinarith only [hp, hl]
  have hN₂ : |target| * epsilonA ≤ (delta * T) * L * x ^ 2 * h := by
    calc
      _ ≤ |target| * (delta * L * e) :=
        mul_le_mul_of_nonneg_left hAerror (abs_nonneg _)
      _ = (delta * L) * (|target| * e) := by ring
      _ ≤ (delta * L) * (T * x ^ 2 * h) :=
        mul_le_mul_of_nonneg_left htarget (by positivity)
      _ = _ := by ring
  exact coupled_three_term_error_budget hL hx hR hh
    (by positivity) (by positivity) (by positivity) hN₀ hN₁ hN₂

end Erdos207
