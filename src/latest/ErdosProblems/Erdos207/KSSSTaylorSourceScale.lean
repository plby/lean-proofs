/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSEnvelopeLowerBounds
import ErdosProblems.Erdos207.KSSSPairCurvatureBound
import ErdosProblems.Erdos207.KSSSConfigurationCurvatureBound

/-! # The discrete Taylor errors on the source envelope scale -/

namespace Erdos207

open Finset

noncomputable section

def ksssPairTaylorCoefficient (orders : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  3 * (18 + 12 * (∑ d ∈ orders, (d : ℝ) * b d) +
    (∑ d ∈ orders, (d : ℝ) * b d) ^ 2 +
      (∑ d ∈ orders, (d : ℝ) * (d - 1 : ℕ) * b d))

def ksssConfigurationTaylorCoefficient (orders : Finset ℕ) (b : ℕ → ℝ) (d c : ℕ) : ℝ :=
  (d.choose c : ℝ) * b d * powerProductCurvatureCoefficient c (d - c)
    (ksssAvailableSlopeBudget orders b) (ksssAvailableCurvatureBudget orders b)

theorem ksssPairTaylorCoefficient_nonneg
    (orders : Finset ℕ) (b : ℕ → ℝ) (hb : ∀ d ∈ orders, 0 ≤ b d) :
    0 ≤ ksssPairTaylorCoefficient orders b := by
  have h₁ : 0 ≤ ∑ d ∈ orders, (d : ℝ) * b d :=
    sum_nonneg fun d hd ↦ mul_nonneg (Nat.cast_nonneg _) (hb d hd)
  have h₂ : 0 ≤ ∑ d ∈ orders, (d : ℝ) * (d - 1 : ℕ) * b d :=
    sum_nonneg fun d hd ↦ mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hb d hd)
  unfold ksssPairTaylorCoefficient
  positivity

theorem ksssConfigurationTaylorCoefficient_nonneg
    (orders : Finset ℕ) (b : ℕ → ℝ) (d c : ℕ)
    (hb : ∀ k ∈ orders, 0 ≤ b k) (hd : d ∈ orders) :
    0 ≤ ksssConfigurationTaylorCoefficient orders b d c := by
  have hb₁ := (ksssAvailable_derivative_budgets_nonneg orders b hb).1
  have hb₂ := (ksssAvailable_derivative_budgets_nonneg orders b hb).2
  have hbd := hb d hd
  unfold ksssConfigurationTaylorCoefficient powerProductCurvatureCoefficient
  positivity

theorem ksssPairTrajectory_unitStep_error_source_scale
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E₀ A₀ scale t : ℝ) (B : ℕ)
    (hE : 0 < E₀) (hA : 0 ≤ A₀) (hs : 0 ≤ scale) (ht : 0 ≤ t)
    (hclock : 3 * (t + 1) < E₀) (hsize : A₀ ≤ scale * E₀ ^ 2)
    (horders : ∀ d ∈ orders, 1 ≤ d) (ha : ∀ d ∈ orders, 0 ≤ a d)
    (hab : ∀ d ∈ orders, a d * E₀ ^ d ≤ b d) :
    |ksssPairTrajectory orders a E₀ A₀ (t + 1) - ksssPairTrajectory orders a E₀ A₀ t -
      ksssPairSlope orders a E₀ A₀ t| ≤
      ksssPairTaylorCoefficient orders b * ksssErrorEnvelope E₀ scale B t /
        (E₀ * ksssEdgeDensity E₀ t) := by
  have hb : ∀ d ∈ orders, 0 ≤ b d := fun d hd ↦
    (mul_nonneg (ha d hd) (pow_nonneg hE.le d)).trans (hab d hd)
  have hc := ksssPairTaylorCoefficient_nonneg orders b hb
  have hscale := ksss_curvature_scale_le_configuration_error E₀ A₀ scale t B 0
    hE hA hs ht (by linarith) (by omega) hsize
  simp only [zero_add, pow_one, ksssConfigurationErrorEnvelope, pow_zero, mul_one] at hscale
  have h := ksssPairTrajectory_unitStep_error_le_coefficients orders a b E₀ A₀ t
    hE hA ht hclock horders ha hab
  calc
    _ ≤ (3 * A₀ * (18 + 12 * (∑ d ∈ orders, (d : ℝ) * b d) +
        (∑ d ∈ orders, (d : ℝ) * b d) ^ 2 +
          (∑ d ∈ orders, (d : ℝ) * (d - 1 : ℕ) * b d))) / E₀ ^ 3 := h
    _ = ksssPairTaylorCoefficient orders b * (A₀ / E₀ ^ 3) := by
      unfold ksssPairTaylorCoefficient
      ring
    _ ≤ ksssPairTaylorCoefficient orders b *
        (ksssErrorEnvelope E₀ scale B t / (E₀ * ksssEdgeDensity E₀ t)) :=
      mul_le_mul_of_nonneg_left hscale hc
    _ = _ := by ring

theorem ksssConfigurationTrajectory_unitStep_error_source_scale
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E₀ A₀ scale t : ℝ) (B d c : ℕ)
    (hd : d ∈ orders) (hc : c < d) (hB : 2 * (d - c - 1) ≤ B)
    (hE : 0 < E₀) (hA : 0 ≤ A₀) (hs : 0 ≤ scale) (ht : 0 ≤ t)
    (hclock : 3 * (t + 1) < E₀) (hsize : A₀ ≤ scale * E₀ ^ 2)
    (horders : ∀ k ∈ orders, 1 ≤ k) (ha : ∀ k ∈ orders, 0 ≤ a k)
    (hab : ∀ k ∈ orders, a k * E₀ ^ k ≤ b k) :
    |ksssConfigurationTrajectory orders a E₀ A₀ d c (t + 1) -
      ksssConfigurationTrajectory orders a E₀ A₀ d c t -
        ksssConfigurationSlope orders a E₀ A₀ d c t| ≤
      ksssConfigurationTaylorCoefficient orders b d c *
        ksssConfigurationErrorEnvelope E₀ A₀ scale B (d - c - 1) t /
          (E₀ * ksssEdgeDensity E₀ t) := by
  have hb : ∀ k ∈ orders, 0 ≤ b k := fun k hk ↦
    (mul_nonneg (ha k hk) (pow_nonneg hE.le k)).trans (hab k hk)
  have hcoef := ksssConfigurationTaylorCoefficient_nonneg orders b d c hb hd
  have hscale := ksss_curvature_scale_le_configuration_error E₀ A₀ scale t B (d - c - 1)
    hE hA hs ht (by linarith) hB hsize
  have hpow₁ : d - c - 1 + 1 = d - c := by omega
  have hpow₂ : d - c - 1 + 3 = d - c + 2 := by omega
  rw [hpow₁, hpow₂] at hscale
  calc
    _ ≤ ksssConfigurationCurvatureBudget orders b E₀ A₀ d c :=
      ksssConfigurationTrajectory_unitStep_error_le_budget orders a b E₀ A₀ t d c
        hd hc.le hE hA ht hclock horders ha hab
    _ = ksssConfigurationTaylorCoefficient orders b d c * (A₀ ^ (d - c) / E₀ ^ (d - c + 2)) := by
      unfold ksssConfigurationCurvatureBudget ksssConfigurationTaylorCoefficient
      ring
    _ ≤ ksssConfigurationTaylorCoefficient orders b d c *
        (ksssConfigurationErrorEnvelope E₀ A₀ scale B (d - c - 1) t /
          (E₀ * ksssEdgeDensity E₀ t)) := mul_le_mul_of_nonneg_left hscale hcoef
    _ = _ := by ring

end

end Erdos207
