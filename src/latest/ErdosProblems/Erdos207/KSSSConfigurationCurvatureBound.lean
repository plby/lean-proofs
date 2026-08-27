/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSConfigurationCurvature
import ErdosProblems.Erdos207.PowerProductCurvatureBound
import ErdosProblems.Erdos207.KSSSAvailableCoefficientBounds

/-! # Coefficient-explicit configuration curvature and discrete-step errors -/

namespace Erdos207

noncomputable section

def ksssConfigurationCurvatureBudget
    (orders : Finset ℕ) (b : ℕ → ℝ) (E₀ A₀ : ℝ) (d c : ℕ) : ℝ :=
  ((d.choose c : ℝ) * b d * A₀ ^ (d - c) * powerProductCurvatureCoefficient c (d - c)
    (ksssAvailableSlopeBudget orders b) (ksssAvailableCurvatureBudget orders b)) / E₀ ^ (d - c + 2)

theorem ksssConfigurationCurvature_mul_clock_power_le
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E₀ A₀ t : ℝ) (d c : ℕ)
    (hd : d ∈ orders) (hc : c ≤ d)
    (hE : 0 < E₀) (hA : 0 ≤ A₀) (ht : 0 ≤ t) (hclock : 3 * t < E₀)
    (horders : ∀ k ∈ orders, 1 ≤ k) (ha : ∀ k ∈ orders, 0 ≤ a k)
    (hab : ∀ k ∈ orders, a k * E₀ ^ k ≤ b k) :
    |ksssConfigurationCurvature orders a E₀ A₀ d c t| * E₀ ^ (d - c + 2) ≤
      (d.choose c : ℝ) * b d * A₀ ^ (d - c) * powerProductCurvatureCoefficient c (d - c)
        (ksssAvailableSlopeBudget orders b) (ksssAvailableCurvatureBudget orders b) := by
  let m := d - c
  let H := powerProductCurvatureCoefficient c m
    (ksssAvailableSlopeBudget orders b) (ksssAvailableCurvatureBudget orders b)
  let P := powerProductCurvature c m (ksssAvailableTrajectory orders a E₀ A₀)
    (ksssAvailableSlope orders a E₀ A₀) (ksssAvailableCurvature orders a E₀ A₀) t
  have hb : ∀ k ∈ orders, 0 ≤ b k := fun k hk ↦
    (mul_nonneg (ha k hk) (pow_nonneg hE.le k)).trans (hab k hk)
  have hbud := ksssAvailable_derivative_budgets_nonneg orders b hb
  have hC₁ := hbud.1
  have hC₂ := hbud.2
  have hH : 0 ≤ H := by dsimp only [H, powerProductCurvatureCoefficient]; positivity
  have hvalue := ksssAvailable_uniform_value_derivative_bounds orders a b E₀ A₀ t
    hE hA ht hclock horders ha hab
  have hbase : |P| * E₀ ^ 2 ≤ E₀ ^ c * A₀ ^ m * H :=
    powerProductCurvature_mul_clock_sq_le c m _ _ _ t A₀ E₀ _ _ ht (by linarith)
      hvalue.1 hvalue.2.1 hbud.1 hbud.2 hvalue.2.2.1 hvalue.2.2.2
  have had := ha d hd
  have hcoef : 0 ≤ (d.choose c : ℝ) * a d := mul_nonneg (Nat.cast_nonneg _) had
  have he : E₀ ^ c * E₀ ^ m = E₀ ^ d := by
    rw [← pow_add]
    congr 1
    dsimp only [m]
    omega
  have hid : |ksssConfigurationCurvature orders a E₀ A₀ d c t| * E₀ ^ (m + 2) =
      ((d.choose c : ℝ) * a d) * (|P| * E₀ ^ 2) * E₀ ^ m := by
    change |((d.choose c : ℝ) * a d) * P| * E₀ ^ (m + 2) = _
    rw [abs_mul, abs_of_nonneg hcoef, pow_add]
    ring
  change |ksssConfigurationCurvature orders a E₀ A₀ d c t| * E₀ ^ (m + 2) ≤
    (d.choose c : ℝ) * b d * A₀ ^ m * H
  calc
    _ = ((d.choose c : ℝ) * a d) * (|P| * E₀ ^ 2) * E₀ ^ m := hid
    _ ≤ ((d.choose c : ℝ) * a d) * (E₀ ^ c * A₀ ^ m * H) * E₀ ^ m :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase hcoef) (pow_nonneg hE.le m)
    _ = (d.choose c : ℝ) * (a d * E₀ ^ d) * A₀ ^ m * H := by rw [← he]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hab d hd) (Nat.cast_nonneg _))
        (pow_nonneg hA m)) hH

theorem ksssConfigurationCurvature_le_budget
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E₀ A₀ t : ℝ) (d c : ℕ)
    (hd : d ∈ orders) (hc : c ≤ d)
    (hE : 0 < E₀) (hA : 0 ≤ A₀) (ht : 0 ≤ t) (hclock : 3 * t < E₀)
    (horders : ∀ k ∈ orders, 1 ≤ k) (ha : ∀ k ∈ orders, 0 ≤ a k)
    (hab : ∀ k ∈ orders, a k * E₀ ^ k ≤ b k) :
    |ksssConfigurationCurvature orders a E₀ A₀ d c t| ≤
      ksssConfigurationCurvatureBudget orders b E₀ A₀ d c := by
  apply (le_div_iff₀ (pow_pos hE (d - c + 2))).mpr
  exact ksssConfigurationCurvature_mul_clock_power_le orders a b E₀ A₀ t d c
    hd hc hE hA ht hclock horders ha hab

theorem ksssConfigurationTrajectory_unitStep_error_le_budget
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E₀ A₀ t : ℝ) (d c : ℕ)
    (hd : d ∈ orders) (hc : c ≤ d)
    (hE : 0 < E₀) (hA : 0 ≤ A₀) (ht : 0 ≤ t) (hclock : 3 * (t + 1) < E₀)
    (horders : ∀ k ∈ orders, 1 ≤ k) (ha : ∀ k ∈ orders, 0 ≤ a k)
    (hab : ∀ k ∈ orders, a k * E₀ ^ k ≤ b k) :
    |ksssConfigurationTrajectory orders a E₀ A₀ d c (t + 1) -
      ksssConfigurationTrajectory orders a E₀ A₀ d c t -
        ksssConfigurationSlope orders a E₀ A₀ d c t| ≤
      ksssConfigurationCurvatureBudget orders b E₀ A₀ d c := by
  have hnow := ksssConfigurationCurvature_le_budget orders a b E₀ A₀ t d c
    hd hc hE hA ht (by linarith) horders ha hab
  apply ksssConfigurationTrajectory_unitStep_error_le orders a E₀ A₀ d c t _ hE.ne'
    ((abs_nonneg _).trans hnow)
  intro u hu
  exact ksssConfigurationCurvature_le_budget orders a b E₀ A₀ u d c
    hd hc hE hA (ht.trans hu.1) (by have h := hu.2; linarith) horders ha hab

end

end Erdos207
