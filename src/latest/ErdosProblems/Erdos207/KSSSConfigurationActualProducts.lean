/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSConfigurationProductBounds
import ErdosProblems.Erdos207.KSSSPairStateDrift

/-! # Actual configuration-count and target-numerator product budgets -/

namespace Erdos207

open Finset

noncomputable section

def ksssConfigurationProductCoefficient (orders : Finset ℕ) (b : ℕ → ℝ) (d c : ℕ) : ℝ :=
  (d.choose c : ℝ) * b d * (Real.exp (∑ k ∈ orders, b k) / 3)

def ksssConfigurationSuccTargetCoefficient (orders : Finset ℕ) (b : ℕ → ℝ) (d c : ℕ) : ℝ :=
  ((d - c : ℕ) : ℝ) * ((d.choose c : ℝ) * b d * (Real.exp (∑ k ∈ orders, b k) / 3) ^ 2) +
    ((d - (c + 1) : ℕ) : ℝ) * ksssConfigurationProductCoefficient orders b d (c + 1) *
      ksssThreatCoefficient orders b

theorem ksssConfiguration_actual_product
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E A scale time v : ℝ) (B d c : ℕ)
    (hE : 0 < E) (hA : 0 < A) (hs : 0 ≤ scale) (ht : 0 ≤ time) (hclock : 3 * time < E)
    (ha : ∀ k ∈ orders, 0 ≤ a k) (hab : ∀ k ∈ orders, a k * E ^ k ≤ b k)
    (hd : d ∈ orders) (hc : c + 1 ≤ d)
    (hsmall : ksssErrorEnvelope E scale B time ≤ ksssPairTrajectory orders a E A time)
    (hv : |v - ksssConfigurationTrajectory orders a E A d c time| ≤
      ksssConfigurationErrorEnvelope E A scale B (d - c - 1) time) :
    v * ksssErrorEnvelope E scale B time ≤
      (ksssConfigurationProductCoefficient orders b d c + 1) * ksssPairTrajectory orders a E A time *
        ksssConfigurationErrorEnvelope E A scale B (d - c - 1) time := by
  have hp := ksssEdgeDensity_pos hE hclock
  have he : 0 ≤ ksssErrorEnvelope E scale B time := by unfold ksssErrorEnvelope; positivity
  have hh : 0 ≤ ksssConfigurationErrorEnvelope E A scale B (d - c - 1) time := by
    unfold ksssConfigurationErrorEnvelope ksssErrorEnvelope
    positivity
  have hy := ksssConfigurationTrajectory_error_product orders a b E A scale time B d c
    (d - c - 1) 1 hE hA hs ht hclock ha hab hd (by omega) (by omega)
  simp only [pow_one] at hy
  exact actual_configuration_product_budget he hh hv hy hsmall

theorem ksssConfiguration_succ_target_product
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E A scale time : ℝ) (B d c : ℕ)
    (hE : 0 < E) (hA : 0 < A) (hs : 0 ≤ scale) (ht : 0 ≤ time) (hclock : 3 * time < E)
    (horders : ∀ k ∈ orders, 1 ≤ k)
    (ha : ∀ k ∈ orders, 0 ≤ a k) (hab : ∀ k ∈ orders, a k * E ^ k ≤ b k)
    (hd : d ∈ orders) (hc : c + 2 ≤ d) :
    |((d - c : ℕ) : ℝ) * ksssConfigurationTrajectory orders a E A d c time -
      ((d - (c + 1) : ℕ) : ℝ) * ksssConfigurationTrajectory orders a E A d (c + 1) time *
        ksssThreatTrajectory orders a E A time| * ksssErrorEnvelope E scale B time ≤
      ksssConfigurationSuccTargetCoefficient orders b d c * ksssPairTrajectory orders a E A time ^ 2 *
        ksssConfigurationErrorEnvelope E A scale B (d - (c + 1) - 1) time := by
  have hp := ksssEdgeDensity_pos hE hclock
  have hx := ksssPairTrajectory_pos orders a hE hA hclock
  have hb : ∀ k ∈ orders, 0 ≤ b k := fun k hk ↦
    (mul_nonneg (ha k hk) (pow_nonneg hE.le k)).trans (hab k hk)
  have he : 0 ≤ ksssErrorEnvelope E scale B time := by unfold ksssErrorEnvelope; positivity
  have hy0 := ksssConfigurationTrajectory_nonneg orders a E A time d c hA.le ht hp.le (ha d hd)
  have hy1 := ksssConfigurationTrajectory_nonneg orders a E A time d (c + 1) hA.le ht hp.le (ha d hd)
  have hprev := ksssConfigurationTrajectory_error_product orders a b E A scale time B d c
    (d - (c + 1) - 1) 2 hE hA hs ht hclock ha hab hd (by omega) (by omega)
  have hcurr := ksssConfigurationTrajectory_error_product orders a b E A scale time B d (c + 1)
    (d - (c + 1) - 1) 1 hE hA hs ht hclock ha hab hd (by omega) (by omega)
  simp only [pow_one] at hcurr
  have hH := ksssThreatTrajectory_bounds orders a b horders ha hab hE hA ht hclock
  have hH0 : 0 ≤ ksssThreatTrajectory orders a E A time := by linarith only [hx, hH.1]
  have hHabs : |ksssThreatTrajectory orders a E A time| ≤
      ksssThreatCoefficient orders b * ksssPairTrajectory orders a E A time := by
    rw [abs_of_nonneg hH0]
    exact hH.2
  exact configuration_target_product_budget (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hy0 hy1 he hx.le (ksssThreatCoefficient_nonneg orders b hb) hprev hcurr hHabs

theorem ksssConfiguration_zero_target_product
    (orders : Finset ℕ) (a b : ℕ → ℝ) (E A scale time : ℝ) (B d : ℕ)
    (hE : 0 < E) (hA : 0 < A) (hs : 0 ≤ scale) (ht : 0 ≤ time) (hclock : 3 * time < E)
    (horders : ∀ k ∈ orders, 1 ≤ k)
    (ha : ∀ k ∈ orders, 0 ≤ a k) (hab : ∀ k ∈ orders, a k * E ^ k ≤ b k)
    (hd : d ∈ orders) :
    |(d : ℝ) * ksssConfigurationTrajectory orders a E A d 0 time *
      ksssThreatTrajectory orders a E A time| * ksssErrorEnvelope E scale B time ≤
      ((d : ℝ) * ksssConfigurationProductCoefficient orders b d 0 * ksssThreatCoefficient orders b) *
        ksssPairTrajectory orders a E A time ^ 2 *
          ksssConfigurationErrorEnvelope E A scale B (d - 1) time := by
  have hp := ksssEdgeDensity_pos hE hclock
  have hx := ksssPairTrajectory_pos orders a hE hA hclock
  have hb : ∀ k ∈ orders, 0 ≤ b k := fun k hk ↦
    (mul_nonneg (ha k hk) (pow_nonneg hE.le k)).trans (hab k hk)
  have he : 0 ≤ ksssErrorEnvelope E scale B time := by unfold ksssErrorEnvelope; positivity
  have hy := ksssConfigurationTrajectory_nonneg orders a E A time d 0 hA.le ht hp.le (ha d hd)
  have hcurr := ksssConfigurationTrajectory_error_product orders a b E A scale time B d 0
    (d - 1) 1 hE hA hs ht hclock ha hab hd (by omega) (by have hk := horders d hd; omega)
  simp only [pow_one] at hcurr
  have hH := ksssThreatTrajectory_bounds orders a b horders ha hab hE hA ht hclock
  have hH0 : 0 ≤ ksssThreatTrajectory orders a E A time := by linarith only [hx, hH.1]
  have hHabs : |ksssThreatTrajectory orders a E A time| ≤
      ksssThreatCoefficient orders b * ksssPairTrajectory orders a E A time := by
    rw [abs_of_nonneg hH0]
    exact hH.2
  have h := configuration_target_product_budget (alpha := 0) (y₀ := 0) (F₀ := 0)
    (beta := (d : ℝ)) le_rfl (Nat.cast_nonneg _) le_rfl hy he hx.le
    (ksssThreatCoefficient_nonneg orders b hb) (by simp) hcurr hHabs
  simpa only [zero_mul, zero_sub, abs_neg, zero_add, ksssConfigurationProductCoefficient] using h

end

end Erdos207
