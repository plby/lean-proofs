/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ConfigurationDriftTrajectoryError
import ErdosProblems.Erdos207.CoupledDriftBudgetArithmetic
import ErdosProblems.Erdos207.RootSelectorDenominatorBudget

/-! # Explicit source-scale bounds for the configuration kernel drift -/

namespace Erdos207

open Finset

noncomputable section

def configurationDriftScaleCoefficient
    (alpha beta F G k ell W C delta T : ℝ) : ℝ :=
  6 * (2 * G + F * (beta * k + ell)) + 6 * (alpha * W + beta * C) + 18 * (delta * T)

theorem restrictedGreedyKernel_configuration_succ_source_scale
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (root : TripleOn V) (d c K : ℕ)
    (L x e h H y₀ y₁ eprev Fcoef Gcoef k W C Tcoef : ℝ)
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hR : (S.available \ greedyClosedThreats F S root).Nonempty)
    (hcard : ∀ E ∈ J, E.card = d + 1) (hpack : ∀ E ∈ J, IsPackingOn E) (hcd : c + 2 ≤ d)
    (hL : 0 < L) (hx : 0 < x) (hh : 0 ≤ h)
    (hF : 0 ≤ Fcoef) (hG : 0 ≤ Gcoef) (hk : 0 ≤ k) (hW : 0 ≤ W)
    (hC : 0 ≤ C) (hT : 0 ≤ Tcoef)
    (he : e ≤ x / 4) (hlarge : 12 * (C + k) ≤ L) (hxe : x ≤ L * e)
    (havailable : |(S.available.card : ℝ) - L * x / 3| ≤ L * e / 3)
    (hH : |H| ≤ C * x)
    (hthreat : ∀ U ∈ S.available, |((greedyClosedThreats F S U).card : ℝ) - H| ≤ k * e)
    (hinter : ∀ U ∈ S.available, ∀ U' ∈ S.available, U ≠ U' → (U.1 ∩ U'.1).card ≤ 1 →
      (greedyClosedThreats F S U ∩ greedyClosedThreats F S U').card ≤ K)
    (hK : (K : ℝ) ≤ e)
    (hgain : (∑ E ∈ greedyConfigurationClass J S root c,
      ((greedyConfigurationRedundantWitnesses F S E).card : ℝ)) ≤ Gcoef * x * h)
    (hprev : |((greedyConfigurationClass J S root c).card : ℝ) - y₀| ≤ eprev)
    (hcurr : |((greedyConfigurationClass J S root (c + 1)).card : ℝ) - y₁| ≤ h)
    (hve : (greedyConfigurationClass J S root (c + 1)).card * e ≤ Fcoef * x * h)
    (heprev : eprev ≤ W * x * h)
    (htarget : |(d - c : ℕ) * y₀ - (d - (c + 1) : ℕ) * y₁ * H| * e ≤ Tcoef * x ^ 2 * h) :
    let R := S.available \ greedyClosedThreats F S root
    let alpha : ℝ := (d - c : ℕ)
    let beta : ℝ := (d - (c + 1) : ℕ)
    let ell : ℝ := ((d - (c + 1)) + (d - (c + 1)).choose 2 : ℕ)
    |(restrictedGreedyKernel F S R hR).expectationReal
        (fun S' ↦ ((greedyConfigurationClass J S' root (c + 1)).card : ℝ) -
          (greedyConfigurationClass J S root (c + 1)).card) - (alpha * y₀ - beta * y₁ * H) / (L * x / 3)| ≤
      configurationDriftScaleCoefficient alpha beta Fcoef Gcoef k ell W C (1 / 3 + C + k) Tcoef * h / L := by
  dsimp only
  have hdenom := root_selector_denominator_budget F S root L x e H C k hL hx hC hk he hlarge
    havailable (hthreat root hroot) hH hxe
  have hraw := restrictedGreedyKernel_configuration_drift_succ_trajectory_error root c d K H (k * e)
    (Gcoef * x * h) y₀ y₁ eprev h (L * x / 3) ((1 / 3 + C + k) * L * e)
    hS hroot hR hcard hpack hcd hinter hthreat hgain hprev hcurr (by positivity) hdenom.2
  have hJ : ((((d - (c + 1)) + (d - (c + 1)).choose 2) * K : ℕ) : ℝ) ≤
      (((d - (c + 1)) + (d - (c + 1)).choose 2 : ℕ) : ℝ) * e := by
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg _)
  exact hraw.trans (configuration_drift_error_coupled_scale (delta := 1 / 3 + C + k)
    hL hx hh (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hF hG hk (Nat.cast_nonneg _) hW hC
    (by positivity) hT hdenom.1 hve le_rfl le_rfl hJ heprev hH le_rfl htarget)

theorem restrictedGreedyKernel_configuration_zero_source_scale
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (root : TripleOn V) (d K : ℕ)
    (L x e h H y Fcoef k C Tcoef : ℝ)
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hR : (S.available \ greedyClosedThreats F S root).Nonempty)
    (hcard : ∀ E ∈ J, E.card = d + 1) (hpack : ∀ E ∈ J, IsPackingOn E)
    (hL : 0 < L) (hx : 0 < x) (hh : 0 ≤ h)
    (hF : 0 ≤ Fcoef) (hk : 0 ≤ k) (hC : 0 ≤ C) (hT : 0 ≤ Tcoef)
    (he : e ≤ x / 4) (hlarge : 12 * (C + k) ≤ L) (hxe : x ≤ L * e)
    (havailable : |(S.available.card : ℝ) - L * x / 3| ≤ L * e / 3)
    (hH : |H| ≤ C * x)
    (hthreat : ∀ U ∈ S.available, |((greedyClosedThreats F S U).card : ℝ) - H| ≤ k * e)
    (hinter : ∀ U ∈ S.available, ∀ U' ∈ S.available, U ≠ U' → (U.1 ∩ U'.1).card ≤ 1 →
      (greedyClosedThreats F S U ∩ greedyClosedThreats F S U').card ≤ K)
    (hK : (K : ℝ) ≤ e)
    (hcurr : |((greedyConfigurationClass J S root 0).card : ℝ) - y| ≤ h)
    (hve : (greedyConfigurationClass J S root 0).card * e ≤ Fcoef * x * h)
    (htarget : |(d : ℝ) * y * H| * e ≤ Tcoef * x ^ 2 * h) :
    let R := S.available \ greedyClosedThreats F S root
    |(restrictedGreedyKernel F S R hR).expectationReal
        (fun S' ↦ ((greedyConfigurationClass J S' root 0).card : ℝ) -
          (greedyConfigurationClass J S root 0).card) + (d : ℝ) * y * H / (L * x / 3)| ≤
      configurationDriftScaleCoefficient 0 d Fcoef 0 k (d + d.choose 2 : ℕ) 0 C
        (1 / 3 + C + k) Tcoef * h / L := by
  dsimp only
  have hdenom := root_selector_denominator_budget F S root L x e H C k hL hx hC hk he hlarge
    havailable (hthreat root hroot) hH hxe
  have hraw := restrictedGreedyKernel_configuration_drift_zero_trajectory_error root d K H (k * e)
    y h (L * x / 3) ((1 / 3 + C + k) * L * e)
    hS hroot hR hcard hpack hinter hthreat hcurr (by positivity) hdenom.2
  have hJ : (((d + d.choose 2) * K : ℕ) : ℝ) ≤ ((d + d.choose 2 : ℕ) : ℝ) * e := by
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg _)
  have hscaled := configuration_drift_error_coupled_scale
    (alpha := 0) (G := 0) (Z := 0) (W := 0) (eprev := 0)
    (delta := 1 / 3 + C + k) (epsilonA := (1 / 3 + C + k) * L * e)
    hL hx hh (Nat.cast_nonneg _) le_rfl (Nat.cast_nonneg d) hF le_rfl hk
    (Nat.cast_nonneg _) le_rfl hC (by positivity) hT hdenom.1 hve
    (by simp) le_rfl hJ (by simp) hH le_rfl htarget
  exact hraw.trans (by simpa only [zero_mul, mul_zero, zero_add, configurationDriftScaleCoefficient] using hscaled)

end

end Erdos207
