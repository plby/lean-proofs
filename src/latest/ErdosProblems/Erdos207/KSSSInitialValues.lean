/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSSourceNormalization
import ErdosProblems.Erdos207.KSSSErrorEnvelopeGrowth
import ErdosProblems.Erdos207.GreedyConfigurationClasses

/-! # Exact initial values and the empty-chosen configuration classes -/

namespace Erdos207

open Finset

noncomputable section

theorem ksssEdgeDensity_zero (E₀ : ℝ) (hE : E₀ ≠ 0) : ksssEdgeDensity E₀ 0 = 1 := by
  simp [ksssEdgeDensity, hE]

theorem ksssPoissonExponent_zero
    (orders : Finset ℕ) (a : ℕ → ℝ) (horders : ∀ d ∈ orders, 1 ≤ d) :
    ksssPoissonExponent orders a 0 = 0 := by
  apply sum_eq_zero
  intro d hd
  simp only [zero_pow (show d ≠ 0 by have h := horders d hd; omega), mul_zero]

theorem ksssAvailableTrajectory_zero
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ : ℝ) (hE : E₀ ≠ 0)
    (horders : ∀ d ∈ orders, 1 ≤ d) :
    ksssAvailableTrajectory orders a E₀ A₀ 0 = A₀ := by
  simp [ksssAvailableTrajectory, ksssEdgeDensity_zero E₀ hE, ksssPoissonExponent_zero orders a horders]

theorem ksssPairTrajectory_zero
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ : ℝ) (hE : E₀ ≠ 0)
    (horders : ∀ d ∈ orders, 1 ≤ d) :
    ksssPairTrajectory orders a E₀ A₀ 0 = 3 * A₀ / E₀ := by
  simp [ksssPairTrajectory, ksssAvailableTrajectory_zero orders a E₀ A₀ hE horders,
    ksssEdgeDensity_zero E₀ hE]

theorem ksssConfigurationTrajectory_zero_zero
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ : ℝ) (d : ℕ) (hE : E₀ ≠ 0)
    (horders : ∀ k ∈ orders, 1 ≤ k) :
    ksssConfigurationTrajectory orders a E₀ A₀ d 0 0 = a d * A₀ ^ d := by
  simp [ksssConfigurationTrajectory, ksssAvailableTrajectory_zero orders a E₀ A₀ hE horders]

theorem ksssConfigurationTrajectory_zero_of_chosen_pos
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ : ℝ) (d c : ℕ) (hc : 0 < c) :
    ksssConfigurationTrajectory orders a E₀ A₀ d c 0 = 0 := by
  simp [ksssConfigurationTrajectory, zero_pow (Nat.ne_of_gt hc)]

theorem ksssErrorEnvelope_zero
    (E₀ scale : ℝ) (B : ℕ) (hE : E₀ ≠ 0) :
    ksssErrorEnvelope E₀ scale B 0 = scale := by
  simp [ksssErrorEnvelope, ksssEdgeDensity_zero E₀ hE]

theorem ksssConfigurationErrorEnvelope_zero
    (E₀ A₀ scale : ℝ) (B z : ℕ) (hE : E₀ ≠ 0) :
    ksssConfigurationErrorEnvelope E₀ A₀ scale B z 0 = scale * (A₀ / E₀) ^ z := by
  simp [ksssConfigurationErrorEnvelope, ksssErrorEnvelope_zero E₀ scale B hE,
    ksssEdgeDensity_zero E₀ hE]

theorem ksssSourceCoefficient_initial_target
    (A₀ : ℝ) (J : ℕ → ℝ) (d : ℕ) (hA : A₀ ≠ 0) :
    ksssSourceCoefficient A₀ J d * A₀ ^ d = (d + 1 : ℕ) * J (d + 3) / A₀ := by
  unfold ksssSourceCoefficient
  rw [pow_succ]
  field_simp

theorem greedyConfigurationClass_empty_of_initial_chosen
    {V : Type*} [Fintype V] [DecidableEq V]
    (J : ForbiddenFamilyOn V) (S : GreedyStateOn V) (root : TripleOn V) (c : ℕ)
    (hchosen : S.chosen = ∅) (hc : 0 < c) :
    greedyConfigurationClass J S root c = ∅ := by
  ext C
  simp [mem_greedyConfigurationClass, hchosen, Ne.symm (Nat.ne_of_gt hc)]

theorem greedyConfigurationClass_initial_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (J : ForbiddenFamilyOn V) (S : GreedyStateOn V) (root : TripleOn V)
    (hchosen : S.chosen = ∅) (havailable : ∀ C ∈ J, C ⊆ S.available) :
    greedyConfigurationClass J S root 0 = J.filter (fun C ↦ root ∈ C) := by
  ext C
  simp only [mem_greedyConfigurationClass, hchosen, inter_empty, card_empty, empty_union,
    true_and, mem_filter]
  constructor
  · rintro ⟨hC, hroot, _⟩
    exact ⟨hC, hroot⟩
  · rintro ⟨hC, hroot⟩
    exact ⟨hC, hroot, havailable C hC⟩

theorem initial_configuration_margin
    {y eta w margin scale : ℝ} (d : ℕ) (hd : 1 ≤ d)
    (heta : 0 ≤ eta) (hw : 0 ≤ w) (herror : |y| ≤ eta * w ^ d)
    (hbudget : 3 * eta * w + margin ≤ scale) :
    |y| + margin * w ^ (d - 1) ≤ scale * w ^ (d - 1) := by
  have he : eta * w + margin ≤ scale := by nlinarith [mul_nonneg heta hw]
  have hmul := mul_le_mul_of_nonneg_right he (pow_nonneg hw (d - 1))
  have hpow : w ^ d = w ^ (d - 1) * w := by rw [← pow_succ, Nat.sub_add_cancel hd]
  rw [hpow] at herror
  nlinarith only [herror, hmul]

end

end Erdos207
