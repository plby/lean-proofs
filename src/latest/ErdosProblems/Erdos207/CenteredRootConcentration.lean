/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CenteredStepBounds
import ErdosProblems.Erdos207.RootObservableConcentration

/-! # Root-survival concentration from raw drift and deterministic trajectory budgets -/

namespace Erdos207

open Finset

noncomputable section

theorem probability_timedStoppedGreedy_centered_root_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (root : TripleOn V) (X : GreedyStateOn V → ℝ)
    (f e slope D C : ℕ → ℝ) (σ J A v theta a : ℝ)
    (hInv₀ : GreedyInvariant F S₀) (hroot₀ : root ∈ S₀.available)
    (hσ : |σ| = 1) (hJ : 0 ≤ J) (hA : 0 ≤ A) (hv : 0 ≤ v)
    (htheta : 0 < theta) (hthetaM : theta * (J + A) ≤ 1)
    (hTaylor : ∀ i, i < n → |f (i + 1) - f i - slope i| ≤ C i)
    (hGrowth : ∀ i, i < n → D i + C i ≤ e (i + 1) - e i)
    (hTime : ∀ i, i < n → |f (i + 1) - f i| + |e (i + 1) - e i| ≤ A)
    (hJump : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → root ∈ S.available →
      ∀ T ∈ S.available \ greedyClosedThreats F S root, |X (greedyStep F S T) - X S| ≤ J)
    (hDrift : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → root ∈ S.available →
      ∀ hR : (S.available \ greedyClosedThreats F S root).Nonempty,
        |(restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hR).expectationReal
          (fun S' ↦ X S' - X S) - slope i| ≤ D i)
    (hSecond : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → root ∈ S.available →
      ∀ hR : (S.available \ greedyClosedThreats F S root).Nonempty,
        (restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hR).expectationReal
          (fun S' ↦ (X S' - X S) ^ 2) ≤ v) :
    ((FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ root ∈ z.2.available ∧ a ≤
        (σ * (X z.2 - f z.1.1) - e z.1.1) - (σ * (X S₀ - f 0) - e 0)) : ℝ) ≤
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * (2 * v + 2 * A ^ 2)) := by
  let obs := fun i S ↦ σ * (X S - f i) - e i
  have hinc (i : ℕ) (S S' : GreedyStateOn V) :
      obs (i + 1) S' - obs i S =
        σ * ((X S' - X S) - (f (i + 1) - f i)) - (e (i + 1) - e i) := by
    dsimp only [obs]
    ring
  apply probability_timedStoppedGreedy_root_observable_le_exp n F active S₀ root obs
    (J + A) theta a (2 * v + 2 * A ^ 2) hInv₀ hroot₀
  · intro i hi S hS hactive hroot T hT
    rw [hinc]
    have hj := hJump i hi S hS hactive hroot T hT
    have ht := hTime i hi
    calc
      _ ≤ |σ * ((X (greedyStep F S T) - X S) - (f (i + 1) - f i)) - (e (i + 1) - e i)| :=
        le_abs_self _
      _ ≤ |X (greedyStep F S T) - X S| + |f (i + 1) - f i| + |e (i + 1) - e i| :=
        centered_step_abs_le _ _ _ _ hσ
      _ ≤ _ := by linarith
  · intro i hi S hS hactive hroot hR
    simp_rw [hinc]
    exact centered_step_drift_nonpos _ (fun S' ↦ X S' - X S)
      σ (f (i + 1) - f i) (e (i + 1) - e i) (slope i) (D i) (C i) hσ
      (hDrift i hi S hS hactive hroot hR) (hTaylor i hi) (hGrowth i hi)
  · intro i hi S hS hactive hroot hR
    simp_rw [hinc]
    have hb := centered_step_secondMoment_le _ (fun S' ↦ X S' - X S)
      σ (f (i + 1) - f i) (e (i + 1) - e i) v hσ (hSecond i hi S hS hactive hroot hR)
    exact hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (hTime i hi) 2) (by norm_num)))
  · positivity
  · exact htheta
  · exact hthetaM
  · positivity

end

end Erdos207
