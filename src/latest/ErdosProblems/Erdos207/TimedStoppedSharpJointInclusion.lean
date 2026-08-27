/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TimedStoppedJointInclusion
import ErdosProblems.Erdos207.SharpInhomogeneousJointInclusion

/-! # Joint inclusion without a factorial loss for the stopped greedy law -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem timedStoppedGreedyProcess_probability_subset_chosen_le_sharp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (hD : 0 < D)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (S₀ : GreedyStateOn V) (U : TripleSystemOn V)
    (hdisjoint : Disjoint U S₀.chosen) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ U ⊆ z.2.chosen) ≤
      ((n : ℝ≥0) * (D : ℝ≥0)⁻¹) ^ U.card := by
  let z₀ : FiniteLaw.TimedState (GreedyStateOn V) n := (⟨0, by omega⟩, S₀)
  have h := evolveKernels_probability_subset_le_pointWeights_sharp
    (fun _i z ↦ FiniteLaw.timedStoppedKernel n (fun _ ↦ greedyKernel F) active z)
    (fun z : FiniteLaw.TimedState (GreedyStateOn V) n ↦ z.2.chosen)
    (fun _i _T ↦ (D : ℝ≥0)⁻¹)
    (fun _i ↦ timedStoppedGreedyKernel_monotone_singleInsertion n F active)
    (fun _i z T hT ↦ timedStoppedGreedyKernel_probability_new_triangle_le
      n F active D hD hfloor z T hT)
    z₀ U hdisjoint n
  simpa [FiniteLaw.timedStoppedProcessLaw, z₀, setWeight, cumulativePointHazard] using h

theorem timedStoppedGreedyProcess_probability_subset_le_scaled_weight
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (D m : ℕ) (p w : ℝ≥0) (hD : 0 < D) (hw : 1 ≤ w)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * p)
    (S₀ : GreedyStateOn V) (U : TripleSystemOn V)
    (hdisjoint : Disjoint U S₀.chosen) (hcard : U.card ≤ m) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ U ⊆ z.2.chosen) ≤ w ^ m * p ^ U.card := by
  refine (timedStoppedGreedyProcess_probability_subset_chosen_le_sharp
    n F active D hD hfloor S₀ U hdisjoint).trans ?_
  calc
    _ ≤ (w * p) ^ U.card := pow_le_pow_left' hratio U.card
    _ = w ^ U.card * p ^ U.card := mul_pow _ _ _
    _ ≤ w ^ m * p ^ U.card :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right' hw hcard) zero_le

end

end Erdos207
