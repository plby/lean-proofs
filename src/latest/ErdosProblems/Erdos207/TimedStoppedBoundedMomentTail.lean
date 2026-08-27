/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.BoundedMomentPowerBudget
import ErdosProblems.Erdos207.TimedStoppedSharpJointInclusion

/-! # Growing-moment tails for an actual stopped constrained greedy law -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem timedStoppedGreedy_dominatedConfigurationTail
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (rem : I → TripleSystemOn V)
    (X : GreedyStateOn V → ℝ≥0) (d s : ℕ) (p w κ K : ℝ≥0)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hD : 0 < D) (hw : 1 ≤ w) (hK : 0 < K)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * p)
    (hdom : ∀ S, GreedyInvariant F S → X S ≤ selectedCount rem S.chosen)
    (hcard : ∀ u, (rem u).card ≤ d) (hκ : HasExtensionBound rem (fun _ ↦ p) κ)
    (hcut : 2 * (w ^ d * ((boundedIntersectionMomentCoefficient d s : ℝ≥0) * κ)) ≤ K) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ K ≤ X z.2) ≤ (1 / 2 : ℝ≥0) ^ s := by
  let L := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀
  have hInv : L.SupportedOn (fun z ↦ GreedyInvariant F z.2) :=
    FiniteLaw.timedStoppedProcessLaw_supported n (fun _ ↦ greedyKernel F) active S₀
      hInv₀ (fun _ _ _ hS ↦ greedyKernel_supported hS)
  refine dominatedConfigurationTailBound_bounded_intersections L rem
    (fun z : FiniteLaw.TimedState (GreedyStateOn V) n ↦ z.2.chosen)
    (fun z ↦ X z.2) (fun _ ↦ p) w κ K (fun z hz ↦ hdom z.2 (hInv z hz)) hcard hκ hK ?_ hcut
  intro U hU
  simpa only [setWeight, prod_const] using
    timedStoppedGreedyProcess_probability_subset_le_scaled_weight n F active D (s * d)
      p w hD hw hfloor hratio S₀ U (by simp [hchosen₀]) hU

theorem timedStoppedGreedy_dominatedConfigurationTail_power
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (rem : I → TripleSystemOn V)
    (X : GreedyStateOn V → ℝ≥0) (d s a b : ℕ) (p t w κ A Z : ℝ≥0)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hD : 0 < D) (hw : 1 ≤ w) (hs : 1 ≤ s) (hst : (s : ℝ≥0) ≤ t) (hZ : 0 < Z)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * p)
    (hdom : ∀ S, GreedyInvariant F S → X S ≤ selectedCount rem S.chosen)
    (hcard : ∀ u, (rem u).card ≤ d) (hκ : HasExtensionBound rem (fun _ ↦ p) κ)
    (hwscale : w ≤ t ^ b) (hκscale : κ ≤ A * Z * t ^ a)
    (hconst : 2 * (((d + 1) ^ (d + 1) : ℕ) : ℝ≥0) * A ≤ t) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ Z * t ^ (a + d * (b + 1) + 1) ≤ X z.2) ≤ (1 / 2 : ℝ≥0) ^ s := by
  have ht : 0 < t := lt_of_lt_of_le (by exact_mod_cast (show 0 < s by omega)) hst
  exact timedStoppedGreedy_dominatedConfigurationTail n F active D S₀ rem X d s p w κ _
    hInv₀ hchosen₀ hD hw (mul_pos hZ (pow_pos ht _)) hfloor hratio hdom hcard hκ
    (boundedMoment_power_cutoff d s a b t w κ A Z hs hst hwscale hκscale hconst)

end

end Erdos207
