/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSIndexedKernelConcentration

/-! # The simultaneous band-failure bound on the single stopped greedy law -/

namespace Erdos207

open Finset

noncomputable section

theorem probability_ksss_trajectory_failure_power
    {V : Type*} [Fintype V] [DecidableEq V]
    (q n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (Q₀ : Finset (Finset V)) (a : ℕ → ℝ)
    (E A eta N : ℝ) (B t R s b H j v : ℕ)
    (hN : 1 ≤ N) (ht : 4 ≤ t) (hscale : (t : ℝ) ^ R ≤ N) (hn : (n : ℝ) ≤ N ^ 2)
    (hratio : N / (t : ℝ) ^ b ≤ A / E)
    (hj : j ≤ H) (hH : v + (s + b * q) + 1 ≤ H) (hR : H + (s + b * q) + 2 ≤ R)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hQ₀ : ∀ P ∈ Q₀, P.card = 2)
    (hregular : KSSSInitialRegularity F S₀ q Q₀ a E A eta)
    (hfamily : ∀ C ∈ F, C ⊆ S₀.available)
    (hE : 0 < E) (hA : 0 ≤ A) (heta : 0 ≤ eta)
    (hbudget : 3 * eta * (A / E) + N / (2 * (t : ℝ) ^ s) ≤ N / (t : ℝ) ^ s)
    (hplus : KSSSIndexedKernelPowerBounds q n F active Q₀ a E A (N / (t : ℝ) ^ s) B 1 N t j v)
    (hminus : KSSSIndexedKernelPowerBounds q n F active Q₀ a E A (N / (t : ℝ) ^ s) B (-1) N t j v) :
    ((FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun w ↦ ¬ KSSSOnTrajectories F w.2 q (ksssResidualPairs Q₀ w.2) a E A
        (N / (t : ℝ) ^ s) B w.1.1) : ℝ) ≤
      2 * ((Fintype.card V : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ 3) * (1 / 2 : ℝ) ^ t := by
  classical
  let L := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀
  have havailable := timedStoppedGreedy_available_subset_initial n F active S₀ hInv₀
  have hbound := probability_not_ksssOnTrajectories_le_signed_tails L F q S₀
    (fun w ↦ w.2) (fun w ↦ ksssResidualPairs Q₀ w.2) (fun w ↦ (w.1.1 : ℝ))
    a E A (N / (t : ℝ) ^ s) B (ksssInitialMargin E A (N / (2 * (t : ℝ) ^ s)))
    (fun _ ↦ (1 / 2 : ℝ) ^ t) (fun _ ↦ (1 / 2 : ℝ) ^ t)
    (fun _ P hP ↦ hQ₀ P (mem_sdiff.mp hP).1)
    (fun index w hmass htracked ↦ hregular.initial_margin B hchosen₀ hfamily hE hA heta hbudget index
      (ksssTracked_initial_of_available_subset Q₀ (havailable w hmass) index htracked))
    (fun index ↦ by
      simpa only [ksssIndexedCenteredObservable, Nat.cast_zero, L] using
        probability_ksss_indexed_deviation_power_tail q n F active S₀ Q₀ a E A 1 N B t R s b H j v
          hN ht hscale hn hratio hj hH hR hInv₀ hchosen₀ hplus index)
    (fun index ↦ by
      simpa only [ksssIndexedCenteredObservable, Nat.cast_zero, L] using
        probability_ksss_indexed_deviation_power_tail q n F active S₀ Q₀ a E A (-1) N B t R s b H j v
          hN ht hscale hn hratio hj hH hR hInv₀ hchosen₀ hminus index)
  simp only [sum_const, card_univ, nsmul_eq_mul] at hbound
  have hcard : (Fintype.card (KSSSTrajectoryIndex V q) : ℝ) ≤
      (Fintype.card V : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ 3 := by
    exact_mod_cast card_ksssTrajectoryIndex_le V q
  calc
    _ ≤ (Fintype.card (KSSSTrajectoryIndex V q) : ℝ) * ((1 / 2 : ℝ) ^ t + (1 / 2 : ℝ) ^ t) := hbound
    _ ≤ ((Fintype.card V : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ 3) *
        ((1 / 2 : ℝ) ^ t + (1 / 2 : ℝ) ^ t) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

end

end Erdos207
