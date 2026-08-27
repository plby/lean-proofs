/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.StoppedGreedyStateLaw
import ErdosProblems.Erdos207.KSSSRefinedStopping

/-! # The stopped clock is recoverable from the chosen-set cardinality -/

namespace Erdos207

open Finset

noncomputable section

theorem stoppedGreedyStateLaw_supported_terminal
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop) (S₀ : GreedyStateOn V)
    (hInv : GreedyInvariant F S₀) (hchosen : S₀.chosen = ∅)
    (havailable : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → S.available.Nonempty) :
    (stoppedGreedyStateLaw n F active S₀).SupportedOn
      (fun S ↦ GreedyInvariant F S ∧ GreedyContainedIn S₀.available S ∧ S.chosen.card ≤ n ∧
        (S.chosen.card = n ∨ ¬ active S.chosen.card S)) := by
  have htime := timedStoppedGreedy_supported_contained_counter n F active S₀ hInv hchosen havailable
  have hterm := FiniteLaw.timedStoppedProcessLaw_supported_terminal n (fun _ ↦ greedyKernel F) active S₀
  have hs : (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).SupportedOn
      (fun u ↦ GreedyInvariant F u.2 ∧ GreedyContainedIn S₀.available u.2 ∧ u.2.chosen.card ≤ n ∧
        (u.2.chosen.card = n ∨ ¬ active u.2.chosen.card u.2)) := by
    intro u hu
    have hc := htime u hu
    refine ⟨hc.1.1, hc.1.2, ?_, ?_⟩
    · rw [hc.2]
      exact Nat.le_of_lt_succ u.1.isLt
    · simpa only [hc.2] using hterm u hu
  exact hs.map Prod.snd (fun _ h ↦ h)

theorem stoppedGreedyStateLaw_probability_indexed
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop) (S₀ : GreedyStateOn V)
    (hInv : GreedyInvariant F S₀) (hchosen : S₀.chosen = ∅)
    (havailable : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → S.available.Nonempty)
    (B : ℕ → GreedyStateOn V → Prop) :
    (stoppedGreedyStateLaw n F active S₀).probability (fun S ↦ B S.chosen.card S) =
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability (fun u ↦ B u.1.1 u.2) := by
  rw [stoppedGreedyStateLaw, FiniteLaw.probability_map]
  have htime := timedStoppedGreedy_supported_contained_counter n F active S₀ hInv hchosen havailable
  apply le_antisymm
  · apply FiniteLaw.probability_mono_of_supported _ htime
    intro u hu hB
    simpa only [hu.2] using hB
  · apply FiniteLaw.probability_mono_of_supported _ htime
    intro u hu hB
    simpa only [hu.2] using hB

theorem KSSSPowerParameters.state_trajectory_failure_of_active_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q n b B k t Rmin : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (Q₀ : Finset (Finset V)) (S₀ : GreedyStateOn V) (eta : ℝ)
    (active : ℕ → GreedyStateOn V → Prop)
    (hactive : ∀ i S, active i S → KSSSPowerActive F Q₀ q b B k t a E A i S)
    (hInv : GreedyInvariant F S₀) (hchosen : S₀.chosen = ∅)
    (hQ₀ : ∀ Q ∈ Q₀, Q.card = 2) (hregular : KSSSInitialRegularity F S₀ q Q₀ a E A eta)
    (hfamily : ∀ C ∈ F, C ⊆ S₀.available) (heta : 0 ≤ eta)
    (hetaSmall : eta ≤ 1 / (6 * (t : ℝ) ^ ksssPowerErrorExponent b B)) :
    ((stoppedGreedyStateLaw n F active S₀).probability
      (fun S ↦ ¬ KSSSOnTrajectories F S q (ksssResidualPairs Q₀ S) a E A
        ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B S.chosen.card) : ℝ) ≤
      2 * ((Fintype.card V : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ 3) * (1 / 2 : ℝ) ^ t := by
  let Bad := fun (i : ℕ) (S : GreedyStateOn V) ↦ ¬ KSSSOnTrajectories F S q (ksssResidualPairs Q₀ S) a E A
    ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B i
  have heq := stoppedGreedyStateLaw_probability_indexed n F active S₀ hInv hchosen
    (fun i hi S hS ha ↦ (P.kernelBounds Q₀ 1 (by norm_num)).available i hi S hS (hactive i S ha)) Bad
  have hfail := P.trajectory_failure_of_active_le Q₀ S₀ eta active hactive hInv hchosen hQ₀ hregular hfamily heta hetaSmall
  rw [← heq] at hfail
  exact hfail

end

end Erdos207
