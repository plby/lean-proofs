/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSInitialMarginPower
import ErdosProblems.Erdos207.PowerStoppedConcentration
import ErdosProblems.Erdos207.PairExtensionTrajectory

/-! # Indexed selectors and initial tracking on the actual frozen support -/

namespace Erdos207

open Finset

noncomputable section

def ksssResidualPairs {V : Type*} [Fintype V] [DecidableEq V]
    (Q₀ : Finset (Finset V)) (S : GreedyStateOn V) : Finset (Finset V) := Q₀ \ chosenPairFinsets S

def ksssTrajectorySelectors {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) : KSSSTrajectoryIndex V q → TripleSystemOn V
  | .inl P => S.available \ availableTrianglesContainingPair S P.1
  | .inr (_, T) => S.available \ greedyClosedThreats F S T

theorem ksssTracked_residual_pair_iff
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (Q₀ : Finset (Finset V)) (S : GreedyStateOn V) (P : PairOn V) :
    ksssTrajectoryTracked S (ksssResidualPairs Q₀ S) (.inl P : KSSSTrajectoryIndex V q) ↔
      P.1 ∈ Q₀ ∧ PairUncovered P.1 S := by
  simp only [ksssTrajectoryTracked, ksssResidualPairs, mem_sdiff, PairUncovered]

theorem ksssTracked_initial_of_available_subset
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (Q₀ : Finset (Finset V)) {S₀ S : GreedyStateOn V}
    (hS : S.available ⊆ S₀.available) (i : KSSSTrajectoryIndex V q)
    (hi : ksssTrajectoryTracked S (ksssResidualPairs Q₀ S) i) :
    ksssTrajectoryTracked S₀ Q₀ i := by
  rcases i with P | ⟨i, T⟩
  · exact (mem_sdiff.mp hi).1
  · exact hS hi

theorem ksssCenteredTrajectoryObservable_increment
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (F : ForbiddenFamilyOn V) (a : ℕ → ℝ) (E A scale time sigma : ℝ) (B : ℕ)
    (S S' : GreedyStateOn V) (i : KSSSTrajectoryIndex V q) :
    ksssCenteredTrajectoryObservable F a E A scale B sigma (time + 1) S' i -
        ksssCenteredTrajectoryObservable F a E A scale B sigma time S i =
      sigma * ((ksssTrajectoryValue F S' i - ksssTrajectoryValue F S i) -
        (ksssTrajectoryTarget a E A (time + 1) i - ksssTrajectoryTarget a E A time i)) -
          (ksssTrajectoryError E A scale B (time + 1) i - ksssTrajectoryError E A scale B time i) := by
  unfold ksssCenteredTrajectoryObservable
  ring

theorem pairUncovered_of_chosen_empty
    {V : Type*} [Fintype V] [DecidableEq V] (P : Finset V) (S : GreedyStateOn V)
    (hchosen : S.chosen = ∅) : PairUncovered P S := by
  intro hP
  obtain ⟨T, hT, _, _⟩ := mem_chosenPairFinsets_iff.mp hP
  rw [hchosen] at hT
  exact notMem_empty _ hT

theorem timedStoppedGreedy_available_subset_initial
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (hInv₀ : GreedyInvariant F S₀) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).SupportedOn
      (fun w ↦ w.2.available ⊆ S₀.available) := by
  have h := FiniteLaw.timedStoppedProcessLaw_supported n (fun _ ↦ greedyKernel F) active S₀
    (pairTrajectoryInvariant_initial hInv₀)
    (fun _ _ _ hS ↦ greedyKernel_supported_pairTrajectoryInvariant hS)
  intro w hw
  exact (h w hw).2

theorem probability_ksssTracked_of_not_initial_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (Q₀ : Finset (Finset V)) (hInv₀ : GreedyInvariant F S₀)
    (i : KSSSTrajectoryIndex V q) (P : FiniteLaw.TimedState (GreedyStateOn V) n → Prop)
    (hi : ¬ ksssTrajectoryTracked S₀ Q₀ i) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun w ↦ ksssTrajectoryTracked w.2 (ksssResidualPairs Q₀ w.2) i ∧ P w) = 0 := by
  let L := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀
  have hsub := timedStoppedGreedy_available_subset_initial n F active S₀ hInv₀
  have hzero := L.probability_mono_of_supported
    (P := fun w ↦ ksssTrajectoryTracked w.2 (ksssResidualPairs Q₀ w.2) i ∧ P w)
    (Q := fun _ ↦ False) hsub
    (fun _ hS hw ↦ hi (ksssTracked_initial_of_available_subset Q₀ hS i hw.1))
  apply le_antisymm
  · simpa only [FiniteLaw.probability_false] using hzero
  · exact zero_le

end

end Erdos207
