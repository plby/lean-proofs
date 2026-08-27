/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UncoveredPairKernel
import ErdosProblems.Erdos207.EnvelopeStoppedGreedy

/-! # Stopped pair concentration while the pair remains uncovered -/

namespace Erdos207

open Finset

noncomputable section

theorem probability_timedStoppedGreedy_uncovered_pair_observable_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (P : Finset V) (hP : P.card = 2)
    (obs : ℕ → GreedyStateOn V → ℝ) (M theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀) (hpair₀ : PairUncovered P S₀)
    (havailable : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → PairUncovered P S → S.available.Nonempty)
    (hjump : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → PairUncovered P S →
      ∀ T ∈ S.available \ availableTrianglesContainingPair S P,
        obs (i + 1) (greedyStep F S T) - obs i S ≤ M)
    (hdrift : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → PairUncovered P S →
      ∀ hR : (S.available \ availableTrianglesContainingPair S P).Nonempty,
        (restrictedGreedyKernel F S (S.available \ availableTrianglesContainingPair S P) hR).expectationReal
          (fun S' ↦ obs (i + 1) S' - obs i S) ≤ 0)
    (hsecond : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → PairUncovered P S →
      ∀ hR : (S.available \ availableTrianglesContainingPair S P).Nonempty,
        (restrictedGreedyKernel F S (S.available \ availableTrianglesContainingPair S P) hR).expectationReal
          (fun S' ↦ (obs (i + 1) S' - obs i S) ^ 2) ≤ v)
    (hM : 0 ≤ M) (htheta : 0 < theta) (hthetaM : theta * M ≤ 1) (hv : 0 ≤ v) :
    ((FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ PairUncovered P z.2 ∧ a ≤ obs z.1.1 z.2 - obs 0 S₀) : ℝ) ≤
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v) := by
  classical
  apply FiniteLaw.probability_timedStoppedProcess_alive_deviation_ge_le_exp
    (P := GreedyInvariant F) (alive := PairUncovered P)
    n (fun _ ↦ greedyKernel F) active obs S₀ theta M a v hInv₀ hpair₀
    htheta hM hthetaM hv
    (fun _ _ S hS ↦ greedyKernel_supported hS)
    (fun _ _ S _ hdead ↦ greedyKernel_supported_pairCovered F S P hdead)
  · intro i hi S hS hactive hpair S' hmass _ halive
    obtain ⟨T, hT, rfl⟩ := greedyKernel_supported_step_of_nonempty F S
      (havailable i hi S hS hactive hpair) S' hmass
    exact hjump i hi S hS hactive hpair T
      (mem_sdiff.mpr ⟨hT, (pairUncovered_greedyStep_iff hP hpair hT).mp halive⟩)
  · intro i hi S hS hactive hpair
    exact greedyKernel_expectationReal_pairUncovered_le_of_restricted P hP hpair
      (havailable i hi S hS hactive hpair) (fun S' ↦ obs (i + 1) S' - obs i S) 0 le_rfl
      (hdrift i hi S hS hactive hpair)
  · intro i hi S hS hactive hpair
    exact greedyKernel_expectationReal_pairUncovered_le_of_restricted P hP hpair
      (havailable i hi S hS hactive hpair) (fun S' ↦ (obs (i + 1) S' - obs i S) ^ 2) v hv
      (hsecond i hi S hS hactive hpair)

end

end Erdos207
