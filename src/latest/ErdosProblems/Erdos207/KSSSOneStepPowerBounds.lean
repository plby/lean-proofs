/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSIndexedKernelConcentration
import ErdosProblems.Erdos207.KSSSPowerExponentChoice

/-! # One-state centered kernel estimates for a tracked index -/

namespace Erdos207

open Finset

noncomputable section

structure KSSSOneStepPowerBounds
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (index : KSSSTrajectoryIndex V q)
    (a : ℕ → ℝ) (E A scale : ℝ) (B : ℕ) (sigma time N : ℝ) (t b k : ℕ) : Prop where
  jump : ∀ T ∈ ksssTrajectorySelectors F S index,
    |ksssCenteredTrajectoryObservable F a E A scale B sigma (time + 1) (greedyStep F S T) index -
      ksssCenteredTrajectoryObservable F a E A scale B sigma time S index| ≤
        N ^ ksssTrajectoryDimension index * (t : ℝ) ^ ksssPowerJumpExponent b k
  drift : ∀ hSel : (ksssTrajectorySelectors F S index).Nonempty,
    (restrictedGreedyKernel F S (ksssTrajectorySelectors F S index) hSel).expectationReal
      (fun S' ↦ ksssCenteredTrajectoryObservable F a E A scale B sigma (time + 1) S' index -
        ksssCenteredTrajectoryObservable F a E A scale B sigma time S index) ≤ 0
  second : ∀ hSel : (ksssTrajectorySelectors F S index).Nonempty,
    (restrictedGreedyKernel F S (ksssTrajectorySelectors F S index) hSel).expectationReal
      (fun S' ↦ (ksssCenteredTrajectoryObservable F a E A scale B sigma (time + 1) S' index -
        ksssCenteredTrajectoryObservable F a E A scale B sigma time S index) ^ 2) ≤
          N ^ (2 * ksssTrajectoryDimension index) / N * (t : ℝ) ^ ksssPowerVarianceExponent b k

theorem ksssIndexedKernelPowerBounds_of_oneStep
    {V : Type*} [Fintype V] [DecidableEq V] (q n t b k : ℕ)
    (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop) (Q₀ : Finset (Finset V))
    (a : ℕ → ℝ) (E A scale : ℝ) (B : ℕ) (sigma N : ℝ)
    (havailable : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → S.available.Nonempty)
    (hstep : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S →
      ∀ index : KSSSTrajectoryIndex V q, ksssTrajectoryTracked S (ksssResidualPairs Q₀ S) index →
        KSSSOneStepPowerBounds F S index a E A scale B sigma i N t b k) :
    KSSSIndexedKernelPowerBounds q n F active Q₀ a E A scale B sigma N t
      (ksssPowerJumpExponent b k) (ksssPowerVarianceExponent b k) := by
  refine ⟨havailable, ?_, ?_, ?_⟩
  · intro i hi S hS hactive index htracked T hT
    have h := (hstep i hi S hS hactive index htracked).jump T hT
    simp only [ksssIndexedCenteredObservable, Nat.cast_add, Nat.cast_one]
    exact (le_abs_self _).trans h
  · intro i hi S hS hactive index htracked hSel
    simpa only [ksssIndexedCenteredObservable, Nat.cast_add, Nat.cast_one] using
      (hstep i hi S hS hactive index htracked).drift hSel
  · intro i hi S hS hactive index htracked hSel
    simpa only [ksssIndexedCenteredObservable, Nat.cast_add, Nat.cast_one] using
      (hstep i hi S hS hactive index htracked).second hSel

end

end Erdos207
