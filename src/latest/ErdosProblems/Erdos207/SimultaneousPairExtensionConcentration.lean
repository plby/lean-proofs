/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpPairConcentration
import ErdosProblems.Erdos207.AbsorberWeightBudget
import ErdosProblems.Erdos207.AlivePairJump

/-!
# Simultaneous pair-extension concentration

The one-pair upper and lower exponential estimates are combined by two finite
union bounds: first over the two tails and then over every two-element vertex
set.  This is the exact simultaneous edge-extension estimate needed by the
random-greedy phase.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Probability that some pair has either an upper or a lower target
deviation. -/
theorem probability_timedStoppedGreedy_exists_pair_deviation_ge_le_of_pairCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V)
    (qUpper qLower : PairOn V → ℕ → ℝ)
    (Δ δ Kpair Kglobal JUpper : ℕ) (theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀)
    (havailable : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → S.available.Nonempty)
    (hpair : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
        HasAvailablePairCutoff Δ S)
    (hpairTwo : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
        HasPairTwoAwayCutoff F Kpair S)
    (htwo : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
        HasTwoAwayCutoff F Kglobal S)
    (hfloor : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S →
        HasAvailablePairFloor δ S)
    (hδ : 1 ≤ δ) (hsmall : 3 + Kpair < δ)
    (hqUpperLowerBound : ∀ P : PairOn V, ∀ i, i < n →
      -(JUpper : ℝ) ≤
        qUpper P (i + 1) - qUpper P i)
    (hqUpperNoninc : ∀ P : PairOn V, ∀ i, i < n →
      qUpper P (i + 1) - qUpper P i ≤ 0)
    (hqLowerDeath : ∀ P : PairOn V, ∀ i, i < n →
      -(δ : ℝ) ≤
        qLower P (i + 1) - qLower P i)
    (hqLowerNoninc : ∀ P : PairOn V, ∀ i, i < n →
      qLower P (i + 1) - qLower P i ≤ 0)
    (hqUpperDrift : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P.1 S →
        -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (3 * δ - 2 - Δ : ℕ)) ≤
          qUpper P (i + 1) - qUpper P i)
    (hqLowerDrift : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P.1 S →
        qLower P (i + 1) - qLower P i ≤
          -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (3 * Δ + Kglobal : ℕ)))
    (hvarianceUpper : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P.1 S →
        2 * ((S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (((3 + Kpair : ℕ) : ℝ) * ((3 * Δ + Kglobal : ℕ) : ℝ)))) +
            2 * (qUpper P (i + 1) - qUpper P i) ^ 2 ≤ v)
    (hvarianceLower : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → active i S → PairAlive P.1 S →
        2 * ((S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (((3 + Kpair : ℕ) : ℝ) * ((3 * Δ + Kglobal : ℕ) : ℝ)))) +
            2 * (qLower P (i + 1) - qLower P i) ^ 2 ≤ v)
    (htheta : 0 < theta)
    (hthetaUpper : theta * (JUpper : ℝ) ≤ 1)
    (hthetaLower : theta * ((3 + Kpair : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    (L.probability (fun z ↦ ∃ P : PairOn V,
      (PairAlive P.1 z.2 ∧
        a ≤ fixedPairUpperDeviation (qUpper P) S₀ P.1 z.1.1 z.2 -
          fixedPairUpperDeviation (qUpper P) S₀ P.1 0 S₀) ∨
      (PairAlive P.1 z.2 ∧
        a ≤ fixedPairLowerDeviation (qLower P) S₀ P.1 z.1.1 z.2 -
          fixedPairLowerDeviation (qLower P) S₀ P.1 0 S₀)) : ℝ) ≤
      (Fintype.card (PairOn V) : ℝ) *
        (2 * Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v)) := by
  classical
  dsimp only
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let upperBad : PairOn V → FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun P z ↦ PairAlive P.1 z.2 ∧
      a ≤ fixedPairUpperDeviation (qUpper P) S₀ P.1 z.1.1 z.2 -
        fixedPairUpperDeviation (qUpper P) S₀ P.1 0 S₀
  let lowerBad : PairOn V → FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun P z ↦ PairAlive P.1 z.2 ∧
      a ≤ fixedPairLowerDeviation (qLower P) S₀ P.1 z.1.1 z.2 -
        fixedPairLowerDeviation (qLower P) S₀ P.1 0 S₀
  let ε : ℝ := Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v)
  have hupper : ∀ P : PairOn V, (L.probability (upperBad P) : ℝ) ≤ ε := by
    intro P
    exact probability_timedStoppedGreedy_fixedPair_sharp_alive_upper_le_exp_of_pairCutoff
      n F active S₀ P.1 P.2 (qUpper P) Δ δ Kpair Kglobal JUpper theta a v
      hInv₀ havailable hpair hpairTwo htwo hfloor hδ hsmall
      (hqUpperLowerBound P) (hqUpperNoninc P)
      (hqUpperDrift P) (hvarianceUpper P) htheta hthetaUpper hv
  have hlower : ∀ P : PairOn V, (L.probability (lowerBad P) : ℝ) ≤ ε := by
    intro P
    exact probability_timedStoppedGreedy_fixedPair_sharp_alive_lower_le_exp_of_pairCutoff
      n F active S₀ P.1 P.2 (qLower P) Δ δ Kpair Kglobal (3 + Kpair)
      theta a v hInv₀ havailable hpair hpairTwo htwo hfloor
      (hqLowerDeath P) (hqLowerNoninc P)
      (fun i hi S hS hactive _halive S' hmass _hS' halive' ↦
        fixedPairLowerDeviation_alive_increment_le_of_pairCutoff P.2 hS
          (havailable i hi S hS hactive) (hpairTwo i hi S hS hactive)
          (hqLowerNoninc P i hi) hmass halive')
      (hqLowerDrift P) (hvarianceLower P)
      htheta hthetaLower hv
  have hpairBad : ∀ P : PairOn V,
      (L.probability (fun z ↦ upperBad P z ∨ lowerBad P z) : ℝ) ≤ 2 * ε := by
    intro P
    have hor := L.probability_or_le (upperBad P) (lowerBad P)
    have horReal :
        (L.probability (fun z ↦ upperBad P z ∨ lowerBad P z) : ℝ) ≤
          (L.probability (upperBad P) : ℝ) +
            (L.probability (lowerBad P) : ℝ) := by
      exact_mod_cast hor
    calc
      (L.probability (fun z ↦ upperBad P z ∨ lowerBad P z) : ℝ) ≤
          (L.probability (upperBad P) : ℝ) +
            (L.probability (lowerBad P) : ℝ) := horReal
      _ ≤ ε + ε := add_le_add (hupper P) (hlower P)
      _ = 2 * ε := by ring
  have hunion := L.probability_exists_le (univ : Finset (PairOn V))
    (fun P z ↦ upperBad P z ∨ lowerBad P z)
  have hunionReal :
      (L.probability (fun z ↦ ∃ P : PairOn V,
        upperBad P z ∨ lowerBad P z) : ℝ) ≤
        ∑ P : PairOn V,
          (L.probability (fun z ↦ upperBad P z ∨ lowerBad P z) : ℝ) := by
    have hraw :
        (L.probability (fun z ↦ ∃ P ∈ (univ : Finset (PairOn V)),
          upperBad P z ∨ lowerBad P z) : ℝ) ≤
          ∑ P : PairOn V,
            (L.probability (fun z ↦ upperBad P z ∨ lowerBad P z) : ℝ) := by
      exact_mod_cast hunion
    simpa using hraw
  calc
    (L.probability (fun z ↦ ∃ P : PairOn V,
        upperBad P z ∨ lowerBad P z) : ℝ) ≤
      ∑ P : PairOn V,
        (L.probability (fun z ↦ upperBad P z ∨ lowerBad P z) : ℝ) := hunionReal
    _ ≤ ∑ _P : PairOn V, 2 * ε := by
      apply sum_le_sum
      intro P _hP
      exact hpairBad P
    _ = (Fintype.card (PairOn V) : ℝ) * (2 * ε) := by simp
    _ = _ := rfl

end

end Erdos207
