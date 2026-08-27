/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SimultaneousPairExtensionConcentration
import ErdosProblems.Erdos207.SharpPairAggregateConcentration

/-! # Simultaneous pair concentration with aggregate lower drift -/

namespace Erdos207

open Finset

noncomputable section

theorem probability_timedStoppedGreedy_exists_pair_deviation_ge_le_of_aggregateCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (S0 : GreedyStateOn V)
    (qUpper qLower : PairOn V → ℕ → ℝ)
    (Delta delta Kpair Kglobal Kinc JUpper : ℕ)
    (theta a v : ℝ)
    (hInv0 : GreedyInvariant F S0)
    (havailable : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S0 S → active i S → S.available.Nonempty)
    (hpair : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S0 S → active i S →
        HasAvailablePairCutoff Delta S)
    (hpairTwo : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S0 S → active i S →
        HasPairTwoAwayCutoff F Kpair S)
    (hglobal : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S0 S → active i S →
        HasTwoAwayCutoff F Kglobal S)
    (hinc : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S0 S → active i S →
        HasPairStarTwoAwayIncidenceCutoff F Kinc S)
    (hfloor : ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S0 S → active i S →
        HasAvailablePairFloor delta S)
    (hdelta : 1 ≤ delta) (hsmall : 3 + Kpair < delta)
    (hqUpperLowerBound : ∀ P : PairOn V, ∀ i, i < n →
      -(JUpper : ℝ) ≤ qUpper P (i + 1) - qUpper P i)
    (hqUpperNoninc : ∀ P : PairOn V, ∀ i, i < n →
      qUpper P (i + 1) - qUpper P i ≤ 0)
    (hqLowerDeath : ∀ P : PairOn V, ∀ i, i < n →
      -(delta : ℝ) ≤ qLower P (i + 1) - qLower P i)
    (hqLowerNoninc : ∀ P : PairOn V, ∀ i, i < n →
      qLower P (i + 1) - qLower P i ≤ 0)
    (hqUpperDrift : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S0 S → active i S → PairAlive P.1 S →
        -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (3 * delta - 2 - Delta : ℕ)) ≤
          qUpper P (i + 1) - qUpper P i)
    (hqLowerDrift : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S0 S → active i S → PairAlive P.1 S →
        qLower P (i + 1) - qLower P i ≤
          -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
                (3 * Delta : ℕ) + Kinc))
    (hvarianceUpper : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S0 S → active i S → PairAlive P.1 S →
        2 * ((S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (((3 + Kpair : ℕ) : ℝ) *
                ((3 * Delta + Kglobal : ℕ) : ℝ)))) +
          2 * (qUpper P (i + 1) - qUpper P i) ^ 2 ≤ v)
    (hvarianceLower : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S0 S → active i S → PairAlive P.1 S →
        2 * ((S.available.card : ℝ)⁻¹ *
            (((3 + Kpair : ℕ) : ℝ) *
              (((availableTrianglesContainingPair S P.1).card : ℝ) *
                (3 * Delta : ℕ) + Kinc))) +
          2 * (qLower P (i + 1) - qLower P i) ^ 2 ≤ v)
    (htheta : 0 < theta)
    (hthetaUpper : theta * (JUpper : ℝ) ≤ 1)
    (hthetaLower : theta * ((3 + Kpair : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S0
    (L.probability (fun z ↦ ∃ P : PairOn V,
      (PairAlive P.1 z.2 ∧
        a ≤ fixedPairUpperDeviation (qUpper P) S0 P.1 z.1.1 z.2 -
          fixedPairUpperDeviation (qUpper P) S0 P.1 0 S0) ∨
      (PairAlive P.1 z.2 ∧
        a ≤ fixedPairLowerDeviation (qLower P) S0 P.1 z.1.1 z.2 -
          fixedPairLowerDeviation (qLower P) S0 P.1 0 S0)) : ℝ) ≤
      (Fintype.card (PairOn V) : ℝ) *
        (2 * Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v)) := by
  classical
  dsimp only
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S0
  let upperBad : PairOn V → FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun P z ↦ PairAlive P.1 z.2 ∧
      a ≤ fixedPairUpperDeviation (qUpper P) S0 P.1 z.1.1 z.2 -
        fixedPairUpperDeviation (qUpper P) S0 P.1 0 S0
  let lowerBad : PairOn V → FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun P z ↦ PairAlive P.1 z.2 ∧
      a ≤ fixedPairLowerDeviation (qLower P) S0 P.1 z.1.1 z.2 -
        fixedPairLowerDeviation (qLower P) S0 P.1 0 S0
  let epsilon : ℝ := Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v)
  have hupper : ∀ P : PairOn V, (L.probability (upperBad P) : ℝ) ≤ epsilon := by
    intro P
    exact probability_timedStoppedGreedy_fixedPair_sharp_alive_upper_le_exp_of_pairCutoff
      n F active S0 P.1 P.2 (qUpper P) Delta delta Kpair Kglobal JUpper
      theta a v hInv0 havailable hpair hpairTwo hglobal hfloor hdelta hsmall
      (hqUpperLowerBound P) (hqUpperNoninc P)
      (hqUpperDrift P) (hvarianceUpper P) htheta hthetaUpper hv
  have hlower : ∀ P : PairOn V, (L.probability (lowerBad P) : ℝ) ≤ epsilon := by
    intro P
    exact probability_timedStoppedGreedy_fixedPair_sharp_alive_lower_le_exp_of_aggregateCutoff
      n F active S0 P.1 P.2 (qLower P) Delta delta Kpair Kinc (3 + Kpair)
      theta a v hInv0 havailable hpair hpairTwo hinc hfloor
      (hqLowerDeath P) (hqLowerNoninc P)
      (fun i hi S hS hactive _halive S' hmass _hS' halive' ↦
        fixedPairLowerDeviation_alive_increment_le_of_pairCutoff P.2 hS
          (havailable i hi S hS hactive) (hpairTwo i hi S hS hactive)
          (hqLowerNoninc P i hi) hmass halive')
      (hqLowerDrift P) (hvarianceLower P) htheta hthetaLower hv
  have hpairBad : ∀ P : PairOn V,
      (L.probability (fun z ↦ upperBad P z ∨ lowerBad P z) : ℝ) ≤
        2 * epsilon := by
    intro P
    have hor := L.probability_or_le (upperBad P) (lowerBad P)
    have horReal :
        (L.probability (fun z ↦ upperBad P z ∨ lowerBad P z) : ℝ) ≤
          (L.probability (upperBad P) : ℝ) +
            (L.probability (lowerBad P) : ℝ) := by
      exact_mod_cast hor
    calc
      _ ≤ (L.probability (upperBad P) : ℝ) +
          (L.probability (lowerBad P) : ℝ) := horReal
      _ ≤ epsilon + epsilon := add_le_add (hupper P) (hlower P)
      _ = 2 * epsilon := by ring
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
    _ ≤ ∑ _P : PairOn V, 2 * epsilon := by
      apply sum_le_sum
      intro P _hP
      exact hpairBad P
    _ = (Fintype.card (PairOn V) : ℝ) * (2 * epsilon) := by simp
    _ = _ := rfl

end

end Erdos207
