/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AverageAvailabilityConcentration
import ErdosProblems.Erdos207.TimedStoppedTotalTwoAway
import ErdosProblems.Erdos207.TimedPairBandTwoCutoffs

/-!
# Pair-band process with aggregate availability control

This is the common stopped law used by the long greedy phase.  It combines
the local pair band, separate pair-local and global two-away cutoffs, one
aggregate two-away-incidence cutoff, and a constant global availability
floor.  The floor is protected probabilistically by the averaged drift
rather than pathwise by the maximum deletion envelope.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Active region for the averaged long phase. -/
def timedAveragePairBandActive
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Kpair Kglobal Δ δ I D : ℕ)
    (i : ℕ) (S : GreedyStateOn V) : Prop :=
  pairBandActiveTwoCutoffs F Kpair Kglobal Δ δ i S ∧
    totalAvailableTwoAwayIncidences F S ≤ I ∧
    D ≤ S.available.card

/-- Every positive-mass state retains the greedy invariant and the initial
availability containment. -/
theorem timedAveragePairBandProcessLaw_supported_pairTrajectoryInvariant
    {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ} {F : ForbiddenFamilyOn V}
    {Kpair Kglobal Δ δ I D : ℕ} {S₀ : GreedyStateOn V}
    (hInv₀ : GreedyInvariant F S₀) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
      (timedAveragePairBandActive F Kpair Kglobal Δ δ I D) S₀).SupportedOn
      (fun z ↦ PairTrajectoryInvariant F S₀ z.2) := by
  apply FiniteLaw.timedStoppedProcessLaw_supported n
    (fun _ ↦ greedyKernel F)
      (timedAveragePairBandActive F Kpair Kglobal Δ δ I D) S₀
      (pairTrajectoryInvariant_initial hInv₀)
  intro _i _hi S hS
  exact greedyKernel_supported_pairTrajectoryInvariant hS

/-- On support, the stopping clock is exactly the number of successful
single-triangle insertions. -/
theorem timedAveragePairBandProcessLaw_supported_chosen_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ} {F : ForbiddenFamilyOn V}
    {Kpair Kglobal Δ δ I D : ℕ} {S₀ : GreedyStateOn V}
    (hInv₀ : GreedyInvariant F S₀) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
      (timedAveragePairBandActive F Kpair Kglobal Δ δ I D) S₀).SupportedOn
      (fun z ↦ z.2.chosen.card = S₀.chosen.card + z.1.1) := by
  let z₀ : FiniteLaw.TimedState (GreedyStateOn V) n :=
    (⟨0, by omega⟩, S₀)
  have hstrong :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedAveragePairBandActive F Kpair Kglobal Δ δ I D) S₀).SupportedOn
        (fun z ↦ PairTrajectoryInvariant F S₀ z.2 ∧
          z.2.chosen.card = S₀.chosen.card + z.1.1) := by
    apply (FiniteLaw.supportedOn_pure
    (fun z : FiniteLaw.TimedState (GreedyStateOn V) n ↦
      PairTrajectoryInvariant F S₀ z.2 ∧
        z.2.chosen.card = S₀.chosen.card + z.1.1)
      ⟨pairTrajectoryInvariant_initial hInv₀, by simp [z₀]⟩).evolveKernels
    intro _i z hz
    classical
    unfold FiniteLaw.timedStoppedKernel
    split_ifs with hactive
    · have hsteps := greedyKernel_supported_step_of_nonempty F z.2
        hactive.2.1.1
      refine hsteps.map
        (fun S' ↦ (FiniteLaw.advanceTime z.1 hactive.1, S')) ?_
      intro S' hS'
      obtain ⟨T, hT, rfl⟩ := hS'
      have hTnot : T ∉ z.2.chosen := (hz.1.1.2.2 T hT).1
      refine ⟨⟨hz.1.1.step hT,
        (greedyStep_available_subset F z.2 T).trans hz.1.2⟩, ?_⟩
      simp only [FiniteLaw.advanceTime_val]
      rw [greedyStep_chosen_card F z.2 T hTnot, hz.2]
      omega
    · exact FiniteLaw.supportedOn_pure _ hz
  exact fun z hmass ↦ (hstrong z hmass).2

/-- Availability-deficit tail on the common averaged pair-band law. -/
theorem probability_timedAveragePairBand_availability_deficit_ge_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (Kpair Kglobal Δ δ I D : ℕ) (theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀) (hD : 0 < D)
    (hvariance :
      2 * ((3 * Δ + Kglobal : ℕ) : ℝ) *
          averageAvailabilityLossRate Δ I D +
        2 * (averageAvailabilityLossRate Δ I D) ^ 2 ≤ v)
    (htheta : 0 < theta)
    (hthetaJump : theta * ((3 * Δ + Kglobal : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    let active := timedAveragePairBandActive
      F Kpair Kglobal Δ δ I D
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    ((L.probability (fun z ↦
      a ≤ averageAvailabilityDeficit (averageAvailabilityLossRate Δ I D)
          z.1.1 z.2 -
        averageAvailabilityDeficit (averageAvailabilityLossRate Δ I D)
          0 S₀) : ℝ)) ≤
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v) := by
  classical
  dsimp only
  apply FiniteLaw.probability_timedStoppedProcess_deviation_ge_le_exp
    (P := fun S ↦ GreedyInvariant F S)
    n (fun _ ↦ greedyKernel F)
      (timedAveragePairBandActive F Kpair Kglobal Δ δ I D)
      (averageAvailabilityDeficit (averageAvailabilityLossRate Δ I D))
      S₀ theta (3 * Δ + Kglobal : ℕ) a v hInv₀ htheta
      (by positivity) hthetaJump hv
  · intro _i _hi S hS
    intro S' hmass
    rcases greedyKernel_supported_step_or_self F S S' hmass with
      rfl | ⟨T, hT, rfl⟩
    · exact hS
    · exact hS.step hT
  · intro i _hi S hS hactive S' hmass _hS'
    exact averageAvailabilityDeficit_jump_le
      (Δ := Δ) (K := Kglobal) (I := I) (D := D) (i := i) hS
      ⟨hactive.1.2.1, hactive.1.2.2.2.1,
        hactive.2.1, hactive.2.2⟩ hmass
  · intro i _hi S hS hactive
    apply
      greedyKernel_expectationReal_averageAvailabilityDeficit_increment_le_zero
        hS hD
    exact ⟨hactive.1.2.1, hactive.1.2.2.2.1,
      hactive.2.1, hactive.2.2⟩
  · intro i _hi S hS hactive
    exact
      (greedyKernel_expectationReal_averageAvailabilityDeficit_sqIncrement_le
        hS hD ⟨hactive.1.2.1, hactive.1.2.2.2.1,
          hactive.2.1, hactive.2.2⟩).trans hvariance

/-- Simultaneous pair-deviation tail on the same common law. -/
theorem probability_timedAveragePairBand_exists_pair_deviation_ge_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (qUpper qLower : PairOn V → ℕ → ℝ)
    (Kpair Kglobal Δ δ I D JUpper : ℕ) (theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀) (hD : 0 < D)
    (hδ : 1 ≤ δ) (hsmall : 3 + Kpair < δ)
    (hqUpperLowerBound : ∀ P : PairOn V, ∀ i, i < n →
      -(JUpper : ℝ) ≤ qUpper P (i + 1) - qUpper P i)
    (hqUpperNoninc : ∀ P : PairOn V, ∀ i, i < n →
      qUpper P (i + 1) - qUpper P i ≤ 0)
    (hqLowerDeath : ∀ P : PairOn V, ∀ i, i < n →
      -(δ : ℝ) ≤ qLower P (i + 1) - qLower P i)
    (hqLowerNoninc : ∀ P : PairOn V, ∀ i, i < n →
      qLower P (i + 1) - qLower P i ≤ 0)
    (hqUpperDrift : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S →
      timedAveragePairBandActive F Kpair Kglobal Δ δ I D i S →
      PairAlive P.1 S →
        -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (3 * δ - 2 - Δ : ℕ)) ≤
          qUpper P (i + 1) - qUpper P i)
    (hqLowerDrift : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S →
      timedAveragePairBandActive F Kpair Kglobal Δ δ I D i S →
      PairAlive P.1 S →
        qLower P (i + 1) - qLower P i ≤
          -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (3 * Δ + Kglobal : ℕ)))
    (hvarianceUpper : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S →
      timedAveragePairBandActive F Kpair Kglobal Δ δ I D i S →
      PairAlive P.1 S →
        2 * ((S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (((3 + Kpair : ℕ) : ℝ) *
                ((3 * Δ + Kglobal : ℕ) : ℝ)))) +
            2 * (qUpper P (i + 1) - qUpper P i) ^ 2 ≤ v)
    (hvarianceLower : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S →
      timedAveragePairBandActive F Kpair Kglobal Δ δ I D i S →
      PairAlive P.1 S →
        2 * ((S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (((3 + Kpair : ℕ) : ℝ) *
                ((3 * Δ + Kglobal : ℕ) : ℝ)))) +
            2 * (qLower P (i + 1) - qLower P i) ^ 2 ≤ v)
    (htheta : 0 < theta)
    (hthetaUpper : theta * (JUpper : ℝ) ≤ 1)
    (hthetaLower : theta * ((3 + Kpair : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    let active := timedAveragePairBandActive
      F Kpair Kglobal Δ δ I D
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
  dsimp only
  apply probability_timedStoppedGreedy_exists_pair_deviation_ge_le_of_pairCutoff
    n F (timedAveragePairBandActive F Kpair Kglobal Δ δ I D)
      S₀ qUpper qLower Δ δ Kpair Kglobal JUpper theta a v hInv₀
  · intro _i _hi _S _hS hactive
    exact hactive.1.1
  · intro _i _hi _S _hS hactive
    exact hactive.1.2.1
  · intro _i _hi _S _hS hactive
    exact hactive.1.2.2.1
  · intro _i _hi _S _hS hactive
    exact hactive.1.2.2.2.1
  · intro _i _hi _S _hS hactive
    exact hactive.1.2.2.2.2
  · exact hδ
  · exact hsmall
  · exact hqUpperLowerBound
  · exact hqUpperNoninc
  · exact hqLowerDeath
  · exact hqLowerNoninc
  · exact hqUpperDrift
  · exact hqLowerDrift
  · exact hvarianceUpper
  · exact hvarianceLower
  · exact htheta
  · exact hthetaUpper
  · exact hthetaLower
  · exact hv

end

end Erdos207
