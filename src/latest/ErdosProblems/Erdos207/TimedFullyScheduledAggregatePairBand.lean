/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TimedScheduledAggregatePairBand
import ErdosProblems.Erdos207.AvailabilityUpperTrajectory

/-!
# Simultaneously scheduled lower and upper trajectories

The retrospective transfer argument needs the upper envelope for total
availability at its actual time, rather than a terminal worst case.  This
module adds that upper schedule to the synchronized stopped process.  Its
failure is charged to the already present upper pair-deviation event, so no
new probabilistic error term is introduced.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def timedFullyScheduledAggregatePairBandActive
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Kpair Kglobal Kinc Delta delta I Dcut : ℕ)
    (Dschedule dschedule Mschedule : ℕ → ℕ)
    (i : ℕ) (S : GreedyStateOn V) : Prop :=
  timedScheduledAggregatePairBandActive F Kpair Kglobal Kinc
      Delta delta I Dcut Dschedule dschedule i S ∧
    S.available.card ≤ Mschedule i

theorem timedFullyScheduledAggregatePairBandProcessLaw_supported_pairTrajectoryInvariant
    {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ} {F : ForbiddenFamilyOn V}
    {Kpair Kglobal Kinc Delta delta I Dcut : ℕ}
    {Dschedule dschedule Mschedule : ℕ → ℕ} {S₀ : GreedyStateOn V}
    (hInv₀ : GreedyInvariant F S₀) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
      (timedFullyScheduledAggregatePairBandActive F Kpair Kglobal Kinc
        Delta delta I Dcut Dschedule dschedule Mschedule) S₀).SupportedOn
      (fun z ↦ PairTrajectoryInvariant F S₀ z.2) := by
  apply FiniteLaw.timedStoppedProcessLaw_supported n (fun _ ↦ greedyKernel F)
    (timedFullyScheduledAggregatePairBandActive F Kpair Kglobal Kinc
      Delta delta I Dcut Dschedule dschedule Mschedule)
    S₀ (pairTrajectoryInvariant_initial hInv₀)
  intro _i _hi S hS
  exact greedyKernel_supported_pairTrajectoryInvariant hS

theorem timedFullyScheduledAggregatePairBandProcessLaw_supported_chosen_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ} {F : ForbiddenFamilyOn V}
    {Kpair Kglobal Kinc Delta delta I Dcut : ℕ}
    {Dschedule dschedule Mschedule : ℕ → ℕ} {S₀ : GreedyStateOn V}
    (hInv₀ : GreedyInvariant F S₀) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
      (timedFullyScheduledAggregatePairBandActive F Kpair Kglobal Kinc
        Delta delta I Dcut Dschedule dschedule Mschedule) S₀).SupportedOn
      (fun z ↦ z.2.chosen.card = S₀.chosen.card + z.1.1) := by
  let z₀ : FiniteLaw.TimedState (GreedyStateOn V) n := (⟨0, by omega⟩, S₀)
  have hstrong :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedFullyScheduledAggregatePairBandActive F Kpair Kglobal Kinc
          Delta delta I Dcut Dschedule dschedule Mschedule) S₀).SupportedOn
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
    split_ifs with hrun
    · have havailable : z.2.available.Nonempty := hrun.2.1.1.1.1.1
      have hsteps := greedyKernel_supported_step_of_nonempty F z.2 havailable
      refine hsteps.map
        (fun S' ↦ (FiniteLaw.advanceTime z.1 hrun.1, S')) ?_
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

/-- The additional upper stop preserves the same availability
supermartingale estimate. -/
theorem probability_timedFullyScheduledAggregatePairBand_availability_deficit_ge_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (Kpair Kglobal Kinc Delta delta I Dcut : ℕ)
    (Dschedule dschedule Mschedule : ℕ → ℕ) (theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀) (hDcut : 0 < Dcut)
    (hvariance :
      2 * ((3 * Delta + Kglobal : ℕ) : ℝ) *
          averageAvailabilityLossRate Delta I Dcut +
        2 * (averageAvailabilityLossRate Delta I Dcut) ^ 2 ≤ v)
    (htheta : 0 < theta)
    (hthetaJump : theta * ((3 * Delta + Kglobal : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    let active := timedFullyScheduledAggregatePairBandActive F Kpair Kglobal
      Kinc Delta delta I Dcut Dschedule dschedule Mschedule
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    (L.probability (fun z ↦
      a ≤ averageAvailabilityDeficit
          (averageAvailabilityLossRate Delta I Dcut) z.1.1 z.2 -
        averageAvailabilityDeficit
          (averageAvailabilityLossRate Delta I Dcut) 0 S₀) : ℝ) ≤
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v) := by
  classical
  dsimp only
  apply FiniteLaw.probability_timedStoppedProcess_deviation_ge_le_exp
    (P := fun S ↦ GreedyInvariant F S) n (fun _ ↦ greedyKernel F)
    (timedFullyScheduledAggregatePairBandActive F Kpair Kglobal Kinc
      Delta delta I Dcut Dschedule dschedule Mschedule)
    (averageAvailabilityDeficit
      (averageAvailabilityLossRate Delta I Dcut))
    S₀ theta (3 * Delta + Kglobal : ℕ) a v hInv₀ htheta
    (by positivity) hthetaJump hv
  · intro _i _hi S hS S' hmass
    rcases greedyKernel_supported_step_or_self F S S' hmass with
      rfl | ⟨T, hT, rfl⟩
    · exact hS
    · exact hS.step hT
  · intro i _hi S hS hactive S' hmass _hS'
    have hsched := hactive.1
    exact averageAvailabilityDeficit_jump_le
      (Δ := Delta) (K := Kglobal) (I := I) (D := Dcut) (i := i) hS
      ⟨hsched.1.1.1.2.1, hsched.1.1.1.2.2.2.1,
        hsched.1.1.2.1, hsched.1.1.2.2⟩ hmass
  · intro i _hi S hS hactive
    have hsched := hactive.1
    apply greedyKernel_expectationReal_averageAvailabilityDeficit_increment_le_zero
      hS hDcut
    exact ⟨hsched.1.1.1.2.1, hsched.1.1.1.2.2.2.1,
      hsched.1.1.2.1, hsched.1.1.2.2⟩
  · intro i _hi S hS hactive
    have hsched := hactive.1
    exact (greedyKernel_expectationReal_averageAvailabilityDeficit_sqIncrement_le
      hS hDcut ⟨hsched.1.1.1.2.1, hsched.1.1.1.2.2.2.1,
        hsched.1.1.2.1, hsched.1.1.2.2⟩).trans hvariance

/-- Simultaneous pair-deviation estimate under all three schedules. -/
theorem probability_timedFullyScheduledAggregatePairBand_exists_pair_deviation_ge_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (qUpper qLower : PairOn V → ℕ → ℝ)
    (Kpair Kglobal Kinc Delta delta I Dcut JUpper : ℕ)
    (Dschedule dschedule Mschedule : ℕ → ℕ) (theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀)
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
      PairTrajectoryInvariant F S₀ S →
      timedAggregateAveragePairBandActive F Kpair Kglobal Kinc
        Delta delta I Dcut i S → PairAlive P.1 S →
      -(S.available.card : ℝ)⁻¹ *
          (((availableTrianglesContainingPair S P.1).card : ℝ) *
            (3 * delta - 2 - Delta : ℕ)) ≤
        qUpper P (i + 1) - qUpper P i)
    (hqLowerDrift : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S →
      timedAggregateAveragePairBandActive F Kpair Kglobal Kinc
        Delta delta I Dcut i S → PairAlive P.1 S →
      qLower P (i + 1) - qLower P i ≤
        -(S.available.card : ℝ)⁻¹ *
          (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (3 * Delta : ℕ) + Kinc))
    (hvarianceUpper : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S →
      timedAggregateAveragePairBandActive F Kpair Kglobal Kinc
        Delta delta I Dcut i S → PairAlive P.1 S →
      2 * ((S.available.card : ℝ)⁻¹ *
          (((availableTrianglesContainingPair S P.1).card : ℝ) *
            (((3 + Kpair : ℕ) : ℝ) *
              ((3 * Delta + Kglobal : ℕ) : ℝ)))) +
        2 * (qUpper P (i + 1) - qUpper P i) ^ 2 ≤ v)
    (hvarianceLower : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S →
      timedAggregateAveragePairBandActive F Kpair Kglobal Kinc
        Delta delta I Dcut i S → PairAlive P.1 S →
      2 * ((S.available.card : ℝ)⁻¹ *
          (((3 + Kpair : ℕ) : ℝ) *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (3 * Delta : ℕ) + Kinc))) +
        2 * (qLower P (i + 1) - qLower P i) ^ 2 ≤ v)
    (htheta : 0 < theta)
    (hthetaUpper : theta * (JUpper : ℝ) ≤ 1)
    (hthetaLower : theta * ((3 + Kpair : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    let active := timedFullyScheduledAggregatePairBandActive F Kpair Kglobal
      Kinc Delta delta I Dcut Dschedule dschedule Mschedule
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
  apply probability_timedStoppedGreedy_exists_pair_deviation_ge_le_of_aggregateCutoff
    n F (timedFullyScheduledAggregatePairBandActive F Kpair Kglobal Kinc
      Delta delta I Dcut Dschedule dschedule Mschedule)
    S₀ qUpper qLower Delta delta Kpair Kglobal Kinc JUpper theta a v hInv₀
  · intro _i _hi _S _hS hactive; exact hactive.1.1.1.1.1
  · intro _i _hi _S _hS hactive; exact hactive.1.1.1.1.2.1
  · intro _i _hi _S _hS hactive; exact hactive.1.1.1.1.2.2.1
  · intro _i _hi _S _hS hactive; exact hactive.1.1.1.1.2.2.2.1
  · intro _i _hi _S _hS hactive; exact hactive.1.1.2
  · intro _i _hi _S _hS hactive; exact hactive.1.1.1.1.2.2.2.2
  · exact hdelta
  · exact hsmall
  · exact hqUpperLowerBound
  · exact hqUpperNoninc
  · exact hqLowerDeath
  · exact hqLowerNoninc
  · intro P i hi S hS hactive hAlive
    exact hqUpperDrift P i hi S hS hactive.1.1 hAlive
  · intro P i hi S hS hactive hAlive
    exact hqLowerDrift P i hi S hS hactive.1.1 hAlive
  · intro P i hi S hS hactive hAlive
    exact hvarianceUpper P i hi S hS hactive.1.1 hAlive
  · intro P i hi S hS hactive hAlive
    exact hvarianceLower P i hi S hS hactive.1.1 hAlive
  · exact htheta
  · exact hthetaUpper
  · exact hthetaLower
  · exact hv

/-- The scheduled upper bound is recovered from the same good pair event,
so the six original exceptional events still control first passage. -/
theorem probability_timedFullyScheduledAggregatePairBand_not_active_le_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (qUpper qLower : PairOn V → ℕ → ℝ)
    (Kpair Kglobal Kinc Delta delta I Dcut : ℕ)
    (Dschedule dschedule Mschedule : ℕ → ℕ) (aPair aAvail : ℝ)
    (epair epairTwo eglobalTwo einc etotal eavail : ℝ≥0)
    (hInv₀ : GreedyInvariant F S₀) (hDcut : 0 < Dcut)
    (havailabilityBuffer : ∀ i, i ≤ n →
      (Dcut : ℝ) + (i : ℝ) *
          averageAvailabilityLossRate Delta I Dcut + aAvail ≤
        (S₀.available.card : ℝ))
    (hcap : ∀ P : PairOn V, ∀ i, i ≤ n →
      qUpper P i +
          (fixedPairAvailableCountReal S₀ P.1 S₀ - qUpper P 0) + aPair ≤
        ((Delta + 1 : ℕ) : ℝ))
    (htargetFloor : ∀ P : PairOn V, ∀ i, i ≤ n →
      PairAlive P.1 S₀ →
      (delta : ℝ) ≤ qLower P i +
          (fixedPairAvailableCountReal S₀ P.1 S₀ - qLower P 0) - aPair)
    (hscheduledAvailability : ∀ i S, i ≤ n →
      PairTrajectoryInvariant F S₀ S →
      averageAvailabilityDeficit (averageAvailabilityLossRate Delta I Dcut)
            i S -
          averageAvailabilityDeficit (averageAvailabilityLossRate Delta I Dcut)
            0 S₀ < aAvail →
      Dschedule i ≤ S.available.card)
    (hscheduledPair : ∀ P : PairOn V, ∀ i S, i ≤ n →
      PairTrajectoryInvariant F S₀ S → PairAlive P.1 S →
      fixedPairLowerDeviation (qLower P) S₀ P.1 i S -
          fixedPairLowerDeviation (qLower P) S₀ P.1 0 S₀ < aPair →
      dschedule i ≤ (availableTrianglesContainingPair S P.1).card)
    (hscheduledUpper : ∀ i S, i ≤ n →
      PairTrajectoryInvariant F S₀ S →
      S.chosen.card = S₀.chosen.card + i →
      (∀ P : PairOn V, PairAlive P.1 S →
        fixedPairUpperDeviation (qUpper P) S₀ P.1 i S -
          fixedPairUpperDeviation (qUpper P) S₀ P.1 0 S₀ < aPair) →
      S.available.card ≤ Mschedule i)
    (hpair :
      let active := timedFullyScheduledAggregatePairBandActive F Kpair Kglobal
        Kinc Delta delta I Dcut Dschedule dschedule Mschedule
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      L.probability (fun z ↦ ∃ P : PairOn V,
        (PairAlive P.1 z.2 ∧
          aPair ≤ fixedPairUpperDeviation (qUpper P) S₀ P.1 z.1.1 z.2 -
            fixedPairUpperDeviation (qUpper P) S₀ P.1 0 S₀) ∨
        (PairAlive P.1 z.2 ∧
          aPair ≤ fixedPairLowerDeviation (qLower P) S₀ P.1 z.1.1 z.2 -
            fixedPairLowerDeviation (qLower P) S₀ P.1 0 S₀)) ≤ epair)
    (hpairTwo :
      let active := timedFullyScheduledAggregatePairBandActive F Kpair Kglobal
        Kinc Delta delta I Dcut Dschedule dschedule Mschedule
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      L.probability (fun z ↦ ¬ HasPairTwoAwayCutoff F Kpair z.2) ≤ epairTwo)
    (hglobalTwo :
      let active := timedFullyScheduledAggregatePairBandActive F Kpair Kglobal
        Kinc Delta delta I Dcut Dschedule dschedule Mschedule
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      L.probability (fun z ↦ ¬ HasTwoAwayCutoff F Kglobal z.2) ≤ eglobalTwo)
    (hinc :
      let active := timedFullyScheduledAggregatePairBandActive F Kpair Kglobal
        Kinc Delta delta I Dcut Dschedule dschedule Mschedule
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      L.probability
        (fun z ↦ ¬ HasPairStarTwoAwayIncidenceCutoff F Kinc z.2) ≤ einc)
    (htotal :
      let active := timedFullyScheduledAggregatePairBandActive F Kpair Kglobal
        Kinc Delta delta I Dcut Dschedule dschedule Mschedule
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      L.probability
        (fun z ↦ I < totalAvailableTwoAwayIncidences F z.2) ≤ etotal)
    (havail :
      let active := timedFullyScheduledAggregatePairBandActive F Kpair Kglobal
        Kinc Delta delta I Dcut Dschedule dschedule Mschedule
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      L.probability (fun z ↦
        aAvail ≤ averageAvailabilityDeficit
            (averageAvailabilityLossRate Delta I Dcut) z.1.1 z.2 -
          averageAvailabilityDeficit
            (averageAvailabilityLossRate Delta I Dcut) 0 S₀) ≤ eavail) :
    let active := timedFullyScheduledAggregatePairBandActive F Kpair Kglobal
      Kinc Delta delta I Dcut Dschedule dschedule Mschedule
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    L.probability (fun z ↦ ¬ active z.1.1 z.2) ≤
      epair + epairTwo + eglobalTwo + einc + etotal + eavail := by
  classical
  dsimp only
  let active := timedFullyScheduledAggregatePairBandActive F Kpair Kglobal
    Kinc Delta delta I Dcut Dschedule dschedule Mschedule
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let pairBad : FiniteLaw.TimedState (GreedyStateOn V) n → Prop := fun z ↦
    ∃ P : PairOn V,
      (PairAlive P.1 z.2 ∧
        aPair ≤ fixedPairUpperDeviation (qUpper P) S₀ P.1 z.1.1 z.2 -
          fixedPairUpperDeviation (qUpper P) S₀ P.1 0 S₀) ∨
      (PairAlive P.1 z.2 ∧
        aPair ≤ fixedPairLowerDeviation (qLower P) S₀ P.1 z.1.1 z.2 -
          fixedPairLowerDeviation (qLower P) S₀ P.1 0 S₀)
  let badAt : Fin 6 → FiniteLaw.TimedState (GreedyStateOn V) n → Prop
    | ⟨0, _⟩ => pairBad
    | ⟨1, _⟩ => fun z ↦ ¬ HasPairTwoAwayCutoff F Kpair z.2
    | ⟨2, _⟩ => fun z ↦ ¬ HasTwoAwayCutoff F Kglobal z.2
    | ⟨3, _⟩ => fun z ↦ ¬ HasPairStarTwoAwayIncidenceCutoff F Kinc z.2
    | ⟨4, _⟩ => fun z ↦ I < totalAvailableTwoAwayIncidences F z.2
    | ⟨5, _⟩ => fun z ↦
        aAvail ≤ averageAvailabilityDeficit
            (averageAvailabilityLossRate Delta I Dcut) z.1.1 z.2 -
          averageAvailabilityDeficit
            (averageAvailabilityLossRate Delta I Dcut) 0 S₀
  let eps : Fin 6 → ℝ≥0
    | ⟨0, _⟩ => epair
    | ⟨1, _⟩ => epairTwo
    | ⟨2, _⟩ => eglobalTwo
    | ⟨3, _⟩ => einc
    | ⟨4, _⟩ => etotal
    | ⟨5, _⟩ => eavail
  have htraj : L.SupportedOn
      (fun z ↦ PairTrajectoryInvariant F S₀ z.2) := by
    simpa only [L, active] using
      timedFullyScheduledAggregatePairBandProcessLaw_supported_pairTrajectoryInvariant
        (n := n) (Kpair := Kpair) (Kglobal := Kglobal) (Kinc := Kinc)
        (Delta := Delta) (delta := delta) (I := I) (Dcut := Dcut)
        (Dschedule := Dschedule) (dschedule := dschedule)
        (Mschedule := Mschedule) hInv₀
  have hcard : L.SupportedOn
      (fun z ↦ z.2.chosen.card = S₀.chosen.card + z.1.1) := by
    simpa only [L, active] using
      timedFullyScheduledAggregatePairBandProcessLaw_supported_chosen_card
        (n := n) (Kpair := Kpair) (Kglobal := Kglobal) (Kinc := Kinc)
        (Delta := Delta) (delta := delta) (I := I) (Dcut := Dcut)
        (Dschedule := Dschedule) (dschedule := dschedule)
        (Mschedule := Mschedule) hInv₀
  have hsupport : L.SupportedOn (fun z ↦
      PairTrajectoryInvariant F S₀ z.2 ∧
        z.2.chosen.card = S₀.chosen.card + z.1.1) := by
    intro z hmass
    exact ⟨htraj z hmass, hcard z hmass⟩
  have hinactiveUnion : L.probability (fun z ↦ ¬ active z.1.1 z.2) ≤
      L.probability (fun z ↦ ∃ j : Fin 6, badAt j z) := by
    apply L.probability_mono_of_supported hsupport
    intro z hz hnotactive
    by_contra hnotbad
    have hnotPairBad : ¬ pairBad z := by
      intro hbad
      exact hnotbad ⟨⟨0, by omega⟩, by simpa [badAt] using hbad⟩
    have hpairTwoGood : HasPairTwoAwayCutoff F Kpair z.2 := by
      by_contra hbad
      exact hnotbad ⟨⟨1, by omega⟩, by simpa [badAt] using hbad⟩
    have hglobalTwoGood : HasTwoAwayCutoff F Kglobal z.2 := by
      by_contra hbad
      exact hnotbad ⟨⟨2, by omega⟩, by simpa [badAt] using hbad⟩
    have hincGood : HasPairStarTwoAwayIncidenceCutoff F Kinc z.2 := by
      by_contra hbad
      exact hnotbad ⟨⟨3, by omega⟩, by simpa [badAt] using hbad⟩
    have htotalGood : totalAvailableTwoAwayIncidences F z.2 ≤ I := by
      by_contra hbad
      have hbad' : I < totalAvailableTwoAwayIncidences F z.2 := by omega
      exact hnotbad ⟨⟨4, by omega⟩, by simpa [badAt] using hbad'⟩
    have havailGood :
        averageAvailabilityDeficit (averageAvailabilityLossRate Delta I Dcut)
            z.1.1 z.2 -
          averageAvailabilityDeficit (averageAvailabilityLossRate Delta I Dcut)
            0 S₀ < aAvail := by
      exact lt_of_not_ge fun hbad ↦
        hnotbad ⟨⟨5, by omega⟩, by simpa [badAt] using hbad⟩
    have htime : z.1.1 ≤ n := by omega
    have havailability : Dcut ≤ z.2.available.card := by
      have hbuffer := havailabilityBuffer z.1.1 htime
      have hreal : (Dcut : ℝ) < (z.2.available.card : ℝ) := by
        simp only [averageAvailabilityDeficit] at havailGood
        push_cast at havailGood
        nlinarith
      exact_mod_cast hreal.le
    have hnonempty : z.2.available.Nonempty := by
      rw [← card_pos]
      exact hDcut.trans_le havailability
    have hupperDev : ∀ P : PairOn V, PairAlive P.1 z.2 →
        fixedPairUpperDeviation (qUpper P) S₀ P.1 z.1.1 z.2 -
          fixedPairUpperDeviation (qUpper P) S₀ P.1 0 S₀ < aPair := by
      intro P halive
      exact lt_of_not_ge fun hbad ↦
        hnotPairBad ⟨P, Or.inl ⟨halive, hbad⟩⟩
    have hlowerDev : ∀ P : PairOn V, PairAlive P.1 z.2 →
        fixedPairLowerDeviation (qLower P) S₀ P.1 z.1.1 z.2 -
          fixedPairLowerDeviation (qLower P) S₀ P.1 0 S₀ < aPair := by
      intro P halive
      exact lt_of_not_ge fun hbad ↦
        hnotPairBad ⟨P, Or.inr ⟨halive, hbad⟩⟩
    have hpairBand :
        pairBandActiveTwoCutoffs F Kpair Kglobal Delta delta z.1.1 z.2 :=
      pairBandActiveTwoCutoffs_of_deviations_lt qUpper qLower z.1.1
        Kpair Kglobal Delta delta aPair hz.1.2 hnonempty hpairTwoGood
        hglobalTwoGood (fun P ↦ hcap P z.1.1 htime)
        (fun P ↦ htargetFloor P z.1.1 htime) hupperDev hlowerDev
    have hbase : timedAggregateAveragePairBandActive F Kpair Kglobal Kinc
        Delta delta I Dcut z.1.1 z.2 :=
      ⟨⟨hpairBand, htotalGood, havailability⟩, hincGood⟩
    have hDschedule : Dschedule z.1.1 ≤ z.2.available.card :=
      hscheduledAvailability z.1.1 z.2 htime hz.1 havailGood
    have hdschedule : HasAvailablePairFloor (dschedule z.1.1) z.2 := by
      intro P hPcard hPalive
      let P' : PairOn V := ⟨P, hPcard⟩
      exact hscheduledPair P' z.1.1 z.2 htime hz.1 hPalive
        (hlowerDev P' hPalive)
    have hMschedule : z.2.available.card ≤ Mschedule z.1.1 :=
      hscheduledUpper z.1.1 z.2 htime hz.1 hz.2 hupperDev
    exact hnotactive ⟨⟨hbase, hDschedule, hdschedule⟩, hMschedule⟩
  have hunion := L.probability_exists_le (univ : Finset (Fin 6)) badAt
  have hbadAt : ∀ j : Fin 6, L.probability (badAt j) ≤ eps j := by
    intro j
    fin_cases j
    · simpa [L, active, badAt, pairBad, eps] using hpair
    · simpa [L, active, badAt, eps] using hpairTwo
    · simpa [L, active, badAt, eps] using hglobalTwo
    · simpa [L, active, badAt, eps] using hinc
    · simpa [L, active, badAt, eps] using htotal
    · simpa [L, active, badAt, eps] using havail
  calc
    L.probability (fun z ↦ ¬ active z.1.1 z.2) ≤
        L.probability (fun z ↦ ∃ j : Fin 6, badAt j z) := hinactiveUnion
    _ ≤ ∑ j : Fin 6, L.probability (badAt j) := by
      simpa using hunion
    _ ≤ ∑ j : Fin 6, eps j := by
      apply sum_le_sum
      intro j _hj
      exact hbadAt j
    _ = epair + epairTwo + eglobalTwo + einc + etotal + eavail := by
      simp [eps, Fin.sum_univ_succ]
      ring

end

end Erdos207
