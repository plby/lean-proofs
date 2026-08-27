/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TimedAveragePairBand
import ErdosProblems.Erdos207.SimultaneousPairAggregateConcentration
import ErdosProblems.Erdos207.TimedStoppedPairAggregateTwoAway
import ErdosProblems.Erdos207.OutsidePairSurvival

/-!
# The common averaged stopped law with aggregate pair-star control

The lower pair-star drift is governed by a sum of two-away incidences rather
than their maximum.  This file adds precisely that sixth stopping condition
to the averaged pair-band law and transports all support and concentration
statements to the resulting single law.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Active region for the corrected averaged long phase. -/
def timedAggregateAveragePairBandActive
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Kpair Kglobal Kinc Delta delta I D : ℕ)
    (i : ℕ) (S : GreedyStateOn V) : Prop :=
  timedAveragePairBandActive F Kpair Kglobal Delta delta I D i S ∧
    HasPairStarTwoAwayIncidenceCutoff F Kinc S

theorem timedAggregateAveragePairBandProcessLaw_supported_pairTrajectoryInvariant
    {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ} {F : ForbiddenFamilyOn V}
    {Kpair Kglobal Kinc Delta delta I D : ℕ} {S0 : GreedyStateOn V}
    (hInv0 : GreedyInvariant F S0) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ => greedyKernel F)
      (timedAggregateAveragePairBandActive F Kpair Kglobal Kinc Delta delta I D)
      S0).SupportedOn (fun z => PairTrajectoryInvariant F S0 z.2) := by
  apply FiniteLaw.timedStoppedProcessLaw_supported n (fun _ => greedyKernel F)
    (timedAggregateAveragePairBandActive F Kpair Kglobal Kinc Delta delta I D)
    S0 (pairTrajectoryInvariant_initial hInv0)
  intro _i _hi S hS
  exact greedyKernel_supported_pairTrajectoryInvariant hS

theorem timedAggregateAveragePairBandProcessLaw_supported_chosen_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ} {F : ForbiddenFamilyOn V}
    {Kpair Kglobal Kinc Delta delta I D : ℕ} {S0 : GreedyStateOn V}
    (hInv0 : GreedyInvariant F S0) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ => greedyKernel F)
      (timedAggregateAveragePairBandActive F Kpair Kglobal Kinc Delta delta I D)
      S0).SupportedOn (fun z => z.2.chosen.card = S0.chosen.card + z.1.1) := by
  let z0 : FiniteLaw.TimedState (GreedyStateOn V) n := (⟨0, by omega⟩, S0)
  have hstrong :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ => greedyKernel F)
        (timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta I D) S0).SupportedOn
        (fun z => PairTrajectoryInvariant F S0 z.2 ∧
          z.2.chosen.card = S0.chosen.card + z.1.1) := by
    apply (FiniteLaw.supportedOn_pure
      (fun z : FiniteLaw.TimedState (GreedyStateOn V) n =>
        PairTrajectoryInvariant F S0 z.2 ∧
          z.2.chosen.card = S0.chosen.card + z.1.1)
      ⟨pairTrajectoryInvariant_initial hInv0, by simp [z0]⟩).evolveKernels
    intro _i z hz
    classical
    unfold FiniteLaw.timedStoppedKernel
    split_ifs with hactive
    · have hsteps := greedyKernel_supported_step_of_nonempty F z.2
        hactive.2.1.1.1
      refine hsteps.map
        (fun S' => (FiniteLaw.advanceTime z.1 hactive.1, S')) ?_
      intro S' hS'
      obtain ⟨T, hT, rfl⟩ := hS'
      have hTnot : T ∉ z.2.chosen := (hz.1.1.2.2 T hT).1
      refine ⟨⟨hz.1.1.step hT,
        (greedyStep_available_subset F z.2 T).trans hz.1.2⟩, ?_⟩
      simp only [FiniteLaw.advanceTime_val]
      rw [greedyStep_chosen_card F z.2 T hTnot, hz.2]
      omega
    · exact FiniteLaw.supportedOn_pure _ hz
  exact fun z hmass => (hstrong z hmass).2

/-- The extra stop does not change the averaged availability martingale. -/
theorem probability_timedAggregateAveragePairBand_availability_deficit_ge_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S0 : GreedyStateOn V)
    (Kpair Kglobal Kinc Delta delta I D : ℕ) (theta a v : ℝ)
    (hInv0 : GreedyInvariant F S0) (hD : 0 < D)
    (hvariance :
      2 * ((3 * Delta + Kglobal : ℕ) : ℝ) *
          averageAvailabilityLossRate Delta I D +
        2 * (averageAvailabilityLossRate Delta I D) ^ 2 ≤ v)
    (htheta : 0 < theta)
    (hthetaJump : theta * ((3 * Delta + Kglobal : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    let active := timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ => greedyKernel F) active S0
    (L.probability (fun z =>
      a ≤ averageAvailabilityDeficit (averageAvailabilityLossRate Delta I D)
          z.1.1 z.2 -
        averageAvailabilityDeficit (averageAvailabilityLossRate Delta I D)
          0 S0) : ℝ) ≤
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v) := by
  classical
  dsimp only
  apply FiniteLaw.probability_timedStoppedProcess_deviation_ge_le_exp
    (P := fun S => GreedyInvariant F S) n (fun _ => greedyKernel F)
    (timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D)
    (averageAvailabilityDeficit (averageAvailabilityLossRate Delta I D))
    S0 theta (3 * Delta + Kglobal : ℕ) a v hInv0 htheta
    (by positivity) hthetaJump hv
  · intro _i _hi S hS S' hmass
    rcases greedyKernel_supported_step_or_self F S S' hmass with
      rfl | ⟨T, hT, rfl⟩
    · exact hS
    · exact hS.step hT
  · intro i _hi S hS hactive S' hmass _hS'
    exact averageAvailabilityDeficit_jump_le
      (Δ := Delta) (K := Kglobal) (I := I) (D := D) (i := i) hS
      ⟨hactive.1.1.2.1, hactive.1.1.2.2.2.1,
        hactive.1.2.1, hactive.1.2.2⟩ hmass
  · intro i _hi S hS hactive
    apply greedyKernel_expectationReal_averageAvailabilityDeficit_increment_le_zero
      hS hD
    exact ⟨hactive.1.1.2.1, hactive.1.1.2.2.2.1,
      hactive.1.2.1, hactive.1.2.2⟩
  · intro i _hi S hS hactive
    exact (greedyKernel_expectationReal_averageAvailabilityDeficit_sqIncrement_le
      hS hD ⟨hactive.1.1.2.1, hactive.1.1.2.2.2.1,
        hactive.1.2.1, hactive.1.2.2⟩).trans hvariance

/-- Simultaneous pair trajectories with the additive lower-drift cutoff. -/
theorem probability_timedAggregateAveragePairBand_exists_pair_deviation_ge_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S0 : GreedyStateOn V)
    (qUpper qLower : PairOn V → ℕ → ℝ)
    (Kpair Kglobal Kinc Delta delta I D JUpper : ℕ)
    (theta a v : ℝ)
    (hInv0 : GreedyInvariant F S0)
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
      PairTrajectoryInvariant F S0 S →
      timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D i S → PairAlive P.1 S →
        -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (3 * delta - 2 - Delta : ℕ)) ≤
          qUpper P (i + 1) - qUpper P i)
    (hqLowerDrift : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S0 S →
      timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D i S → PairAlive P.1 S →
        qLower P (i + 1) - qLower P i ≤
          -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
                (3 * Delta : ℕ) + Kinc))
    (hvarianceUpper : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S0 S →
      timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D i S → PairAlive P.1 S →
        2 * ((S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (((3 + Kpair : ℕ) : ℝ) *
                ((3 * Delta + Kglobal : ℕ) : ℝ)))) +
          2 * (qUpper P (i + 1) - qUpper P i) ^ 2 ≤ v)
    (hvarianceLower : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S0 S →
      timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D i S → PairAlive P.1 S →
        2 * ((S.available.card : ℝ)⁻¹ *
            (((3 + Kpair : ℕ) : ℝ) *
              (((availableTrianglesContainingPair S P.1).card : ℝ) *
                (3 * Delta : ℕ) + Kinc))) +
          2 * (qLower P (i + 1) - qLower P i) ^ 2 ≤ v)
    (htheta : 0 < theta)
    (hthetaUpper : theta * (JUpper : ℝ) ≤ 1)
    (hthetaLower : theta * ((3 + Kpair : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    let active := timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ => greedyKernel F) active S0
    (L.probability (fun z => ∃ P : PairOn V,
      (PairAlive P.1 z.2 ∧
        a ≤ fixedPairUpperDeviation (qUpper P) S0 P.1 z.1.1 z.2 -
          fixedPairUpperDeviation (qUpper P) S0 P.1 0 S0) ∨
      (PairAlive P.1 z.2 ∧
        a ≤ fixedPairLowerDeviation (qLower P) S0 P.1 z.1.1 z.2 -
          fixedPairLowerDeviation (qLower P) S0 P.1 0 S0)) : ℝ) ≤
      (Fintype.card (PairOn V) : ℝ) *
        (2 * Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v)) := by
  dsimp only
  apply probability_timedStoppedGreedy_exists_pair_deviation_ge_le_of_aggregateCutoff
    n F (timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D)
    S0 qUpper qLower Delta delta Kpair Kglobal Kinc JUpper theta a v hInv0
  · intro _i _hi _S _hS hactive; exact hactive.1.1.1
  · intro _i _hi _S _hS hactive; exact hactive.1.1.2.1
  · intro _i _hi _S _hS hactive; exact hactive.1.1.2.2.1
  · intro _i _hi _S _hS hactive; exact hactive.1.1.2.2.2.1
  · intro _i _hi _S _hS hactive; exact hactive.2
  · intro _i _hi _S _hS hactive; exact hactive.1.1.2.2.2.2
  · exact hdelta
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

/-- The sixth stop also preserves all eligible outside leave pairs. -/
theorem timedAggregateAveragePairBandProcessLaw_supported_outsideLeavePairsAlive
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (H : SimpleGraph V) (X : Finset V)
    (S0 : GreedyStateOn V) (Kpair Kglobal Kinc Delta delta I D : ℕ)
    (hInv0 : GreedyInvariant F S0)
    (houtside0 : OutsideLeavePairsAlive H X S0)
    (hsmall : 3 + Kpair < delta) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ => greedyKernel F)
      (timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D) S0).SupportedOn
      (fun z => OutsideLeavePairsAlive H X z.2) := by
  have hsupport :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ => greedyKernel F)
        (timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta I D) S0).SupportedOn
        (fun z => GreedyInvariant F z.2 ∧ OutsideLeavePairsAlive H X z.2) := by
    apply (FiniteLaw.supportedOn_pure
      (fun z : FiniteLaw.TimedState (GreedyStateOn V) n =>
        GreedyInvariant F z.2 ∧ OutsideLeavePairsAlive H X z.2)
      ⟨hInv0, houtside0⟩).evolveKernels
    intro _i z hz
    classical
    unfold FiniteLaw.timedStoppedKernel
    split_ifs with hactive
    · have hout := greedyKernel_supported_outsideLeavePairsAlive_of_pairCutoff
          hz.2 hz.1 hactive.2.1.1.2.2.1 hactive.2.1.1.2.2.2.2 hsmall
      have hboth : (greedyKernel F z.2).SupportedOn
          (fun S' => GreedyInvariant F S' ∧ OutsideLeavePairsAlive H X S') := by
        intro S' hmass
        exact ⟨greedyKernel_supported hz.1 S' hmass, hout S' hmass⟩
      exact hboth.map (fun S' => (FiniteLaw.advanceTime z.1 hactive.1, S'))
        (fun _S' hS' => hS')
    · exact FiniteLaw.supportedOn_pure _ hz
  exact fun z hmass => (hsupport z hmass).2

end

end Erdos207
