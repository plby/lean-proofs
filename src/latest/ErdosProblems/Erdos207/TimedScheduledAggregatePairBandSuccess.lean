/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TimedScheduledAggregatePairBand

/-!
# Positive-probability extraction for the scheduled aggregate phase

Once the probability of leaving the scheduled active region is strictly
below one, a positive-mass terminal trajectory is still active.  The stopped
process terminal certificate then forces its clock to equal the horizon.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem exists_timedScheduledAggregatePairBand_full_phase_of_not_active_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (Kpair Kglobal Kinc Delta delta I Dcut : ℕ)
    (Dschedule dschedule : ℕ → ℕ) (efailure : ℝ)
    (hInv₀ : GreedyInvariant F S₀)
    {Q : GreedyStateOn V → Prop}
    (hQsupport :
      let active := timedScheduledAggregatePairBandActive F Kpair Kglobal
        Kinc Delta delta I Dcut Dschedule dschedule
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      L.SupportedOn (fun z ↦ Q z.2))
    (hfailure :
      let active := timedScheduledAggregatePairBandActive F Kpair Kglobal
        Kinc Delta delta I Dcut Dschedule dschedule
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      (L.probability (fun z ↦ ¬ active z.1.1 z.2) : ℝ) ≤ efailure)
    (hsmall : efailure < 1) :
    ∃ S : GreedyStateOn V,
      Q S ∧ GreedyInvariant F S ∧
        HasAvailablePairCutoff Delta S ∧ HasAvailablePairFloor delta S ∧
        HasPairTwoAwayCutoff F Kpair S ∧ HasTwoAwayCutoff F Kglobal S ∧
        HasPairStarTwoAwayIncidenceCutoff F Kinc S ∧
        totalAvailableTwoAwayIncidences F S ≤ I ∧
        Dcut ≤ S.available.card ∧ Dschedule n ≤ S.available.card ∧
        HasAvailablePairFloor (dschedule n) S ∧
        S.chosen.card = S₀.chosen.card + n := by
  classical
  let active := timedScheduledAggregatePairBandActive F Kpair Kglobal
    Kinc Delta delta I Dcut Dschedule dschedule
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  have hinactiveLt :
      (L.probability (fun z ↦ ¬ active z.1.1 z.2) : ℝ) < 1 := by
    have hfailure' := hfailure
    dsimp only at hfailure'
    exact hfailure'.trans_lt hsmall
  have hgoodReal :
      0 < (L.probability (fun z ↦ ¬ (¬ active z.1.1 z.2)) : ℝ) := by
    rw [L.probability_not]
    rw [NNReal.coe_sub (L.probability_le_one _)]
    norm_num only [NNReal.coe_one]
    exact sub_pos.mpr hinactiveLt
  have hgood : 0 < L.probability (fun z ↦ ¬ (¬ active z.1.1 z.2)) := by
    exact_mod_cast hgoodReal
  obtain ⟨z, hzgood, hmass⟩ :=
    L.exists_of_probability_pos_with_mass hgood
  have hzactive : active z.1.1 z.2 := not_not.mp hzgood
  have htraj : PairTrajectoryInvariant F S₀ z.2 := by
    exact timedScheduledAggregatePairBandProcessLaw_supported_pairTrajectoryInvariant
      (n := n) (Kpair := Kpair) (Kglobal := Kglobal) (Kinc := Kinc)
      (Delta := Delta) (delta := delta) (I := I) (Dcut := Dcut)
      (Dschedule := Dschedule) (dschedule := dschedule) hInv₀ z hmass
  have hcard : z.2.chosen.card = S₀.chosen.card + z.1.1 := by
    exact timedScheduledAggregatePairBandProcessLaw_supported_chosen_card
      (n := n) (Kpair := Kpair) (Kglobal := Kglobal) (Kinc := Kinc)
      (Delta := Delta) (delta := delta) (I := I) (Dcut := Dcut)
      (Dschedule := Dschedule) (dschedule := dschedule) hInv₀ z hmass
  have hQ : Q z.2 := by
    have hQsupport' := hQsupport
    dsimp only at hQsupport'
    exact hQsupport' z hmass
  have hterminal := FiniteLaw.timedStoppedProcessLaw_supported_terminal
    n (fun _ ↦ greedyKernel F) active S₀ z hmass
  have hztime : z.1.1 = n := hterminal.resolve_right hzgood
  have hpairBand : pairBandActiveTwoCutoffs F Kpair Kglobal Delta delta
      z.1.1 z.2 := hzactive.1.1.1
  exact ⟨z.2, hQ, htraj.1, hpairBand.2.1, hpairBand.2.2.2.2,
    hpairBand.2.2.1, hpairBand.2.2.2.1, hzactive.1.2,
    hzactive.1.1.2.1, hzactive.1.1.2.2,
    by simpa only [hztime] using hzactive.2.1,
    by simpa only [hztime] using hzactive.2.2,
    by simpa only [hztime] using hcard⟩

end

end Erdos207
