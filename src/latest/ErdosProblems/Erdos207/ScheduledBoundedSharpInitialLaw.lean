/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.BoundedSharpScheduleEstimates
import ErdosProblems.Erdos207.TimedScheduledAggregatePairBand

/-!
# Initial product law on the synchronized aggregate process
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem timedScheduledAggregatePairBand_boundedSharpInitialProductBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (H : SimpleGraph V) (X : Finset V) (A : TripleSystemOn V)
    (S₀ : GreedyStateOn V)
    (Kpair Kglobal Kinc Delta delta I Dcut d₀ K : ℕ)
    (Dschedule dschedule : ℕ → ℕ)
    (C b : ℝ≥0)
    (hAbs₀ : AbsorberGreedyInvariant F A S₀)
    (houtside₀ : OutsideLeavePairsAlive H X S₀)
    (hchosen₀ : S₀.chosen = ∅)
    (hsmallPair : 3 + Kpair < delta)
    (hactive₀ : timedScheduledAggregatePairBandActive F Kpair Kglobal Kinc
      Delta delta I Dcut Dschedule dschedule 0 S₀)
    (hDcut : 0 < Dcut)
    (hcardV : 0 < Fintype.card V)
    (hd₀M : d₀ ≤ S₀.available.card)
    (heffective : d₀ - 3 * K < S₀.available.card)
    (hdschedule : ∀ i, i < n → dschedule i ≤ d₀)
    (hratio : (n : ℝ≥0) * (Dcut : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hfactor :
      (boundedSharpSurvivalTheta S₀.available.card d₀ (3 * K) ^
        (3 * K))⁻¹ ≤ C)
    (hCp : 1 ≤ C * cumulativeSurvival
      (boundedSharpSurvivalSchedule n (fun _ ↦ S₀.available.card)
        dschedule (3 * K)) n)
    (hC : 1 ≤ C)
    (hCb : 1 ≤ C ^ (K + 1) * b)
    (hinactive :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedScheduledAggregatePairBandActive F Kpair Kglobal Kinc
          Delta delta I Dcut Dschedule dschedule) S₀).probability
        (fun z ↦ ¬ timedScheduledAggregatePairBandActive F Kpair Kglobal
          Kinc Delta delta I Dcut Dschedule dschedule z.1.1 z.2) ≤ b) :
    let p := cumulativeSurvival
      (boundedSharpSurvivalSchedule n (fun _ ↦ S₀.available.card)
        dschedule (3 * K)) n
    IsInitialProductBound
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedScheduledAggregatePairBandActive F Kpair Kglobal Kinc
          Delta delta I Dcut Dschedule dschedule) S₀)
      (fun z ↦ z.2.chosen) p C b := by
  dsimp only
  let active := timedScheduledAggregatePairBandActive F Kpair Kglobal Kinc
    Delta delta I Dcut Dschedule dschedule
  let Inv : GreedyStateOn V → Prop := fun S ↦
    AbsorberGreedyInvariant F A S ∧
      OutsideLeavePairsAlive H X S ∧
      S.available ⊆ S₀.available ∧ S.chosen ⊆ S₀.available
  let M : ℕ → ℕ := fun _ ↦ S₀.available.card
  let D : ℕ → ℕ := fun _ ↦ Dcut
  let p := cumulativeSurvival
    (boundedSharpSurvivalSchedule n M dschedule (3 * K)) n
  have hInv₀ : Inv S₀ := by
    exact ⟨hAbs₀, houtside₀, Subset.rfl, by simpa [hchosen₀]⟩
  have hInvStep : ∀ i, i < n → ∀ S, Inv S → active i S →
      (greedyKernel F S).SupportedOn Inv := by
    intro i _hi S hS hact S' hmass
    have hAbs' : AbsorberGreedyInvariant F A S' :=
      absorberGreedyKernel_supported hS.1 S' hmass
    have hout' : OutsideLeavePairsAlive H X S' := by
      exact greedyKernel_supported_outsideLeavePairsAlive_of_pairCutoff
        hS.2.1 hS.1.1 hact.1.1.1.2.2.1
          hact.1.1.1.2.2.2.2 hsmallPair S' hmass
    have htransition := greedyKernel_supported_step_or_self F S S' hmass
    rcases htransition with rfl | ⟨T, hT, rfl⟩
    · exact ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2⟩
    · refine ⟨hAbs', hout',
        (greedyStep_available_subset F S T).trans hS.2.2.1, ?_⟩
      intro U hU
      rw [greedyStep, mem_insert] at hU
      rcases hU with rfl | hUS
      · exact hS.2.2.1 hT
      · exact hS.2.2.2 hUS
  have hstruct : ∀ S, Inv S →
      IsPackingOn S.chosen ∧ S.chosen ⊆ S₀.available := by
    intro S hS
    exact ⟨hS.1.1.1, hS.2.2.2⟩
  have hfloor : ∀ i S, i < n → Inv S → active i S →
      D i ≤ S.available.card := by
    intro i S _hi _hS hact
    exact hact.1.1.2.2
  have hpairFloor : ∀ i S, i < n → Inv S → active i S →
      HasAvailablePairFloor (dschedule i) S := by
    intro i S _hi _hS hact
    exact hact.2.2
  have hupper : ∀ i S, i < n → Inv S → active i S →
      S.available.card ≤ M i := by
    intro i S _hi hS _hact
    exact card_le_card hS.2.2.1
  have hdM : ∀ i, i < n → dschedule i ≤ M i := by
    intro i hi
    exact (hdschedule i hi).trans hd₀M
  have heffective' : ∀ i, i < n → dschedule i - 3 * K < M i := by
    intro i hi
    exact lt_of_le_of_lt
      (Nat.sub_le_sub_right (hdschedule i hi) (3 * K)) heffective
  have hsurvival : cumulativeSurvival
      (boundedSharpSurvivalSchedule n M dschedule (3 * K)) n ≤ C * p := by
    dsimp only [p]
    calc
      cumulativeSurvival
          (boundedSharpSurvivalSchedule n M dschedule (3 * K)) n =
          1 * cumulativeSurvival
            (boundedSharpSurvivalSchedule n M dschedule (3 * K)) n := by simp
      _ ≤ C * cumulativeSurvival
          (boundedSharpSurvivalSchedule n M dschedule (3 * K)) n := by
        gcongr
  have hpoint : transferPointWeight
      (boundedSharpSurvivalSchedule n M dschedule (3 * K))
      (boundedSharpTransferSchedule n D M dschedule (3 * K)) n ≤
        C * (Fintype.card V : ℝ≥0)⁻¹ := by
    exact transferPointWeight_boundedSharp_const_le hDcut
      (lt_of_le_of_lt (Nat.zero_le _) heffective) hcardV heffective
      hdschedule hratio hfactor
  apply timedStoppedGreedyProcess_boundedSharpInitialProductBound
    n F H X active Inv D dschedule M K S₀ hchosen₀ hInv₀ hactive₀
    hInvStep hstruct (fun S hS ↦ hS.2.1)
    (fun _i _hi ↦ hDcut) hfloor hpairFloor hupper hdM heffective'
    p C b
  · simpa only [active] using hinactive
  · exact hsurvival
  · exact hpoint
  · simpa only [M, p] using hCp
  · exact hC
  · intro Q E hlarge
    exact large_pattern_paid_by_error hlarge hCb hC

end

end Erdos207
