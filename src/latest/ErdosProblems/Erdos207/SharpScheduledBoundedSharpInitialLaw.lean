/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TimedSharpScheduledAggregatePairBand
import ErdosProblems.Erdos207.BoundedSharpInitialLaw

/-! # The bounded initial product law for the fully sharp stopped process -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem timedSharpScheduledAggregatePairBand_boundedSharpInitialProductBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (H : SimpleGraph V) (X : Finset V) (A : TripleSystemOn V)
    (S₀ : GreedyStateOn V)
    (Kpair Kglobal Kinc Delta delta I Dcut K : ℕ)
    (D d M u : ℕ → ℕ)
    (p C b : ℝ≥0)
    (hAbs₀ : AbsorberGreedyInvariant F A S₀)
    (houtside₀ : OutsideLeavePairsAlive H X S₀)
    (hchosen₀ : S₀.chosen = ∅)
    (hsmallPair : 3 + Kpair < delta)
    (hactive₀ : timedSharpScheduledAggregatePairBandActive F Kpair Kglobal Kinc
      Delta delta I Dcut D d M u 0 S₀)
    (hD : ∀ i, i < n → 0 < D i)
    (hdM : ∀ i, i < n → d i ≤ M i)
    (heffective : ∀ i, i < n → d i - 3 * K < M i)
    (hinactive :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedSharpScheduledAggregatePairBandActive F Kpair Kglobal Kinc
          Delta delta I Dcut D d M u) S₀).probability
        (fun z ↦ ¬ timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
          Kinc Delta delta I Dcut D d M u z.1.1 z.2) ≤ b)
    (hsurvival : cumulativeSurvival
        (boundedSharpSurvivalSchedule n M d (3 * K)) n ≤ C * p)
    (hpoint : transferPointWeight
        (boundedSharpSurvivalSchedule n M d (3 * K))
        (boundedSharpTransferSchedule n D M d (3 * K)) n ≤
      C * (Fintype.card V : ℝ≥0)⁻¹)
    (hCp : 1 ≤ C * p) (hC : 1 ≤ C)
    (hlarge : ∀ (Q : TripleSystemOn V) (E : Finset (Sym2 V)),
      K < Q.card + E.card →
      1 ≤ C ^ (Q.card + E.card) *
        (p ^ E.card *
          (Fintype.card V : ℝ≥0)⁻¹ ^ Q.card + b)) :
    IsInitialProductBound
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedSharpScheduledAggregatePairBandActive F Kpair Kglobal Kinc
          Delta delta I Dcut D d M u) S₀)
      (fun z ↦ z.2.chosen) p C b := by
  let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal Kinc
    Delta delta I Dcut D d M u
  let Inv : GreedyStateOn V → Prop := fun S ↦
    AbsorberGreedyInvariant F A S ∧
      OutsideLeavePairsAlive H X S ∧
      S.available ⊆ S₀.available ∧ S.chosen ⊆ S₀.available
  have hInv₀ : Inv S₀ := by
    exact ⟨hAbs₀, houtside₀, Subset.rfl, by simpa [hchosen₀]⟩
  have hInvStep : ∀ i, i < n → ∀ S, Inv S → active i S →
      (greedyKernel F S).SupportedOn Inv := by
    intro i _hi S hS hact S' hmass
    have hAbs' : AbsorberGreedyInvariant F A S' :=
      absorberGreedyKernel_supported hS.1 S' hmass
    have hout' : OutsideLeavePairsAlive H X S' := by
      exact greedyKernel_supported_outsideLeavePairsAlive_of_pairCutoff
        hS.2.1 hS.1.1 hact.1.1.1.1.1.2.2.1
          hact.1.1.1.1.1.2.2.2.2 hsmallPair S' hmass
    rcases greedyKernel_supported_step_or_self F S S' hmass with
      rfl | ⟨T, hT, rfl⟩
    · exact ⟨hS.1, hS.2.1, hS.2.2.1, hS.2.2.2⟩
    · refine ⟨hAbs', hout',
        (greedyStep_available_subset F S T).trans hS.2.2.1, ?_⟩
      intro U hU
      rw [greedyStep, mem_insert] at hU
      rcases hU with rfl | hUS
      · exact hS.2.2.1 hT
      · exact hS.2.2.2 hUS
  apply timedStoppedGreedyProcess_boundedSharpInitialProductBound
    n F H X active Inv D d M K S₀ hchosen₀ hInv₀ hactive₀ hInvStep
    (fun S hS ↦ ⟨hS.1.1.1, hS.2.2.2⟩)
    (fun S hS ↦ hS.2.1) hD
  · intro i S _hi _hS hact
    exact hact.1.1.2.1
  · intro i S _hi _hS hact
    exact hact.1.1.2.2
  · intro i S _hi _hS hact
    exact hact.1.2
  · exact hdM
  · exact heffective
  · exact hinactive
  · exact hsurvival
  · exact hpoint
  · exact hCp
  · exact hC
  · exact hlarge

end

end Erdos207
