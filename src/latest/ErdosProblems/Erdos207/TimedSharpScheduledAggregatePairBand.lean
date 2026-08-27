/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpScheduledPairConcentration

/-!
# The fully sharp scheduled stopped process

The active region records lower and upper schedules for total availability
and live pair stars.  Its lower total-availability schedule is recovered
deterministically from the surviving outside pairs, so first passage has
only five exceptional events.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def timedSharpScheduledAggregatePairBandActive
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Kpair Kglobal Kinc Delta delta I Dcut : ℕ)
    (D d M u : ℕ → ℕ) (i : ℕ) (S : GreedyStateOn V) : Prop :=
  timedFullyScheduledAggregatePairBandActive F Kpair Kglobal Kinc
      Delta delta I Dcut D d M i S ∧
    HasAvailablePairCutoff (u i) S

theorem timedSharpScheduledAggregatePairBandProcessLaw_supported_pairTrajectoryInvariant
    {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ} {F : ForbiddenFamilyOn V}
    {Kpair Kglobal Kinc Delta delta I Dcut : ℕ}
    {D d M u : ℕ → ℕ} {S₀ : GreedyStateOn V}
    (hInv₀ : GreedyInvariant F S₀) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
      (timedSharpScheduledAggregatePairBandActive F Kpair Kglobal Kinc
        Delta delta I Dcut D d M u) S₀).SupportedOn
      (fun z ↦ PairTrajectoryInvariant F S₀ z.2) := by
  apply FiniteLaw.timedStoppedProcessLaw_supported n (fun _ ↦ greedyKernel F)
    (timedSharpScheduledAggregatePairBandActive F Kpair Kglobal Kinc
      Delta delta I Dcut D d M u)
    S₀ (pairTrajectoryInvariant_initial hInv₀)
  intro _i _hi S hS
  exact greedyKernel_supported_pairTrajectoryInvariant hS

theorem timedSharpScheduledAggregatePairBandProcessLaw_supported_chosen_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ} {F : ForbiddenFamilyOn V}
    {Kpair Kglobal Kinc Delta delta I Dcut : ℕ}
    {D d M u : ℕ → ℕ} {S₀ : GreedyStateOn V}
    (hInv₀ : GreedyInvariant F S₀) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
      (timedSharpScheduledAggregatePairBandActive F Kpair Kglobal Kinc
        Delta delta I Dcut D d M u) S₀).SupportedOn
      (fun z ↦ z.2.chosen.card = S₀.chosen.card + z.1.1) := by
  let z₀ : FiniteLaw.TimedState (GreedyStateOn V) n := (⟨0, by omega⟩, S₀)
  have hstrong :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedSharpScheduledAggregatePairBandActive F Kpair Kglobal Kinc
          Delta delta I Dcut D d M u) S₀).SupportedOn
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
    · have havailable : z.2.available.Nonempty := hrun.2.1.1.1.1.1.1
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

theorem timedSharpScheduledAggregatePairBandProcessLaw_supported_outsideLeavePairsAlive
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (H : SimpleGraph V) (X : Finset V)
    (S₀ : GreedyStateOn V) (Kpair Kglobal Kinc Delta delta I Dcut : ℕ)
    (D d M u : ℕ → ℕ)
    (hInv₀ : GreedyInvariant F S₀)
    (houtside₀ : OutsideLeavePairsAlive H X S₀)
    (hsmall : 3 + Kpair < delta) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
      (timedSharpScheduledAggregatePairBandActive F Kpair Kglobal Kinc
        Delta delta I Dcut D d M u) S₀).SupportedOn
      (fun z ↦ OutsideLeavePairsAlive H X z.2) := by
  have hsupport :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedSharpScheduledAggregatePairBandActive F Kpair Kglobal Kinc
          Delta delta I Dcut D d M u) S₀).SupportedOn
        (fun z ↦ GreedyInvariant F z.2 ∧ OutsideLeavePairsAlive H X z.2) := by
    apply (FiniteLaw.supportedOn_pure
      (fun z : FiniteLaw.TimedState (GreedyStateOn V) n ↦
        GreedyInvariant F z.2 ∧ OutsideLeavePairsAlive H X z.2)
      ⟨hInv₀, houtside₀⟩).evolveKernels
    intro _i z hz
    classical
    unfold FiniteLaw.timedStoppedKernel
    split_ifs with hactive
    · have hout := greedyKernel_supported_outsideLeavePairsAlive_of_pairCutoff
          hz.2 hz.1 hactive.2.1.1.1.1.1.2.2.1
            hactive.2.1.1.1.1.1.2.2.2.2 hsmall
      have hboth : (greedyKernel F z.2).SupportedOn
          (fun S' ↦ GreedyInvariant F S' ∧ OutsideLeavePairsAlive H X S') := by
        intro S' hmass
        exact ⟨greedyKernel_supported hz.1 S' hmass, hout S' hmass⟩
      exact hboth.map (fun S' ↦ (FiniteLaw.advanceTime z.1 hactive.1, S'))
        (fun _S' hS' ↦ hS')
    · exact FiniteLaw.supportedOn_pure _ hz
  exact fun z hmass ↦ (hsupport z hmass).2

theorem probability_timedSharpScheduledAggregatePairBand_exists_pair_deviation_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (Kpair Kglobal Kinc Delta delta I Dcut JUpper : ℕ)
    (D d M u : ℕ → ℕ) (theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀)
    (hDpos : ∀ i, i < n → 0 < D i)
    (hDgap : ∀ i, i < n → u i < D i)
    (hdone : ∀ i, i < n → 1 ≤ d i)
    (hsmall : ∀ i, i < n → 3 + Kpair < d i)
    (hupperJump : ∀ i, i < n →
      sharpScheduledPairUpperRate (M i) (d i) (u i) ≤ JUpper)
    (hlowerDeath : ∀ i, i < n →
      sharpScheduledPairLowerRate (D i) (u i) Kinc ≤ d i)
    (hvarianceUpper : ∀ i, i < n →
      sharpScheduledPairUpperVariance (D i) (u i) Kpair Kglobal
        (sharpScheduledPairUpperRate (M i) (d i) (u i)) ≤ v)
    (hvarianceLower : ∀ i, i < n →
      sharpScheduledPairLowerVariance (D i) (u i) Kpair Kinc
        (sharpScheduledPairLowerRate (D i) (u i) Kinc) ≤ v)
    (htheta : 0 < theta)
    (hthetaUpper : theta * (JUpper : ℝ) ≤ 1)
    (hthetaLower : theta * ((3 + Kpair : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
      Kinc Delta delta I Dcut D d M u
    let qUpper := sharpScheduledPairUpperTarget S₀ M d u
    let qLower := sharpScheduledPairLowerTarget S₀ D u Kinc
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
  apply probability_timedStoppedGreedy_exists_pair_sharpScheduled_deviation_le
    n F (timedSharpScheduledAggregatePairBandActive F Kpair Kglobal Kinc
      Delta delta I Dcut D d M u) S₀ D d M u Kpair Kglobal Kinc JUpper
      theta a v hInv₀ hDpos
  · intro _i _hi _S _hS hactive; exact hactive.1.1.2.1
  · exact hDgap
  · intro _i _hi _S _hS hactive; exact hactive.1.2
  · intro _i _hi _S _hS hactive; exact hactive.1.1.2.2
  · intro _i _hi _S _hS hactive; exact hactive.2
  · intro _i _hi _S _hS hactive; exact hactive.1.1.1.1.1.2.2.1
  · intro _i _hi _S _hS hactive; exact hactive.1.1.1.1.1.2.2.2.1
  · intro _i _hi _S _hS hactive; exact hactive.1.1.1.2
  · exact hdone
  · exact hsmall
  · exact hupperJump
  · exact hlowerDeath
  · exact hvarianceUpper
  · exact hvarianceLower
  · exact htheta
  · exact hthetaUpper
  · exact hthetaLower
  · exact hv

/-- First passage is controlled by pair deviations and the four structural
cutoffs.  The scheduled lower availability bound is a deterministic
consequence of the scheduled pair floor and outside-pair survival. -/
theorem probability_timedSharpScheduledAggregatePairBand_not_active_le_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (H : SimpleGraph V) (X : Finset V)
    (S₀ : GreedyStateOn V)
    (Kpair Kglobal Kinc Delta delta I Dcut : ℕ)
    (D d M u : ℕ → ℕ) (aPair : ℝ)
    (epair epairTwo eglobalTwo einc etotal : ℝ≥0)
    (hInv₀ : GreedyInvariant F S₀)
    (houtside₀ : OutsideLeavePairsAlive H X S₀)
    (hchosen₀ : S₀.chosen = ∅)
    (hsmallBase : 3 + Kpair < delta)
    (hDpos : ∀ i, i ≤ n → 0 < D i)
    (hDcut : ∀ i, i ≤ n → Dcut ≤ D i)
    (hbaseCap : ∀ P : PairOn V, ∀ i, i ≤ n →
      sharpScheduledPairUpperTarget S₀ M d u P i + aPair ≤
        ((Delta + 1 : ℕ) : ℝ))
    (hbaseFloor : ∀ P : PairOn V, ∀ i, i ≤ n → PairAlive P.1 S₀ →
      (delta : ℝ) ≤
        sharpScheduledPairLowerTarget S₀ D u Kinc P i - aPair)
    (hscheduledCap : ∀ P : PairOn V, ∀ i, i ≤ n →
      sharpScheduledPairUpperTarget S₀ M d u P i + aPair ≤
        ((u i + 1 : ℕ) : ℝ))
    (hscheduledFloor : ∀ P : PairOn V, ∀ i, i ≤ n → PairAlive P.1 S₀ →
      (d i : ℝ) ≤
        sharpScheduledPairLowerTarget S₀ D u Kinc P i - aPair)
    (hDschedule : ∀ i, i ≤ n →
      D i ≤ (Nat.choose (Fintype.card V) 2 - 3 * i -
          (graphEdges H).card - X.sym2.card) * d i / 3)
    (hMschedule : ∀ i, i ≤ n →
      ((Nat.choose (Fintype.card V) 2 - 3 * i) * u i) / 3 ≤ M i)
    (hpair :
      let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
        Kinc Delta delta I Dcut D d M u
      let qUpper := sharpScheduledPairUpperTarget S₀ M d u
      let qLower := sharpScheduledPairLowerTarget S₀ D u Kinc
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
      let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
        Kinc Delta delta I Dcut D d M u
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      L.probability (fun z ↦ ¬ HasPairTwoAwayCutoff F Kpair z.2) ≤ epairTwo)
    (hglobalTwo :
      let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
        Kinc Delta delta I Dcut D d M u
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      L.probability (fun z ↦ ¬ HasTwoAwayCutoff F Kglobal z.2) ≤ eglobalTwo)
    (hincBad :
      let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
        Kinc Delta delta I Dcut D d M u
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      L.probability
        (fun z ↦ ¬ HasPairStarTwoAwayIncidenceCutoff F Kinc z.2) ≤ einc)
    (htotal :
      let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
        Kinc Delta delta I Dcut D d M u
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      L.probability
        (fun z ↦ I < totalAvailableTwoAwayIncidences F z.2) ≤ etotal) :
    let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
      Kinc Delta delta I Dcut D d M u
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    L.probability (fun z ↦ ¬ active z.1.1 z.2) ≤
      epair + epairTwo + eglobalTwo + einc + etotal := by
  classical
  dsimp only
  let active := timedSharpScheduledAggregatePairBandActive F Kpair Kglobal
    Kinc Delta delta I Dcut D d M u
  let qUpper := sharpScheduledPairUpperTarget S₀ M d u
  let qLower := sharpScheduledPairLowerTarget S₀ D u Kinc
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
  let badAt : Fin 5 → FiniteLaw.TimedState (GreedyStateOn V) n → Prop
    | ⟨0, _⟩ => pairBad
    | ⟨1, _⟩ => fun z ↦ ¬ HasPairTwoAwayCutoff F Kpair z.2
    | ⟨2, _⟩ => fun z ↦ ¬ HasTwoAwayCutoff F Kglobal z.2
    | ⟨3, _⟩ => fun z ↦ ¬ HasPairStarTwoAwayIncidenceCutoff F Kinc z.2
    | ⟨4, _⟩ => fun z ↦ I < totalAvailableTwoAwayIncidences F z.2
  let eps : Fin 5 → ℝ≥0
    | ⟨0, _⟩ => epair
    | ⟨1, _⟩ => epairTwo
    | ⟨2, _⟩ => eglobalTwo
    | ⟨3, _⟩ => einc
    | ⟨4, _⟩ => etotal
  have htraj : L.SupportedOn
      (fun z ↦ PairTrajectoryInvariant F S₀ z.2) := by
    simpa only [L, active] using
      timedSharpScheduledAggregatePairBandProcessLaw_supported_pairTrajectoryInvariant
        (n := n) (Kpair := Kpair) (Kglobal := Kglobal) (Kinc := Kinc)
        (Delta := Delta) (delta := delta) (I := I) (Dcut := Dcut)
        (D := D) (d := d) (M := M) (u := u) hInv₀
  have hcard : L.SupportedOn
      (fun z ↦ z.2.chosen.card = S₀.chosen.card + z.1.1) := by
    simpa only [L, active] using
      timedSharpScheduledAggregatePairBandProcessLaw_supported_chosen_card
        (n := n) (Kpair := Kpair) (Kglobal := Kglobal) (Kinc := Kinc)
        (Delta := Delta) (delta := delta) (I := I) (Dcut := Dcut)
        (D := D) (d := d) (M := M) (u := u) hInv₀
  have houtside : L.SupportedOn
      (fun z ↦ OutsideLeavePairsAlive H X z.2) := by
    simpa only [L, active] using
      timedSharpScheduledAggregatePairBandProcessLaw_supported_outsideLeavePairsAlive
        n F H X S₀ Kpair Kglobal Kinc Delta delta I Dcut D d M u
          hInv₀ houtside₀ hsmallBase
  have hsupport : L.SupportedOn (fun z ↦
      PairTrajectoryInvariant F S₀ z.2 ∧
        z.2.chosen.card = S₀.chosen.card + z.1.1 ∧
        OutsideLeavePairsAlive H X z.2) := by
    intro z hmass
    exact ⟨htraj z hmass, hcard z hmass, houtside z hmass⟩
  have hinactiveUnion : L.probability (fun z ↦ ¬ active z.1.1 z.2) ≤
      L.probability (fun z ↦ ∃ j : Fin 5, badAt j z) := by
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
    have htime : z.1.1 ≤ n := by omega
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
    have hdfloor : HasAvailablePairFloor (d z.1.1) z.2 :=
      hasAvailablePairFloor_of_lowerDeviations_lt qLower z.1.1
        (d z.1.1) aPair hz.1.2
        (by
          intro P halive
          simpa [qLower, sharpScheduledPairLowerTarget_zero] using
            hscheduledFloor P z.1.1 htime halive)
        hlowerDev
    have hDavail : D z.1.1 ≤ z.2.available.card :=
      scheduled_available_floor_of_clock hz.1 hchosen₀ hz.2.1 hdfloor hz.2.2
        (hDschedule z.1.1 htime)
    have hnonempty : z.2.available.Nonempty := by
      rw [← card_pos]
      exact (hDpos z.1.1 htime).trans_le hDavail
    have hpairBand :
        pairBandActiveTwoCutoffs F Kpair Kglobal Delta delta z.1.1 z.2 :=
      pairBandActiveTwoCutoffs_of_deviations_lt qUpper qLower z.1.1
        Kpair Kglobal Delta delta aPair hz.1.2 hnonempty hpairTwoGood
        hglobalTwoGood
        (by
          intro P
          simpa [qUpper, sharpScheduledPairUpperTarget_zero] using
            hbaseCap P z.1.1 htime)
        (by
          intro P halive
          simpa [qLower, sharpScheduledPairLowerTarget_zero] using
            hbaseFloor P z.1.1 htime halive)
        hupperDev hlowerDev
    have hbase : timedAggregateAveragePairBandActive F Kpair Kglobal Kinc
        Delta delta I Dcut z.1.1 z.2 :=
      ⟨⟨hpairBand, htotalGood, (hDcut z.1.1 htime).trans hDavail⟩,
        hincGood⟩
    have hucut : HasAvailablePairCutoff (u z.1.1) z.2 :=
      hasAvailablePairCutoff_of_upperDeviations_lt qUpper z.1.1
        (u z.1.1) aPair hz.1.2
        (by
          intro P
          simpa [qUpper, sharpScheduledPairUpperTarget_zero] using
            hscheduledCap P z.1.1 htime)
        hupperDev
    have hMraw : z.2.available.card ≤
        ((Nat.choose (Fintype.card V) 2 - 3 * z.1.1) * u z.1.1) / 3 := by
      have hpairCut : HasAvailablePairCutoff (u z.1.1) z.2 := hucut
      have hcount :=
        available_card_le_choose_sub_chosen_mul_pairCutoff_div_three
          hz.1.1 hpairCut
      rw [hz.2.1, hchosen₀] at hcount
      simpa only [card_empty, zero_add] using hcount
    have hMavail : z.2.available.card ≤ M z.1.1 :=
      hMraw.trans (hMschedule z.1.1 htime)
    exact hnotactive ⟨⟨⟨hbase, hDavail, hdfloor⟩, hMavail⟩, hucut⟩
  have hunion := L.probability_exists_le (univ : Finset (Fin 5)) badAt
  have hbadAt : ∀ j : Fin 5, L.probability (badAt j) ≤ eps j := by
    intro j
    fin_cases j
    · simpa [L, active, qUpper, qLower, badAt, pairBad, eps] using hpair
    · simpa [L, active, badAt, eps] using hpairTwo
    · simpa [L, active, badAt, eps] using hglobalTwo
    · simpa [L, active, badAt, eps] using hincBad
    · simpa [L, active, badAt, eps] using htotal
  calc
    L.probability (fun z ↦ ¬ active z.1.1 z.2) ≤
        L.probability (fun z ↦ ∃ j : Fin 5, badAt j z) := hinactiveUnion
    _ ≤ ∑ j : Fin 5, L.probability (badAt j) := by simpa using hunion
    _ ≤ ∑ j : Fin 5, eps j := by
      apply sum_le_sum
      intro j _hj
      exact hbadAt j
    _ = epair + epairTwo + eglobalTwo + einc + etotal := by
      simp [eps, Fin.sum_univ_succ]
      ring

end

end Erdos207
