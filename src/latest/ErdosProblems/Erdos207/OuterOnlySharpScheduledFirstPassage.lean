/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.OuterOnlyResidualDegree
import ErdosProblems.Erdos207.TimedSharpScheduledAggregatePairBand
import ErdosProblems.Erdos207.OuterOnlyExactAvailability

/-!
# First passage with the exact outer-only clock

For an outer-only phase, packinghood and the exact clock sharpen the available-
triple count.  This file threads that count through the five-event sharp
scheduled first-passage argument.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The five-event first-passage estimate using the exact outer-only clock. -/
theorem probability_timedSharpScheduledAggregatePairBand_not_active_le_sum_outerOnly
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (G : SimpleGraph V)
    (U : Finset V) (A : TripleSystemOn V) (S₀ : GreedyStateOn V)
    (Kpair Kglobal Kinc Delta delta I Dcut : ℕ)
    (D d M u : ℕ → ℕ) (aPair : ℝ)
    (epair epairTwo eglobalTwo einc etotal : ℝ≥0)
    (hAbs₀ : AbsorberGreedyInvariant F (outerOnlyAvailable U A) S₀)
    (htri : ConsistsOfTriangles G A)
    (houtside₀ : OutsideLeavePairsAlive (internalOuterGraph G U)ᶜ U S₀)
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
          (graphEdges (internalOuterGraph G U)ᶜ).card) * d i / 3)
    (hMschedule : ∀ i, i ≤ n →
      ((Nat.choose (Fintype.card V) 2 - 3 * i -
          (graphEdges (internalOuterGraph G U)ᶜ).card) * u i) / 3 ≤ M i)
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
  have hAbs : L.SupportedOn (fun z ↦
      AbsorberGreedyInvariant F (outerOnlyAvailable U A) z.2) := by
    apply FiniteLaw.timedStoppedProcessLaw_supported n
      (fun _ ↦ greedyKernel F) active S₀ hAbs₀
    intro _i _hi S hS
    exact absorberGreedyKernel_supported hS
  have htraj : L.SupportedOn
      (fun z ↦ PairTrajectoryInvariant F S₀ z.2) := by
    simpa only [L, active] using
      timedSharpScheduledAggregatePairBandProcessLaw_supported_pairTrajectoryInvariant
        (n := n) (Kpair := Kpair) (Kglobal := Kglobal) (Kinc := Kinc)
        (Delta := Delta) (delta := delta) (I := I) (Dcut := Dcut)
        (D := D) (d := d) (M := M) (u := u) hAbs₀.1
  have hcard : L.SupportedOn
      (fun z ↦ z.2.chosen.card = S₀.chosen.card + z.1.1) := by
    simpa only [L, active] using
      timedSharpScheduledAggregatePairBandProcessLaw_supported_chosen_card
        (n := n) (Kpair := Kpair) (Kglobal := Kglobal) (Kinc := Kinc)
        (Delta := Delta) (delta := delta) (I := I) (Dcut := Dcut)
        (D := D) (d := d) (M := M) (u := u) hAbs₀.1
  have houtside : L.SupportedOn
      (fun z ↦ OutsideLeavePairsAlive (internalOuterGraph G U)ᶜ U z.2) := by
    simpa only [L, active] using
      timedSharpScheduledAggregatePairBandProcessLaw_supported_outsideLeavePairsAlive
        n F (internalOuterGraph G U)ᶜ U S₀ Kpair Kglobal Kinc Delta delta I Dcut D d M u
          hAbs₀.1 houtside₀ hsmallBase
  have hsupport : L.SupportedOn (fun z ↦
      AbsorberGreedyInvariant F (outerOnlyAvailable U A) z.2 ∧
        PairTrajectoryInvariant F S₀ z.2 ∧
        z.2.chosen.card = S₀.chosen.card + z.1.1 ∧
        OutsideLeavePairsAlive (internalOuterGraph G U)ᶜ U z.2) := by
    intro z hmass
    exact ⟨hAbs z hmass, htraj z hmass, hcard z hmass, houtside z hmass⟩
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
        (d z.1.1) aPair hz.2.1.2
        (by
          intro P halive
          simpa [qLower, sharpScheduledPairLowerTarget_zero] using
            hscheduledFloor P z.1.1 htime halive)
        hlowerDev
    have hchosenCard : z.2.chosen.card = z.1.1 := by
      rw [hz.2.2.1, hchosen₀]
      simp
    have hDavail : D z.1.1 ≤ z.2.available.card :=
      scheduled_available_floor_outerOnly_exact hz.1 htri hz.2.2.2
        hchosenCard hdfloor (hDschedule z.1.1 htime)
    have hnonempty : z.2.available.Nonempty := by
      rw [← card_pos]
      exact (hDpos z.1.1 htime).trans_le hDavail
    have hpairBand :
        pairBandActiveTwoCutoffs F Kpair Kglobal Delta delta z.1.1 z.2 :=
      pairBandActiveTwoCutoffs_of_deviations_lt qUpper qLower z.1.1
        Kpair Kglobal Delta delta aPair hz.2.1.2 hnonempty hpairTwoGood
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
    have hucut : HasAvailablePairCutoff (u z.1.1) z.2 :=
      hasAvailablePairCutoff_of_upperDeviations_lt qUpper z.1.1
        (u z.1.1) aPair hz.2.1.2
        (by
          intro P
          simpa [qUpper, sharpScheduledPairUpperTarget_zero] using
            hscheduledCap P z.1.1 htime)
        hupperDev
    have hbase : timedAggregateAveragePairBandActive F Kpair Kglobal Kinc
        Delta delta I Dcut z.1.1 z.2 :=
      ⟨⟨hpairBand, htotalGood, (hDcut z.1.1 htime).trans hDavail⟩,
        hincGood⟩
    have hMavail : z.2.available.card ≤ M z.1.1 :=
      scheduled_available_ceiling_outerOnly_exact hz.1 htri hchosenCard
        hucut (hMschedule z.1.1 htime)
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
