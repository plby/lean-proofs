/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TimedAggregateAveragePairBand
import Mathlib.Algebra.BigOperators.Fin

/-! # Positive-probability extraction for the corrected averaged phase -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Quantitative first-passage form of the six-event argument.  The
probability that the aggregate process has left its active region is at most
the sum of the pair-band, cutoff, incidence, and availability failure
probabilities. -/
theorem probability_timedAggregateAveragePairBand_not_active_le_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S0 : GreedyStateOn V)
    (qUpper qLower : PairOn V → ℕ → ℝ)
    (Kpair Kglobal Kinc Delta delta I D : ℕ) (aPair aAvail : ℝ)
    (epair epairTwo eglobalTwo einc etotal eavail : ℝ≥0)
    (hInv0 : GreedyInvariant F S0) (hD : 0 < D)
    (havailabilityBuffer : ∀ i, i ≤ n →
      (D : ℝ) + (i : ℝ) * averageAvailabilityLossRate Delta I D + aAvail ≤
        (S0.available.card : ℝ))
    (hcap : ∀ P : PairOn V, ∀ i, i ≤ n →
      qUpper P i +
          (fixedPairAvailableCountReal S0 P.1 S0 - qUpper P 0) + aPair ≤
        ((Delta + 1 : ℕ) : ℝ))
    (htargetFloor : ∀ P : PairOn V, ∀ i, i ≤ n →
      PairAlive P.1 S0 →
      (delta : ℝ) ≤ qLower P i +
          (fixedPairAvailableCountReal S0 P.1 S0 - qLower P 0) - aPair)
    (hpair :
      let active := timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S0
      L.probability (fun z ↦ ∃ P : PairOn V,
        (PairAlive P.1 z.2 ∧
          aPair ≤ fixedPairUpperDeviation (qUpper P) S0 P.1 z.1.1 z.2 -
            fixedPairUpperDeviation (qUpper P) S0 P.1 0 S0) ∨
        (PairAlive P.1 z.2 ∧
          aPair ≤ fixedPairLowerDeviation (qLower P) S0 P.1 z.1.1 z.2 -
            fixedPairLowerDeviation (qLower P) S0 P.1 0 S0)) ≤ epair)
    (hpairTwo :
      let active := timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S0
      L.probability (fun z ↦ ¬ HasPairTwoAwayCutoff F Kpair z.2) ≤ epairTwo)
    (hglobalTwo :
      let active := timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S0
      L.probability (fun z ↦ ¬ HasTwoAwayCutoff F Kglobal z.2) ≤ eglobalTwo)
    (hinc :
      let active := timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S0
      L.probability
        (fun z ↦ ¬ HasPairStarTwoAwayIncidenceCutoff F Kinc z.2) ≤ einc)
    (htotal :
      let active := timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S0
      L.probability
        (fun z ↦ I < totalAvailableTwoAwayIncidences F z.2) ≤ etotal)
    (havail :
      let active := timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S0
      L.probability (fun z ↦
        aAvail ≤ averageAvailabilityDeficit
            (averageAvailabilityLossRate Delta I D) z.1.1 z.2 -
          averageAvailabilityDeficit
            (averageAvailabilityLossRate Delta I D) 0 S0) ≤ eavail) :
    let active := timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S0
    L.probability (fun z ↦ ¬ active z.1.1 z.2) ≤
      epair + epairTwo + eglobalTwo + einc + etotal + eavail := by
  classical
  dsimp only
  let active := timedAggregateAveragePairBandActive
    F Kpair Kglobal Kinc Delta delta I D
  let L := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S0
  let pairBad : FiniteLaw.TimedState (GreedyStateOn V) n → Prop := fun z ↦
    ∃ P : PairOn V,
      (PairAlive P.1 z.2 ∧
        aPair ≤ fixedPairUpperDeviation (qUpper P) S0 P.1 z.1.1 z.2 -
          fixedPairUpperDeviation (qUpper P) S0 P.1 0 S0) ∨
      (PairAlive P.1 z.2 ∧
        aPair ≤ fixedPairLowerDeviation (qLower P) S0 P.1 z.1.1 z.2 -
          fixedPairLowerDeviation (qLower P) S0 P.1 0 S0)
  let badAt : Fin 6 → FiniteLaw.TimedState (GreedyStateOn V) n → Prop
    | ⟨0, _⟩ => pairBad
    | ⟨1, _⟩ => fun z ↦ ¬ HasPairTwoAwayCutoff F Kpair z.2
    | ⟨2, _⟩ => fun z ↦ ¬ HasTwoAwayCutoff F Kglobal z.2
    | ⟨3, _⟩ => fun z ↦ ¬ HasPairStarTwoAwayIncidenceCutoff F Kinc z.2
    | ⟨4, _⟩ => fun z ↦ I < totalAvailableTwoAwayIncidences F z.2
    | ⟨5, _⟩ => fun z ↦
        aAvail ≤ averageAvailabilityDeficit
            (averageAvailabilityLossRate Delta I D) z.1.1 z.2 -
          averageAvailabilityDeficit
            (averageAvailabilityLossRate Delta I D) 0 S0
  let eps : Fin 6 → ℝ≥0
    | ⟨0, _⟩ => epair
    | ⟨1, _⟩ => epairTwo
    | ⟨2, _⟩ => eglobalTwo
    | ⟨3, _⟩ => einc
    | ⟨4, _⟩ => etotal
    | ⟨5, _⟩ => eavail
  have htraj : L.SupportedOn (fun z ↦ PairTrajectoryInvariant F S0 z.2) := by
    simpa only [L, active] using
      timedAggregateAveragePairBandProcessLaw_supported_pairTrajectoryInvariant
        (n := n) (Kpair := Kpair) (Kglobal := Kglobal) (Kinc := Kinc)
        (Delta := Delta) (delta := delta) (I := I) (D := D) hInv0
  have hinactiveUnion : L.probability (fun z ↦ ¬ active z.1.1 z.2) ≤
      L.probability (fun z ↦ ∃ j : Fin 6, badAt j z) := by
    apply L.probability_mono_of_supported htraj
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
        averageAvailabilityDeficit (averageAvailabilityLossRate Delta I D)
            z.1.1 z.2 -
          averageAvailabilityDeficit (averageAvailabilityLossRate Delta I D)
            0 S0 < aAvail := by
      exact lt_of_not_ge fun hbad ↦
        hnotbad ⟨⟨5, by omega⟩, by simpa [badAt] using hbad⟩
    have htime : z.1.1 ≤ n := by omega
    have havailability : D ≤ z.2.available.card := by
      have hbuffer := havailabilityBuffer z.1.1 htime
      have hreal : (D : ℝ) < (z.2.available.card : ℝ) := by
        simp only [averageAvailabilityDeficit] at havailGood
        push_cast at havailGood
        nlinarith
      exact_mod_cast hreal.le
    have hnonempty : z.2.available.Nonempty := by
      rw [← card_pos]
      exact hD.trans_le havailability
    have hupperDev : ∀ P : PairOn V, PairAlive P.1 z.2 →
        fixedPairUpperDeviation (qUpper P) S0 P.1 z.1.1 z.2 -
          fixedPairUpperDeviation (qUpper P) S0 P.1 0 S0 < aPair := by
      intro P halive
      exact lt_of_not_ge fun hbad ↦
        hnotPairBad ⟨P, Or.inl ⟨halive, hbad⟩⟩
    have hlowerDev : ∀ P : PairOn V, PairAlive P.1 z.2 →
        fixedPairLowerDeviation (qLower P) S0 P.1 z.1.1 z.2 -
          fixedPairLowerDeviation (qLower P) S0 P.1 0 S0 < aPair := by
      intro P halive
      exact lt_of_not_ge fun hbad ↦
        hnotPairBad ⟨P, Or.inr ⟨halive, hbad⟩⟩
    have hpairBand :
        pairBandActiveTwoCutoffs F Kpair Kglobal Delta delta z.1.1 z.2 :=
      pairBandActiveTwoCutoffs_of_deviations_lt qUpper qLower z.1.1
        Kpair Kglobal Delta delta aPair hz.2 hnonempty hpairTwoGood
        hglobalTwoGood (fun P ↦ hcap P z.1.1 htime)
        (fun P ↦ htargetFloor P z.1.1 htime) hupperDev hlowerDev
    exact hnotactive ⟨⟨hpairBand, htotalGood, havailability⟩, hincGood⟩
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

theorem exists_timedAggregateAveragePairBand_full_phase_of_failure_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S0 : GreedyStateOn V)
    (qUpper qLower : PairOn V → ℕ → ℝ)
    (Kpair Kglobal Kinc Delta delta I D : ℕ) (aPair aAvail : ℝ)
    (epair epairTwo eglobalTwo einc etotal eavail : ℝ)
    (hInv0 : GreedyInvariant F S0) (hD : 0 < D)
    {Q : GreedyStateOn V → Prop}
    (hQsupport :
      let active := timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ => greedyKernel F) active S0
      L.SupportedOn (fun z => Q z.2))
    (havailabilityBuffer : ∀ i, i ≤ n →
      (D : ℝ) + (i : ℝ) * averageAvailabilityLossRate Delta I D + aAvail ≤
        (S0.available.card : ℝ))
    (hcap : ∀ P : PairOn V, ∀ i, i ≤ n →
      qUpper P i +
          (fixedPairAvailableCountReal S0 P.1 S0 - qUpper P 0) + aPair ≤
        ((Delta + 1 : ℕ) : ℝ))
    (htargetFloor : ∀ P : PairOn V, ∀ i, i ≤ n →
      PairAlive P.1 S0 →
      (delta : ℝ) ≤ qLower P i +
          (fixedPairAvailableCountReal S0 P.1 S0 - qLower P 0) - aPair)
    (hpair :
      let active := timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ => greedyKernel F) active S0
      (L.probability (fun z => ∃ P : PairOn V,
        (PairAlive P.1 z.2 ∧
          aPair ≤ fixedPairUpperDeviation (qUpper P) S0 P.1 z.1.1 z.2 -
            fixedPairUpperDeviation (qUpper P) S0 P.1 0 S0) ∨
        (PairAlive P.1 z.2 ∧
          aPair ≤ fixedPairLowerDeviation (qLower P) S0 P.1 z.1.1 z.2 -
            fixedPairLowerDeviation (qLower P) S0 P.1 0 S0)) : ℝ) ≤ epair)
    (hpairTwo :
      let active := timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ => greedyKernel F) active S0
      (L.probability (fun z => ¬ HasPairTwoAwayCutoff F Kpair z.2) : ℝ) ≤
        epairTwo)
    (hglobalTwo :
      let active := timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ => greedyKernel F) active S0
      (L.probability (fun z => ¬ HasTwoAwayCutoff F Kglobal z.2) : ℝ) ≤
        eglobalTwo)
    (hinc :
      let active := timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ => greedyKernel F) active S0
      (L.probability
        (fun z => ¬ HasPairStarTwoAwayIncidenceCutoff F Kinc z.2) : ℝ) ≤ einc)
    (htotal :
      let active := timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ => greedyKernel F) active S0
      (L.probability
        (fun z => I < totalAvailableTwoAwayIncidences F z.2) : ℝ) ≤ etotal)
    (havail :
      let active := timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ => greedyKernel F) active S0
      (L.probability (fun z =>
        aAvail ≤ averageAvailabilityDeficit
            (averageAvailabilityLossRate Delta I D) z.1.1 z.2 -
          averageAvailabilityDeficit
            (averageAvailabilityLossRate Delta I D) 0 S0) : ℝ) ≤ eavail)
    (hsmall : epair + epairTwo + eglobalTwo + einc + etotal + eavail < 1) :
    ∃ S : GreedyStateOn V,
      Q S ∧ GreedyInvariant F S ∧
        HasAvailablePairCutoff Delta S ∧ HasAvailablePairFloor delta S ∧
        HasPairTwoAwayCutoff F Kpair S ∧ HasTwoAwayCutoff F Kglobal S ∧
        HasPairStarTwoAwayIncidenceCutoff F Kinc S ∧
        totalAvailableTwoAwayIncidences F S ≤ I ∧ D ≤ S.available.card ∧
        S.chosen.card = S0.chosen.card + n := by
  classical
  let active := timedAggregateAveragePairBandActive
    F Kpair Kglobal Kinc Delta delta I D
  let L := FiniteLaw.timedStoppedProcessLaw n (fun _ => greedyKernel F) active S0
  let pairBad : FiniteLaw.TimedState (GreedyStateOn V) n → Prop := fun z =>
    ∃ P : PairOn V,
      (PairAlive P.1 z.2 ∧
        aPair ≤ fixedPairUpperDeviation (qUpper P) S0 P.1 z.1.1 z.2 -
          fixedPairUpperDeviation (qUpper P) S0 P.1 0 S0) ∨
      (PairAlive P.1 z.2 ∧
        aPair ≤ fixedPairLowerDeviation (qLower P) S0 P.1 z.1.1 z.2 -
          fixedPairLowerDeviation (qLower P) S0 P.1 0 S0)
  let pairTwoBad : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z => ¬ HasPairTwoAwayCutoff F Kpair z.2
  let globalTwoBad : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z => ¬ HasTwoAwayCutoff F Kglobal z.2
  let incBad : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z => ¬ HasPairStarTwoAwayIncidenceCutoff F Kinc z.2
  let totalBad : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z => I < totalAvailableTwoAwayIncidences F z.2
  let availBad : FiniteLaw.TimedState (GreedyStateOn V) n → Prop := fun z =>
    aAvail ≤ averageAvailabilityDeficit (averageAvailabilityLossRate Delta I D)
        z.1.1 z.2 -
      averageAvailabilityDeficit (averageAvailabilityLossRate Delta I D) 0 S0
  let badAt : Fin 6 → FiniteLaw.TimedState (GreedyStateOn V) n → Prop
    | ⟨0, _⟩ => pairBad
    | ⟨1, _⟩ => pairTwoBad
    | ⟨2, _⟩ => globalTwoBad
    | ⟨3, _⟩ => incBad
    | ⟨4, _⟩ => totalBad
    | ⟨5, _⟩ => availBad
  let epsilon : Fin 6 → ℝ
    | ⟨0, _⟩ => epair
    | ⟨1, _⟩ => epairTwo
    | ⟨2, _⟩ => eglobalTwo
    | ⟨3, _⟩ => einc
    | ⟨4, _⟩ => etotal
    | ⟨5, _⟩ => eavail
  have hbadAt : ∀ j : Fin 6, (L.probability (badAt j) : ℝ) ≤ epsilon j := by
    intro j
    fin_cases j
    · simpa [L, active, badAt, pairBad, epsilon] using hpair
    · simpa [L, active, badAt, pairTwoBad, epsilon] using hpairTwo
    · simpa [L, active, badAt, globalTwoBad, epsilon] using hglobalTwo
    · simpa [L, active, badAt, incBad, epsilon] using hinc
    · simpa [L, active, badAt, totalBad, epsilon] using htotal
    · simpa [L, active, badAt, availBad, epsilon] using havail
  have hunionNN := L.probability_exists_le (univ : Finset (Fin 6)) badAt
  have hunionReal :
      (L.probability (fun z => ∃ j : Fin 6, badAt j z) : ℝ) ≤
        ∑ j : Fin 6, (L.probability (badAt j) : ℝ) := by
    have hraw :
        (L.probability (fun z => ∃ j ∈ (univ : Finset (Fin 6)),
          badAt j z) : ℝ) ≤
          ∑ j : Fin 6, (L.probability (badAt j) : ℝ) := by
      exact_mod_cast hunionNN
    simpa using hraw
  have hfailure :
      (L.probability (fun z => ∃ j : Fin 6, badAt j z) : ℝ) < 1 := by
    calc
      _ ≤ ∑ j : Fin 6, (L.probability (badAt j) : ℝ) := hunionReal
      _ ≤ ∑ j : Fin 6, epsilon j := by
        apply sum_le_sum
        intro j _hj
        exact hbadAt j
      _ = epair + epairTwo + eglobalTwo + einc + etotal + eavail := by
        simp [epsilon, Fin.sum_univ_succ]
        ring
      _ < 1 := hsmall
  have hgoodReal :
      0 < (L.probability (fun z => ¬ ∃ j : Fin 6, badAt j z) : ℝ) := by
    rw [L.probability_not]
    rw [NNReal.coe_sub (L.probability_le_one _)]
    norm_num only [NNReal.coe_one]
    exact sub_pos.mpr hfailure
  have hgood : 0 < L.probability (fun z => ¬ ∃ j : Fin 6, badAt j z) := by
    exact_mod_cast hgoodReal
  obtain ⟨z, hzgood, hmass⟩ := L.exists_of_probability_pos_with_mass hgood
  have htraj : PairTrajectoryInvariant F S0 z.2 :=
    timedAggregateAveragePairBandProcessLaw_supported_pairTrajectoryInvariant
      (n := n) (Kpair := Kpair) (Kglobal := Kglobal) (Kinc := Kinc)
      (Delta := Delta) (delta := delta) (I := I) (D := D) hInv0 z hmass
  have hcard : z.2.chosen.card = S0.chosen.card + z.1.1 :=
    timedAggregateAveragePairBandProcessLaw_supported_chosen_card
      (n := n) (Kpair := Kpair) (Kglobal := Kglobal) (Kinc := Kinc)
      (Delta := Delta) (delta := delta) (I := I) (D := D) hInv0 z hmass
  have hQ : Q z.2 := hQsupport z hmass
  have hterminal := FiniteLaw.timedStoppedProcessLaw_supported_terminal
    n (fun _ => greedyKernel F) active S0 z hmass
  have hnotPairBad : ¬ pairBad z := by
    intro hbad
    exact hzgood ⟨⟨0, by omega⟩, by simpa [badAt] using hbad⟩
  have hpairTwoGood : HasPairTwoAwayCutoff F Kpair z.2 := by
    by_contra hbad
    exact hzgood ⟨⟨1, by omega⟩, by simpa [badAt, pairTwoBad] using hbad⟩
  have hglobalTwoGood : HasTwoAwayCutoff F Kglobal z.2 := by
    by_contra hbad
    exact hzgood ⟨⟨2, by omega⟩, by simpa [badAt, globalTwoBad] using hbad⟩
  have hincGood : HasPairStarTwoAwayIncidenceCutoff F Kinc z.2 := by
    by_contra hbad
    exact hzgood ⟨⟨3, by omega⟩, by simpa [badAt, incBad] using hbad⟩
  have htotalGood : totalAvailableTwoAwayIncidences F z.2 ≤ I := by
    by_contra hbad
    have hbad' : I < totalAvailableTwoAwayIncidences F z.2 := by omega
    exact hzgood ⟨⟨4, by omega⟩, by simpa [badAt, totalBad] using hbad'⟩
  have havailGood :
      averageAvailabilityDeficit (averageAvailabilityLossRate Delta I D)
          z.1.1 z.2 -
        averageAvailabilityDeficit (averageAvailabilityLossRate Delta I D)
          0 S0 < aAvail := by
    exact lt_of_not_ge fun hbad =>
      hzgood ⟨⟨5, by omega⟩, by simpa [badAt, availBad] using hbad⟩
  have htime : z.1.1 ≤ n := by omega
  have havailability : D ≤ z.2.available.card := by
    have hbuffer := havailabilityBuffer z.1.1 htime
    have hreal : (D : ℝ) < (z.2.available.card : ℝ) := by
      simp only [averageAvailabilityDeficit] at havailGood
      push_cast at havailGood
      nlinarith
    exact_mod_cast hreal.le
  have hnonempty : z.2.available.Nonempty := by
    rw [← card_pos]
    exact hD.trans_le havailability
  have hupperDev : ∀ P : PairOn V, PairAlive P.1 z.2 →
      fixedPairUpperDeviation (qUpper P) S0 P.1 z.1.1 z.2 -
        fixedPairUpperDeviation (qUpper P) S0 P.1 0 S0 < aPair := by
    intro P halive
    exact lt_of_not_ge fun hbad =>
      hnotPairBad ⟨P, Or.inl ⟨halive, hbad⟩⟩
  have hlowerDev : ∀ P : PairOn V, PairAlive P.1 z.2 →
      fixedPairLowerDeviation (qLower P) S0 P.1 z.1.1 z.2 -
        fixedPairLowerDeviation (qLower P) S0 P.1 0 S0 < aPair := by
    intro P halive
    exact lt_of_not_ge fun hbad =>
      hnotPairBad ⟨P, Or.inr ⟨halive, hbad⟩⟩
  have hpairBand :
      pairBandActiveTwoCutoffs F Kpair Kglobal Delta delta z.1.1 z.2 :=
    pairBandActiveTwoCutoffs_of_deviations_lt qUpper qLower z.1.1
      Kpair Kglobal Delta delta aPair htraj.2 hnonempty hpairTwoGood
      hglobalTwoGood (fun P => hcap P z.1.1 htime)
      (fun P => htargetFloor P z.1.1 htime) hupperDev hlowerDev
  have hztime : z.1.1 = n := by
    rcases hterminal with htimeEq | hinactive
    · exact htimeEq
    · exact (hinactive ⟨⟨hpairBand, htotalGood, havailability⟩,
        hincGood⟩).elim
  exact ⟨z.2, hQ, htraj.1, hpairBand.2.1, hpairBand.2.2.2.2,
    hpairTwoGood, hglobalTwoGood, hincGood, htotalGood, havailability,
    by simpa [hztime] using hcard⟩

end

end Erdos207
