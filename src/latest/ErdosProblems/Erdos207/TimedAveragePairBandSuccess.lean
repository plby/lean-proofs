/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TimedAveragePairBand
import Mathlib.Algebra.BigOperators.Fin

/-!
# Positive-probability extraction for the averaged pair-band phase

There are five possible terminal failures on the common stopped law: a pair
trajectory deviation, failure of the pair-local two-away cutoff, failure of
the global two-away cutoff, failure of the aggregate incidence cutoff, or a
global availability deficit.  If their probability bounds sum to less than
one, some trajectory reaches the horizon and retains every invariant.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Abstract final union bound for the common averaged pair-band law. -/
theorem exists_timedAveragePairBand_full_phase_of_failure_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (qUpper qLower : PairOn V → ℕ → ℝ)
    (Kpair Kglobal Δ δ I D : ℕ) (aPair aAvail : ℝ)
    (εpair εpairTwo εglobalTwo εtotal εavail : ℝ)
    (hInv₀ : GreedyInvariant F S₀) (hD : 0 < D)
    {Q : GreedyStateOn V → Prop}
    (hQsupport :
      let active := timedAveragePairBandActive
        F Kpair Kglobal Δ δ I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      L.SupportedOn (fun z ↦ Q z.2))
    (havailabilityBuffer : ∀ i, i ≤ n →
      (D : ℝ) + (i : ℝ) * averageAvailabilityLossRate Δ I D + aAvail ≤
        (S₀.available.card : ℝ))
    (hcap : ∀ P : PairOn V, ∀ i, i ≤ n →
      qUpper P i +
          (fixedPairAvailableCountReal S₀ P.1 S₀ - qUpper P 0) + aPair ≤
        ((Δ + 1 : ℕ) : ℝ))
    (htargetFloor : ∀ P : PairOn V, ∀ i, i ≤ n →
      PairAlive P.1 S₀ →
      (δ : ℝ) ≤ qLower P i +
          (fixedPairAvailableCountReal S₀ P.1 S₀ - qLower P 0) - aPair)
    (hpair :
      let active := timedAveragePairBandActive
        F Kpair Kglobal Δ δ I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      (L.probability (fun z ↦ ∃ P : PairOn V,
        (PairAlive P.1 z.2 ∧
          aPair ≤ fixedPairUpperDeviation (qUpper P) S₀ P.1 z.1.1 z.2 -
            fixedPairUpperDeviation (qUpper P) S₀ P.1 0 S₀) ∨
        (PairAlive P.1 z.2 ∧
          aPair ≤ fixedPairLowerDeviation (qLower P) S₀ P.1 z.1.1 z.2 -
            fixedPairLowerDeviation (qLower P) S₀ P.1 0 S₀)) : ℝ) ≤ εpair)
    (hpairTwo :
      let active := timedAveragePairBandActive
        F Kpair Kglobal Δ δ I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      (L.probability
        (fun z ↦ ¬ HasPairTwoAwayCutoff F Kpair z.2) : ℝ) ≤ εpairTwo)
    (hglobalTwo :
      let active := timedAveragePairBandActive
        F Kpair Kglobal Δ δ I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      (L.probability
        (fun z ↦ ¬ HasTwoAwayCutoff F Kglobal z.2) : ℝ) ≤ εglobalTwo)
    (htotal :
      let active := timedAveragePairBandActive
        F Kpair Kglobal Δ δ I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      (L.probability
        (fun z ↦ I < totalAvailableTwoAwayIncidences F z.2) : ℝ) ≤ εtotal)
    (havail :
      let active := timedAveragePairBandActive
        F Kpair Kglobal Δ δ I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      (L.probability (fun z ↦
        aAvail ≤
          averageAvailabilityDeficit (averageAvailabilityLossRate Δ I D)
              z.1.1 z.2 -
            averageAvailabilityDeficit (averageAvailabilityLossRate Δ I D)
              0 S₀) : ℝ) ≤ εavail)
    (hsmall : εpair + εpairTwo + εglobalTwo + εtotal + εavail < 1) :
    ∃ S : GreedyStateOn V,
      Q S ∧ GreedyInvariant F S ∧
        HasAvailablePairCutoff Δ S ∧
        HasAvailablePairFloor δ S ∧
        HasPairTwoAwayCutoff F Kpair S ∧
        HasTwoAwayCutoff F Kglobal S ∧
        totalAvailableTwoAwayIncidences F S ≤ I ∧
        D ≤ S.available.card ∧
        S.chosen.card = S₀.chosen.card + n := by
  classical
  let active := timedAveragePairBandActive F Kpair Kglobal Δ δ I D
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
  let pairTwoBad : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ ¬ HasPairTwoAwayCutoff F Kpair z.2
  let globalTwoBad : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ ¬ HasTwoAwayCutoff F Kglobal z.2
  let totalBad : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ I < totalAvailableTwoAwayIncidences F z.2
  let availBad : FiniteLaw.TimedState (GreedyStateOn V) n → Prop := fun z ↦
    aAvail ≤
      averageAvailabilityDeficit (averageAvailabilityLossRate Δ I D)
          z.1.1 z.2 -
        averageAvailabilityDeficit (averageAvailabilityLossRate Δ I D)
          0 S₀
  let badAt : Fin 5 → FiniteLaw.TimedState (GreedyStateOn V) n → Prop
    | ⟨0, _⟩ => pairBad
    | ⟨1, _⟩ => pairTwoBad
    | ⟨2, _⟩ => globalTwoBad
    | ⟨3, _⟩ => totalBad
    | ⟨4, _⟩ => availBad
  let ε : Fin 5 → ℝ
    | ⟨0, _⟩ => εpair
    | ⟨1, _⟩ => εpairTwo
    | ⟨2, _⟩ => εglobalTwo
    | ⟨3, _⟩ => εtotal
    | ⟨4, _⟩ => εavail
  have hbadAt : ∀ j : Fin 5, (L.probability (badAt j) : ℝ) ≤ ε j := by
    intro j
    fin_cases j
    · simpa [L, active, badAt, pairBad, ε] using hpair
    · simpa [L, active, badAt, pairTwoBad, ε] using hpairTwo
    · simpa [L, active, badAt, globalTwoBad, ε] using hglobalTwo
    · simpa [L, active, badAt, totalBad, ε] using htotal
    · simpa [L, active, badAt, availBad, ε] using havail
  have hunionNN := L.probability_exists_le
    (univ : Finset (Fin 5)) badAt
  have hunionReal :
      (L.probability (fun z ↦ ∃ j : Fin 5, badAt j z) : ℝ) ≤
        ∑ j : Fin 5, (L.probability (badAt j) : ℝ) := by
    have hraw :
        (L.probability (fun z ↦ ∃ j ∈ (univ : Finset (Fin 5)),
          badAt j z) : ℝ) ≤
            ∑ j : Fin 5, (L.probability (badAt j) : ℝ) := by
      exact_mod_cast hunionNN
    simpa using hraw
  have hfailure :
      (L.probability (fun z ↦ ∃ j : Fin 5, badAt j z) : ℝ) < 1 := by
    calc
      (L.probability (fun z ↦ ∃ j : Fin 5, badAt j z) : ℝ) ≤
          ∑ j : Fin 5, (L.probability (badAt j) : ℝ) := hunionReal
      _ ≤ ∑ j : Fin 5, ε j := by
        apply sum_le_sum
        intro j _hj
        exact hbadAt j
      _ = εpair + εpairTwo + εglobalTwo + εtotal + εavail := by
        simp [ε, Fin.sum_univ_succ]
        ring
      _ < 1 := hsmall
  have hgoodReal :
      0 < (L.probability (fun z ↦ ¬ ∃ j : Fin 5, badAt j z) : ℝ) := by
    rw [L.probability_not]
    rw [NNReal.coe_sub (L.probability_le_one _)]
    norm_num only [NNReal.coe_one]
    exact sub_pos.mpr hfailure
  have hgood : 0 < L.probability (fun z ↦ ¬ ∃ j : Fin 5, badAt j z) := by
    exact_mod_cast hgoodReal
  obtain ⟨z, hzgood, hmass⟩ :=
    L.exists_of_probability_pos_with_mass hgood
  have htraj : PairTrajectoryInvariant F S₀ z.2 :=
    timedAveragePairBandProcessLaw_supported_pairTrajectoryInvariant
      (n := n) (Kpair := Kpair) (Kglobal := Kglobal) (Δ := Δ)
      (δ := δ) (I := I) (D := D) hInv₀ z hmass
  have hcard : z.2.chosen.card = S₀.chosen.card + z.1.1 :=
    timedAveragePairBandProcessLaw_supported_chosen_card
      (n := n) (Kpair := Kpair) (Kglobal := Kglobal) (Δ := Δ)
      (δ := δ) (I := I) (D := D) hInv₀ z hmass
  have hQ : Q z.2 := hQsupport z hmass
  have hterminal := FiniteLaw.timedStoppedProcessLaw_supported_terminal
    n (fun _ ↦ greedyKernel F) active S₀ z hmass
  have hnotPairBad : ¬ pairBad z := by
    intro hbad
    exact hzgood ⟨⟨0, by omega⟩, by simpa [badAt] using hbad⟩
  have hpairTwoGood : HasPairTwoAwayCutoff F Kpair z.2 := by
    by_contra hbad
    exact hzgood ⟨⟨1, by omega⟩, by simpa [badAt, pairTwoBad] using hbad⟩
  have hglobalTwoGood : HasTwoAwayCutoff F Kglobal z.2 := by
    by_contra hbad
    exact hzgood ⟨⟨2, by omega⟩, by simpa [badAt, globalTwoBad] using hbad⟩
  have htotalGood : totalAvailableTwoAwayIncidences F z.2 ≤ I := by
    by_contra hbad
    have hbad' : I < totalAvailableTwoAwayIncidences F z.2 := by omega
    exact hzgood ⟨⟨3, by omega⟩, by simpa [badAt, totalBad] using hbad'⟩
  have havailGood :
      averageAvailabilityDeficit (averageAvailabilityLossRate Δ I D)
          z.1.1 z.2 -
        averageAvailabilityDeficit (averageAvailabilityLossRate Δ I D)
          0 S₀ < aAvail := by
    exact lt_of_not_ge fun hbad ↦
      hzgood ⟨⟨4, by omega⟩, by simpa [badAt, availBad] using hbad⟩
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
      pairBandActiveTwoCutoffs F Kpair Kglobal Δ δ z.1.1 z.2 :=
    pairBandActiveTwoCutoffs_of_deviations_lt qUpper qLower z.1.1
      Kpair Kglobal Δ δ aPair htraj.2 hnonempty hpairTwoGood
      hglobalTwoGood (fun P ↦ hcap P z.1.1 htime)
      (fun P ↦ htargetFloor P z.1.1 htime) hupperDev hlowerDev
  have hztime : z.1.1 = n := by
    rcases hterminal with htimeEq | hinactive
    · exact htimeEq
    · exact (hinactive ⟨hpairBand, htotalGood, havailability⟩).elim
  exact ⟨z.2, hQ, htraj.1, hpairBand.2.1, hpairBand.2.2.2.2,
    hpairTwoGood, hglobalTwoGood, htotalGood, havailability,
    by simpa [hztime] using hcard⟩

end

end Erdos207
