/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TimedActiveGreedyJointLaw
import ErdosProblems.Erdos207.TimedAggregateAveragePairBandSuccess
import ErdosProblems.Erdos207.PreliminaryOutsideSupply
import ErdosProblems.Erdos207.PreliminarySurvivalScalar
import ErdosProblems.Erdos207.PreliminaryAugmentedReserveLaw

/-!
# The aggregate pair-band process satisfies the preliminary joint law

The common stopped law used for availability and pair-star concentration
also satisfies equation (8.7).  Outside-pair survival supplies all uncovered
crossing edges, the pair floor gives at least `3k` choices through each of
them, and the exact Bernoulli calculation gives the survival factor.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Equation (8.7), now for the same aggregate pair-band law used by all
stopping-time concentration estimates. -/
theorem timedAggregateAveragePairBand_probability_selected_preliminaryResidual_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (H G : SimpleGraph V) (X : Finset V)
    (Kpair Kglobal Kinc Delta delta I D M k : ℕ)
    (hD : 0 < D) (hkM : k ≤ M) (h3k : 3 * k ≤ delta)
    (alpha eta epsilon : ℝ≥0) (S₀ : GreedyStateOn V)
    (hInv₀ : GreedyInvariant F S₀)
    (houtside₀ : OutsideLeavePairsAlive H X S₀)
    (hHG : Disjoint H G)
    (hsmall : 3 + Kpair < delta)
    (hchosen₀ : S₀.chosen = ∅)
    (hactive₀ : timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D 0 S₀)
    (hupper : ∀ j S,
      timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D j S →
      S.available.card ≤ M)
    (hselected : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : ∀ Q : TripleSystemOn V,
      ((((M - k : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹) ^
        (n - Q.card)) ≤ eta)
    (hinactive :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta I D) S₀).probability
        (fun z ↦ ¬ timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta I D z.1.1 z.2) ≤ epsilon)
    (Q : TripleSystemOn V) (E : Finset (Sym2 V)) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
      (timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D) S₀).probability
        (fun z ↦ Q ⊆ z.2.chosen ∧
          E ⊆ preliminaryResidualCrossingEdges G X z.2.chosen) ≤
      alpha ^ Q.card * eta ^ E.card + epsilon := by
  classical
  let active := timedAggregateAveragePairBandActive
    F Kpair Kglobal Kinc Delta delta I D
  let Inv : GreedyStateOn V → Prop := fun S ↦
    GreedyInvariant F S ∧ OutsideLeavePairsAlive H X S
  let theta : ℝ≥0 :=
    ((M - k : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  have hInvStep : ∀ j, j < n → ∀ S, Inv S → active j S →
      (greedyKernel F S).SupportedOn Inv := by
    intro j _hj S hS hact
    have hout := greedyKernel_supported_outsideLeavePairsAlive_of_pairCutoff
      hS.2 hS.1 hact.1.1.2.2.1 hact.1.1.2.2.2.2 hsmall
    intro S' hmass
    exact ⟨greedyKernel_supported hS.1 S' hmass, hout S' hmass⟩
  have hfloorD : ∀ j S, active j S → D ≤ S.available.card := by
    intro j S hact
    exact hact.1.2.2
  have hsupply : ∀ j S, Inv S → active j S →
      ∀ e ∈ greedyUncoveredEdges (crossingEdges G X) S,
        3 * k ≤ (greedyChoicesCoveringEdge S e).card := by
    intro j S hS hact e he
    have hpre := hasPreliminaryEdgeSupply_of_outsideLeavePairsAlive
      hHG hS.2 hact.1.1.2.2.2.2
    exact h3k.trans (hpre e he)
  have hscalar : ∀ j S B, Inv S → active j S →
      B ⊆ greedyUncoveredEdges (crossingEdges G X) S →
      ((S.available.card - B.card * (3 * k) / 3 : ℕ) : ℝ≥0) *
          (S.available.card : ℝ≥0)⁻¹ ≤ theta ^ B.card := by
    intro j S B _hS hact _hB
    have hA : 0 < S.available.card :=
      card_pos.mpr hact.1.1.1
    exact preliminary_survival_scalar S.available.card M k B.card
      hA (hupper j S hact) hkM
  by_cases hE : E ⊆ crossingEdges G X
  · have hQ : Disjoint Q S₀.chosen := by
      rw [hchosen₀]
      simp
    have hB : E ⊆ greedyUncoveredEdges (crossingEdges G X) S₀ := by
      rw [greedyUncoveredEdges_eq_self_of_chosen_eq_empty
        (crossingEdges G X) S₀ hchosen₀]
      exact hE
    have htracked : L.probability (fun z ↦
        Q ⊆ z.2.chosen ∧
          E ⊆ timedActiveTrackedUncoveredEdges active
            (crossingEdges G X) z) ≤
        alpha ^ Q.card * eta ^ E.card := by
      exact timedStoppedGreedyProcess_probability_selectedTrackedUncovered_le_product
        n F active (crossingEdges G X) Inv D (3 * k) hD theta alpha eta S₀
          ⟨hInv₀, houtside₀⟩ hactive₀ hInvStep hfloorD hsupply hscalar
          hselected Q E hQ hB (hsurvived Q)
    calc
      L.probability (fun z ↦ Q ⊆ z.2.chosen ∧
          E ⊆ preliminaryResidualCrossingEdges G X z.2.chosen) ≤
          L.probability (fun z ↦
            (Q ⊆ z.2.chosen ∧
              E ⊆ timedActiveTrackedUncoveredEdges active
                (crossingEdges G X) z) ∨
            ¬ active z.1.1 z.2) := by
        apply L.probability_mono
        intro z hz
        by_cases hact : active z.1.1 z.2
        · left
          exact ⟨hz.1, by
            simpa only [timedActiveTrackedUncoveredEdges, if_pos hact,
              greedyUncoveredCrossingEdges_eq_preliminaryResidual] using hz.2⟩
        · exact Or.inr hact
      _ ≤ L.probability (fun z ↦
            Q ⊆ z.2.chosen ∧
              E ⊆ timedActiveTrackedUncoveredEdges active
                (crossingEdges G X) z) +
          L.probability (fun z ↦ ¬ active z.1.1 z.2) :=
        L.probability_or_le _ _
      _ ≤ alpha ^ Q.card * eta ^ E.card + epsilon :=
        add_le_add htracked (by simpa [L, active] using hinactive)
  · calc
      L.probability (fun z ↦ Q ⊆ z.2.chosen ∧
          E ⊆ preliminaryResidualCrossingEdges G X z.2.chosen) ≤
          L.probability (fun _ ↦ False) := by
        apply L.probability_mono
        intro z hz
        exact hE (hz.2.trans
          (preliminaryResidualCrossingEdges_subset_crossingEdges
            G X z.2.chosen))
      _ = 0 := L.probability_false
      _ ≤ alpha ^ Q.card * eta ^ E.card + epsilon := bot_le

/-- Equation (8.7) with the exceptional term expressed as the six concrete
failure probabilities controlled by the aggregate differential-equation
argument. -/
theorem timedAggregateAveragePairBand_probability_selected_preliminaryResidual_le_of_failureBounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (H G : SimpleGraph V) (X : Finset V)
    (qUpper qLower : PairOn V → ℕ → ℝ)
    (Kpair Kglobal Kinc Delta delta I D M k : ℕ)
    (aPair aAvail : ℝ)
    (hD : 0 < D) (hkM : k ≤ M) (h3k : 3 * k ≤ delta)
    (alpha eta epair epairTwo eglobalTwo einc etotal eavail : ℝ≥0)
    (S₀ : GreedyStateOn V)
    (hInv₀ : GreedyInvariant F S₀)
    (houtside₀ : OutsideLeavePairsAlive H X S₀)
    (hHG : Disjoint H G)
    (hsmall : 3 + Kpair < delta)
    (hchosen₀ : S₀.chosen = ∅)
    (hactive₀ : timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D 0 S₀)
    (hupper : ∀ j S,
      timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D j S →
      S.available.card ≤ M)
    (havailabilityBuffer : ∀ i, i ≤ n →
      (D : ℝ) + (i : ℝ) * averageAvailabilityLossRate Delta I D + aAvail ≤
        (S₀.available.card : ℝ))
    (hcap : ∀ P : PairOn V, ∀ i, i ≤ n →
      qUpper P i +
          (fixedPairAvailableCountReal S₀ P.1 S₀ - qUpper P 0) + aPair ≤
        ((Delta + 1 : ℕ) : ℝ))
    (htargetFloor : ∀ P : PairOn V, ∀ i, i ≤ n →
      PairAlive P.1 S₀ →
      (delta : ℝ) ≤ qLower P i +
          (fixedPairAvailableCountReal S₀ P.1 S₀ - qLower P 0) - aPair)
    (hselected : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : ∀ Q : TripleSystemOn V,
      ((((M - k : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹) ^
        (n - Q.card)) ≤ eta)
    (hpair :
      let active := timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D
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
      let active := timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      L.probability (fun z ↦ ¬ HasPairTwoAwayCutoff F Kpair z.2) ≤ epairTwo)
    (hglobalTwo :
      let active := timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      L.probability (fun z ↦ ¬ HasTwoAwayCutoff F Kglobal z.2) ≤ eglobalTwo)
    (hinc :
      let active := timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      L.probability
        (fun z ↦ ¬ HasPairStarTwoAwayIncidenceCutoff F Kinc z.2) ≤ einc)
    (htotal :
      let active := timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      L.probability
        (fun z ↦ I < totalAvailableTwoAwayIncidences F z.2) ≤ etotal)
    (havail :
      let active := timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      L.probability (fun z ↦
        aAvail ≤ averageAvailabilityDeficit
            (averageAvailabilityLossRate Delta I D) z.1.1 z.2 -
          averageAvailabilityDeficit
            (averageAvailabilityLossRate Delta I D) 0 S₀) ≤ eavail)
    (Q : TripleSystemOn V) (E : Finset (Sym2 V)) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
      (timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D) S₀).probability
        (fun z ↦ Q ⊆ z.2.chosen ∧
          E ⊆ preliminaryResidualCrossingEdges G X z.2.chosen) ≤
      alpha ^ Q.card * eta ^ E.card +
        (epair + epairTwo + eglobalTwo + einc + etotal + eavail) := by
  have hinactive :=
    probability_timedAggregateAveragePairBand_not_active_le_sum
      n F S₀ qUpper qLower Kpair Kglobal Kinc Delta delta I D aPair aAvail
      epair epairTwo eglobalTwo einc etotal eavail hInv₀ hD
      havailabilityBuffer hcap htargetFloor hpair hpairTwo hglobalTwo hinc
      htotal havail
  exact timedAggregateAveragePairBand_probability_selected_preliminaryResidual_le
    n F H G X Kpair Kglobal Kinc Delta delta I D M k hD hkM h3k
      alpha eta (epair + epairTwo + eglobalTwo + einc + etotal + eavail) S₀
      hInv₀ houtside₀ hHG hsmall hchosen₀ hactive₀ hupper hselected
      hsurvived hinactive Q E

end

end Erdos207
