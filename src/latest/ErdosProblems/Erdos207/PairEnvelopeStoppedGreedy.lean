/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AvailablePairDegreeTrajectory
import ErdosProblems.Erdos207.EnvelopeStoppedGreedy

/-!
# Greedy stopping with a decaying available-pair codegree

This is the trajectory kernel used by cover-down.  At time `i` it checks the
two-away cutoff, the scheduled maximum available pair-codegree `Δ i`, and the
global availability floor `D i`.  The refined deletion envelope is then
`3 Δ(i) + K`.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

def pairEnvelopeStoppedGreedyKernel
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (K : ℕ) (Δ D : ℕ → ℕ)
    (i : ℕ) (S : GreedyStateOn V) : FiniteLaw (GreedyStateOn V) := by
  classical
  exact if HasTwoAwayCutoff F K S ∧ HasAvailablePairCutoff (Δ i) S ∧
      D i ≤ S.available.card then
    greedyKernel F S
  else
    FiniteLaw.pure S

def pairEnvelopeStoppedGreedyProcessLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (K : ℕ) (Δ D : ℕ → ℕ)
    (fuel : ℕ) (S : GreedyStateOn V) : FiniteLaw (GreedyStateOn V) :=
  FiniteLaw.evolveKernels (pairEnvelopeStoppedGreedyKernel F K Δ D) fuel
    (FiniteLaw.pure S)

/-- Pair-codegree schedule obtained from the deterministic packing envelope
at the selected-edge count expected at time `i`. -/
def packingPairEnvelopeSchedule
    (V : Type*) [Fintype V] (initialCard i : ℕ) : ℕ :=
  packingPairEnvelope V (initialCard + i)

theorem packingPairEnvelopeSchedule_antitone
    (V : Type*) [Fintype V] (initialCard i : ℕ) :
    packingPairEnvelopeSchedule V initialCard (i + 1) ≤
      packingPairEnvelopeSchedule V initialCard i := by
  unfold packingPairEnvelopeSchedule packingPairEnvelope
  omega

theorem pairEnvelopeStoppedGreedyKernel_monotone_singleInsertion
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (K : ℕ) (Δ D : ℕ → ℕ) (i : ℕ) :
    IsMonotoneSingleInsertionKernel
      (pairEnvelopeStoppedGreedyKernel F K Δ D i)
      (fun S : GreedyStateOn V ↦ S.chosen) := by
  classical
  intro S
  unfold pairEnvelopeStoppedGreedyKernel
  split_ifs with hactive
  · exact greedyKernel_monotone_singleInsertion F S
  · exact FiniteLaw.supportedOn_pure _ ⟨Subset.rfl, by simp⟩

theorem pairEnvelopeStoppedGreedyKernel_probability_new_triangle_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (K : ℕ) (Δ D : ℕ → ℕ)
    (i : ℕ) (hD : 0 < D i) (S : GreedyStateOn V) (T : TripleOn V)
    (hTnot : T ∉ S.chosen) :
    (pairEnvelopeStoppedGreedyKernel F K Δ D i S).probability
        (fun S' ↦ T ∈ S'.chosen) ≤ (D i : ℝ≥0)⁻¹ := by
  classical
  unfold pairEnvelopeStoppedGreedyKernel
  split_ifs with hactive
  · exact greedyKernel_probability_new_triangle_le
      F S T (D i) hD hactive.2.2 hTnot
  · rw [FiniteLaw.probability_pure]
    simp [hTnot]

theorem pairEnvelopeStoppedGreedyProcess_probability_subset_chosen_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (K : ℕ) (Δ D : ℕ → ℕ)
    (hD : ∀ i, 0 < D i) (fuel : ℕ) (S : GreedyStateOn V)
    (U : TripleSystemOn V) (hdisjoint : Disjoint U S.chosen) :
    (pairEnvelopeStoppedGreedyProcessLaw F K Δ D fuel S).probability
        (fun S' ↦ U ⊆ S'.chosen) ≤
      (U.card.factorial : ℝ≥0) *
        ((∑ i ∈ range fuel, (D i : ℝ≥0)⁻¹) ^ U.card) := by
  exact evolveKernels_probability_subset_le
    (pairEnvelopeStoppedGreedyKernel F K Δ D)
    (fun S : GreedyStateOn V ↦ S.chosen)
    (fun i ↦ (D i : ℝ≥0)⁻¹)
    (pairEnvelopeStoppedGreedyKernel_monotone_singleInsertion F K Δ D)
    (fun i S T hT ↦
      pairEnvelopeStoppedGreedyKernel_probability_new_triangle_le
        F K Δ D i (hD i) S T hT)
    S U hdisjoint fuel

theorem pairEnvelopeStoppedGreedyProcess_probability_subset_chosen_le_weight
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (K : ℕ) (Δ D : ℕ → ℕ)
    (hD : ∀ i, 0 < D i) (fuel m : ℕ) (p : ℝ≥0)
    (hratio : (∑ i ∈ range fuel, (D i : ℝ≥0)⁻¹) ≤ p)
    (S : GreedyStateOn V) (U : TripleSystemOn V)
    (hdisjoint : Disjoint U S.chosen) (hcard : U.card ≤ m) :
    (pairEnvelopeStoppedGreedyProcessLaw F K Δ D fuel S).probability
        (fun S' ↦ U ⊆ S'.chosen) ≤
      (m.factorial : ℝ≥0) * setWeight (constantTripleWeight p) U := by
  rw [setWeight_constantTripleWeight]
  calc
    (pairEnvelopeStoppedGreedyProcessLaw F K Δ D fuel S).probability
        (fun S' ↦ U ⊆ S'.chosen) ≤
      (U.card.factorial : ℝ≥0) *
        ((∑ i ∈ range fuel, (D i : ℝ≥0)⁻¹) ^ U.card) :=
      pairEnvelopeStoppedGreedyProcess_probability_subset_chosen_le
        F K Δ D hD fuel S U hdisjoint
    _ ≤ (m.factorial : ℝ≥0) * p ^ U.card := by
      apply mul_le_mul
      · exact_mod_cast Nat.factorial_le hcard
      · exact pow_le_pow_left' hratio U.card
      · exact bot_le
      · exact bot_le

/-- Full support/progress invariant for the refined stopped kernel. -/
theorem pairEnvelopeStoppedAbsorberGreedyProcessLaw_supported_progress
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V}
    {K : ℕ} {Δ D : ℕ → ℕ} {S₀ : GreedyStateOn V}
    (hInv : AbsorberGreedyInvariant F A S₀)
    (hfloor : D 0 ≤ S₀.available.card) (hD : ∀ i, 0 < D i)
    (hΔmono : ∀ i, Δ (i + 1) ≤ Δ i)
    (hdecrease : ∀ i, D (i + 1) + (3 * Δ i + K) ≤ D i) :
    ∀ fuel,
      FiniteLaw.SupportedOn
        (fun S ↦ AbsorberGreedyInvariant F A S ∧
          D fuel ≤ S.available.card ∧
          (¬ HasTwoAwayCutoff F K S ∨
            ¬ HasAvailablePairCutoff (Δ fuel) S ∨
            S.chosen.card = S₀.chosen.card + fuel))
        (pairEnvelopeStoppedGreedyProcessLaw F K Δ D fuel S₀) := by
  intro fuel
  induction fuel with
  | zero =>
      exact FiniteLaw.supportedOn_pure _
        ⟨hInv, hfloor, Or.inr (Or.inr (by omega))⟩
  | succ fuel ih =>
      change FiniteLaw.SupportedOn _
        (FiniteLaw.bind
          (pairEnvelopeStoppedGreedyProcessLaw F K Δ D fuel S₀)
          (pairEnvelopeStoppedGreedyKernel F K Δ D fuel))
      refine ih.bind (pairEnvelopeStoppedGreedyKernel F K Δ D fuel) ?_
      intro S hS
      have hdec := hdecrease fuel
      have hnext_le : D (fuel + 1) ≤ D fuel := by omega
      unfold pairEnvelopeStoppedGreedyKernel
      split_ifs with hactive
      · have hnonempty : S.available.Nonempty := by
          rw [← card_pos]
          exact (hD fuel).trans_le hS.2.1
        have hsteps := greedyKernel_supported_step_of_nonempty F S hnonempty
        intro S' hmass
        obtain ⟨T, hT, rfl⟩ := hsteps S' hmass
        have hTnot : T ∉ S.chosen := (hS.1.1.2.2 T hT).1
        have hcardS : S.chosen.card = S₀.chosen.card + fuel := by
          rcases hS.2.2 with hbad | hbad | hcard
          · exact (hbad hactive.1).elim
          · exact (hbad hactive.2.1).elim
          · exact hcard
        have hstepfloor := greedyStep_available_card_le_add_pairEnvelope
          hS.1.1 hactive.2.1 hactive.1 hT
        refine ⟨hS.1.step hT, ?_, Or.inr (Or.inr ?_)⟩
        · omega
        · rw [greedyStep_chosen_card F S T hTnot, hcardS]
          omega
      · have hbad : ¬ HasTwoAwayCutoff F K S ∨
            ¬ HasAvailablePairCutoff (Δ fuel) S := by
          by_cases htwo : HasTwoAwayCutoff F K S
          · exact Or.inr fun hpair ↦ hactive ⟨htwo, hpair, hS.2.1⟩
          · exact Or.inl htwo
        exact FiniteLaw.supportedOn_pure _
          ⟨hS.1, hnext_le.trans hS.2.1, hbad.elim Or.inl
            (fun hp ↦ Or.inr (Or.inl fun hpairNext ↦ hp
              (fun P hP ↦ (hpairNext P hP).trans (hΔmono fuel))))⟩

/-- With the packing-derived pair schedule, pair-codegree failure can never
be the first stopping reason.  Hence every supported trajectory either has
already violated the two-away cutoff or has made exactly one insertion per
elapsed step. -/
theorem packingPairEnvelopeStoppedAbsorberGreedyProcessLaw_supported_progress
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V}
    {K : ℕ} {D : ℕ → ℕ} {S₀ : GreedyStateOn V}
    (hInv : AbsorberGreedyInvariant F A S₀)
    (hfloor : D 0 ≤ S₀.available.card) (hD : ∀ i, 0 < D i)
    (hdecrease : ∀ i,
      D (i + 1) +
          (3 * packingPairEnvelopeSchedule V S₀.chosen.card i + K) ≤
        D i) :
    ∀ fuel,
      FiniteLaw.SupportedOn
        (fun S ↦ AbsorberGreedyInvariant F A S ∧
          D fuel ≤ S.available.card ∧
          (¬ HasTwoAwayCutoff F K S ∨
            S.chosen.card = S₀.chosen.card + fuel))
        (pairEnvelopeStoppedGreedyProcessLaw F K
          (packingPairEnvelopeSchedule V S₀.chosen.card) D fuel S₀) := by
  intro fuel
  induction fuel with
  | zero =>
      exact FiniteLaw.supportedOn_pure _
        ⟨hInv, hfloor, Or.inr (by omega)⟩
  | succ fuel ih =>
      change FiniteLaw.SupportedOn _
        (FiniteLaw.bind
          (pairEnvelopeStoppedGreedyProcessLaw F K
            (packingPairEnvelopeSchedule V S₀.chosen.card) D fuel S₀)
          (pairEnvelopeStoppedGreedyKernel F K
            (packingPairEnvelopeSchedule V S₀.chosen.card) D fuel))
      refine ih.bind
        (pairEnvelopeStoppedGreedyKernel F K
          (packingPairEnvelopeSchedule V S₀.chosen.card) D fuel) ?_
      intro S hS
      have hdec := hdecrease fuel
      have hnext_le : D (fuel + 1) ≤ D fuel := by omega
      by_cases htwo : HasTwoAwayCutoff F K S
      · have hcardS : S.chosen.card = S₀.chosen.card + fuel :=
          hS.2.2.resolve_left (not_not_intro htwo)
        have hpair : HasAvailablePairCutoff
            (packingPairEnvelopeSchedule V S₀.chosen.card fuel) S := by
          have hp := hasAvailablePairCutoff_packingPairEnvelope hS.1.1
          simpa [packingPairEnvelopeSchedule, hcardS] using hp
        have hactive : HasTwoAwayCutoff F K S ∧
            HasAvailablePairCutoff
              (packingPairEnvelopeSchedule V S₀.chosen.card fuel) S ∧
            D fuel ≤ S.available.card := ⟨htwo, hpair, hS.2.1⟩
        unfold pairEnvelopeStoppedGreedyKernel
        rw [if_pos hactive]
        have hnonempty : S.available.Nonempty := by
          rw [← card_pos]
          exact (hD fuel).trans_le hS.2.1
        have hsteps := greedyKernel_supported_step_of_nonempty F S hnonempty
        intro S' hmass
        obtain ⟨T, hT, rfl⟩ := hsteps S' hmass
        have hTnot : T ∉ S.chosen := (hS.1.1.2.2 T hT).1
        have hstepfloor := greedyStep_available_card_le_add_pairEnvelope
          hS.1.1 hpair htwo hT
        refine ⟨hS.1.step hT, ?_, Or.inr ?_⟩
        · omega
        · rw [greedyStep_chosen_card F S T hTnot, hcardS]
          omega
      · have hactiveNot : ¬(HasTwoAwayCutoff F K S ∧
            HasAvailablePairCutoff
              (packingPairEnvelopeSchedule V S₀.chosen.card fuel) S ∧
            D fuel ≤ S.available.card) := fun h ↦ htwo h.1
        unfold pairEnvelopeStoppedGreedyKernel
        rw [if_neg hactiveNot]
        exact FiniteLaw.supportedOn_pure _
          ⟨hS.1, hnext_le.trans hS.2.1, Or.inl htwo⟩

end

end Erdos207
