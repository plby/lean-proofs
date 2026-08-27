/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPowerActive
import ErdosProblems.Erdos207.AbsorberGreedy
import ErdosProblems.Erdos207.TimedStoppedIndexedInvariant

/-! # Residual-pair geometry is automatic on the actual stopped support -/

namespace Erdos207

open Finset

noncomputable section

theorem ksssResidualGeometry_of_contained
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (ambient : TripleSystemOn V) (Q₀ : Finset (Finset V)) (E : ℝ) (time : ℕ)
    (hS : GreedyInvariant F S) (hcontained : GreedyContainedIn ambient S)
    (hchosen : S.chosen.card = time) (hE : 0 < E) (hEcard : (Q₀.card : ℝ) = E)
    (hQ : ∀ P ∈ Q₀, P.card = 2)
    (hcover : ∀ T ∈ ambient, ∀ P : Finset V, P.card = 2 → P ⊆ T.1 → P ∈ Q₀) :
    KSSSResidualGeometry Q₀ S E time := by
  have hchosenPairs : chosenPairFinsets S ⊆ Q₀ := by
    intro P hP
    obtain ⟨T, hT, hPT, hcard⟩ := mem_chosenPairFinsets_iff.mp hP
    exact hcover T (hcontained.1 hT) P hcard hPT
  have hcount := residualPairSet_card_add_chosen Q₀ hS hchosenPairs
  rw [hchosen] at hcount
  have hreal : ((Q₀ \ chosenPairFinsets S).card : ℝ) + 3 * (time : ℝ) = (Q₀.card : ℝ) := by
    exact_mod_cast hcount
  have hclock : E * ksssEdgeDensity E time = E - 3 * (time : ℝ) := by
    unfold ksssEdgeDensity
    field_simp
  refine ⟨fun P hP ↦ hQ P (mem_sdiff.mp hP).1, ?_, ?_⟩
  · intro P hP hstar
    exact residualPairSet_covers_available Q₀ hS
      (fun T hT Q hQ hQT ↦ hcover T (hcontained.2 hT) Q hQ hQT) hP hstar
  · rw [hclock]
    dsimp only [ksssResidualPairs]
    linarith only [hreal, hEcard]

theorem timedStoppedGreedy_supported_contained_counter
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (havailable : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → S.available.Nonempty) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).SupportedOn
      (fun w ↦ (GreedyInvariant F w.2 ∧ GreedyContainedIn S₀.available w.2) ∧
        w.2.chosen.card = w.1.1) := by
  apply FiniteLaw.timedStoppedProcessLaw_supported_indexed n (fun _ ↦ greedyKernel F) active
    (fun i S ↦ (GreedyInvariant F S ∧ GreedyContainedIn S₀.available S) ∧ S.chosen.card = i) S₀
  · refine ⟨⟨hInv₀, ?_⟩, ?_⟩
    · exact ⟨by rw [hchosen₀]; exact empty_subset _, Subset.rfl⟩
    · rw [hchosen₀, card_empty]
  · intro i hi S hS hactive S' hmass
    obtain ⟨T, hT, rfl⟩ := greedyKernel_supported_step_of_nonempty F S
      (havailable i hi S hS.1.1 hactive) S' hmass
    refine ⟨⟨hS.1.1.step hT, hS.1.2.step hT⟩, ?_⟩
    rw [greedyStep_chosen_card F S T (hS.1.1.2.2 T hT).1, hS.2]

theorem timedStoppedGreedy_supported_residualGeometry
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (Q₀ : Finset (Finset V)) (E : ℝ)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hE : 0 < E) (hEcard : (Q₀.card : ℝ) = E) (hQ : ∀ P ∈ Q₀, P.card = 2)
    (hcover : ∀ T ∈ S₀.available, ∀ P : Finset V, P.card = 2 → P ⊆ T.1 → P ∈ Q₀)
    (havailable : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → S.available.Nonempty) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).SupportedOn
      (fun w ↦ KSSSResidualGeometry Q₀ w.2 E w.1.1) := by
  have hsupport := timedStoppedGreedy_supported_contained_counter n F active S₀ hInv₀ hchosen₀ havailable
  intro w hw
  have hs := hsupport w hw
  exact ksssResidualGeometry_of_contained S₀.available Q₀ E w.1.1 hs.1.1 hs.1.2 hs.2
    hE hEcard hQ hcover

end

end Erdos207
