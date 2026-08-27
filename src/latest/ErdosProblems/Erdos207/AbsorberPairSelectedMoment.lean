/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberPairSelectedWeight
import ErdosProblems.Erdos207.TimedStoppedSharpJointInclusion

/-! # Selected pair-local witness moments and stopped-process tails -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def absorberPairSelectedMomentUpper
    {V : Type*} [Fintype V] [DecidableEq V]
    (q s : ℕ) (B : TripleSystemOn V) (C : ℝ≥0) : ℝ≥0 :=
  C * ((2 : ℝ≥0) ^ (s * q) * (pairTwoAwayThreatExtensionCoefficient q B : ℕ)) ^ s

theorem absorberForbiddenPairThreat_selected_moment_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (A : Ω → TripleSystemOn V)
    (q s : ℕ) (B : TripleSystemOn V) (F : ForbiddenFamilyOn V) (T : TripleOn V) (P : PairOn V) (C : ℝ≥0)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (hjoint : ∀ U : TripleSystemOn V, U.card ≤ s * q →
      L.probability (fun ω ↦ U ⊆ A ω) ≤ C * ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ U.card) :
    L.expectation (fun ω ↦ (selectedCount
      (fun w : PairTwoAwayThreatWitness V F T P ↦ pairTwoAwayThreatRemainder w) (A ω)) ^ s) ≤
      absorberPairSelectedMomentUpper q s B C := by
  apply configurationMomentBound L
    (fun w : PairTwoAwayThreatWitness V F T P ↦ pairTwoAwayThreatRemainder w) A
    (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) C (pairTwoAwayThreatExtensionCoefficient q B : ℕ)
    (absorberForbiddenPairThreat_remainder_card_le q B F T P hF)
    (absorberForbiddenPairThreat_hasExtensionBound q B F T P hF)
  intro U hU
  simpa only [setWeight, prod_const] using hjoint U hU

theorem timedStoppedAbsorber_pairSelectedMomentBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (B : TripleSystemOn V)
    (q s : ℕ) (T : TripleOn V) (P : PairOn V) (w : ℝ≥0)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (hchosen₀ : S₀.chosen = ∅) (hD : 0 < D) (hw : 1 ≤ w)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).expectation
      (fun z ↦ (selectedCount (fun u : PairTwoAwayThreatWitness V F T P ↦
        pairTwoAwayThreatRemainder u) z.2.chosen) ^ s) ≤
      absorberPairSelectedMomentUpper q s B (w ^ (s * q)) := by
  refine absorberForbiddenPairThreat_selected_moment_le
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀)
    (fun z : FiniteLaw.TimedState (GreedyStateOn V) n ↦ z.2.chosen)
    q s B F T P (w ^ (s * q)) hF ?_
  intro U hU
  exact timedStoppedGreedyProcess_probability_subset_le_scaled_weight n F active D (s * q)
    (Fintype.card V + 1 : ℝ≥0)⁻¹ w hD hw hfloor hratio S₀ U (by simp [hchosen₀]) hU

theorem timedStoppedAbsorber_pairSelectedTailBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (B : TripleSystemOn V)
    (q s : ℕ) (T : TripleOn V) (P : PairOn V) (w K : ℝ≥0)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (hchosen₀ : S₀.chosen = ∅) (hD : 0 < D) (hw : 1 ≤ w) (hK : 0 < K)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ K ≤ selectedCount (fun u : PairTwoAwayThreatWitness V F T P ↦
        pairTwoAwayThreatRemainder u) z.2.chosen) ≤
      absorberPairSelectedMomentUpper q s B (w ^ (s * q)) / K ^ s := by
  let L := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀
  let X : FiniteLaw.TimedState (GreedyStateOn V) n → ℝ≥0 := fun z ↦
    (selectedCount (fun u : PairTwoAwayThreatWitness V F T P ↦ pairTwoAwayThreatRemainder u) z.2.chosen) ^ s
  have hpos : 0 < K ^ s := pow_pos hK s
  have hmono : L.probability (fun z ↦ K ≤ selectedCount
      (fun u : PairTwoAwayThreatWitness V F T P ↦ pairTwoAwayThreatRemainder u) z.2.chosen) ≤
      L.probability (fun z ↦ K ^ s ≤ X z) :=
    L.probability_mono (fun _ hz ↦ pow_le_pow_left' hz s)
  refine hmono.trans ((L.probability_le_expectation_div X hpos).trans ?_)
  apply (div_le_div_iff_of_pos_right hpos).mpr
  exact timedStoppedAbsorber_pairSelectedMomentBound n F active D S₀ B q s T P w
    hF hchosen₀ hD hw hfloor hratio

end

end Erdos207
