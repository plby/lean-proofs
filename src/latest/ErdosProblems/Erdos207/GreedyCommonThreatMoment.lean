/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberCommonThreatFamily
import ErdosProblems.Erdos207.GreedyCommonThreatPairs
import ErdosProblems.Erdos207.TimedStoppedSharpJointInclusion

/-! # Moments and tails of the actual third crude statistic -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def absorberCommonThreatMomentUpper
    {V : Type*} [Fintype V] [DecidableEq V]
    (q s : ℕ) (B : TripleSystemOn V) (C : ℝ≥0) : ℝ≥0 :=
  C * ((2 : ℝ≥0) ^ (s * (2 * q)) * absorberCommonThreatWeightBound q B) ^ s

theorem greedyCommonThreatPairs_absorber_moment_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (S : Ω → GreedyStateOn V)
    (q s : ℕ) (B : TripleSystemOn V) (T T' : TripleOn V) (C : ℝ≥0)
    (hjoint : ∀ U : TripleSystemOn V, U.card ≤ s * (2 * q) →
      L.probability (fun ω ↦ U ⊆ (S ω).chosen) ≤
        C * ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ U.card) :
    L.expectation (fun ω ↦ ((greedyCommonThreatPairs
      (absorberNontrivialInducedFamily q B) (absorberNontrivialInducedFamily q B)
      (S ω) T T').card : ℝ≥0) ^ s) ≤ absorberCommonThreatMomentUpper q s B C := by
  let J := absorberNontrivialInducedFamily q B
  let rem := fun w : CommonThreatWitness J J T T' ↦ w.remainder
  have hdom : L.expectation (fun ω ↦ ((greedyCommonThreatPairs J J (S ω) T T').card : ℝ≥0) ^ s) ≤
      L.expectation (fun ω ↦ (selectedCount rem (S ω).chosen) ^ s) := by
    apply L.expectation_mono
    intro ω
    exact pow_le_pow_left' (greedyCommonThreatPairs_card_le_selectedCount J J (S ω) T T') s
  refine hdom.trans (configurationMomentBound L rem (fun ω ↦ (S ω).chosen)
    (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) C (absorberCommonThreatWeightBound q B)
    (absorberCommonThreat_remainder_card_le q B T T')
    (absorberCommonThreat_hasExtensionBound q B T T') ?_)
  intro U hU
  simpa only [setWeight, prod_const] using hjoint U hU

theorem timedStoppedAbsorber_commonThreatMomentBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (B : TripleSystemOn V)
    (q s : ℕ) (T T' : TripleOn V) (w : ℝ≥0)
    (hchosen₀ : S₀.chosen = ∅) (hD : 0 < D) (hw : 1 ≤ w)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).expectation
      (fun z ↦ ((greedyCommonThreatPairs
        (absorberNontrivialInducedFamily q B) (absorberNontrivialInducedFamily q B)
        z.2 T T').card : ℝ≥0) ^ s) ≤
      absorberCommonThreatMomentUpper q s B (w ^ (s * (2 * q))) := by
  refine greedyCommonThreatPairs_absorber_moment_le
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀)
    (fun z : FiniteLaw.TimedState (GreedyStateOn V) n ↦ z.2)
    q s B T T' (w ^ (s * (2 * q))) ?_
  intro U hU
  exact timedStoppedGreedyProcess_probability_subset_le_scaled_weight n F active D (s * (2 * q))
    (Fintype.card V + 1 : ℝ≥0)⁻¹ w hD hw hfloor hratio S₀ U
    (by simp [hchosen₀]) hU

theorem timedStoppedAbsorber_commonThreatTailBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (B : TripleSystemOn V)
    (q s K : ℕ) (T T' : TripleOn V) (w : ℝ≥0)
    (hchosen₀ : S₀.chosen = ∅) (hD : 0 < D) (hw : 1 ≤ w)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ K < (greedyCommonThreatPairs
        (absorberNontrivialInducedFamily q B) (absorberNontrivialInducedFamily q B)
        z.2 T T').card) ≤
      absorberCommonThreatMomentUpper q s B (w ^ (s * (2 * q))) /
        ((K + 1 : ℕ) : ℝ≥0) ^ s := by
  let L := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀
  let J := absorberNontrivialInducedFamily q B
  let X : FiniteLaw.TimedState (GreedyStateOn V) n → ℝ≥0 := fun z ↦
    ((greedyCommonThreatPairs J J z.2 T T').card : ℝ≥0) ^ s
  have hpos : (0 : ℝ≥0) < ((K + 1 : ℕ) : ℝ≥0) ^ s := by positivity
  have hmono : L.probability (fun z ↦ K < (greedyCommonThreatPairs J J z.2 T T').card) ≤
      L.probability (fun z ↦ ((K + 1 : ℕ) : ℝ≥0) ^ s ≤ X z) := by
    apply L.probability_mono
    intro z hz
    apply pow_le_pow_left'
    exact_mod_cast (show K + 1 ≤ (greedyCommonThreatPairs J J z.2 T T').card by omega)
  refine hmono.trans ((L.probability_le_expectation_div X hpos).trans ?_)
  apply (div_le_div_iff_of_pos_right hpos).mpr
  exact timedStoppedAbsorber_commonThreatMomentBound n F active D S₀ B q s T T' w
    hchosen₀ hD hw hfloor hratio

end

end Erdos207
