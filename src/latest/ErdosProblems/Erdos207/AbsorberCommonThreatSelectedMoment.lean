/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberNontrivialFamily
import ErdosProblems.Erdos207.GreedyCommonThreatMoment

/-! # Selected common-threat witness moments for the actual forbidden family -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem absorberForbiddenCommonThreat_selected_moment_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (A : Ω → TripleSystemOn V)
    (q s : ℕ) (B : TripleSystemOn V) (F : ForbiddenFamilyOn V) (T T' : TripleOn V) (C : ℝ≥0)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (hjoint : ∀ U : TripleSystemOn V, U.card ≤ s * (2 * q) →
      L.probability (fun ω ↦ U ⊆ A ω) ≤ C * ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ U.card) :
    L.expectation (fun ω ↦
      (selectedCount (fun w : CommonThreatWitness F F T T' ↦ w.remainder) (A ω)) ^ s) ≤
      absorberCommonThreatMomentUpper q s B C := by
  apply configurationMomentBound L (fun w : CommonThreatWitness F F T T' ↦ w.remainder) A
    (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) C (absorberCommonThreatWeightBound q B)
    (absorberForbiddenCommonThreat_remainder_card_le q B F T T' hF)
    (absorberForbiddenCommonThreat_hasExtensionBound q B F T T' hF)
  intro U hU
  simpa only [setWeight, prod_const] using hjoint U hU

theorem timedStoppedAbsorber_commonThreatSelectedMomentBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (B : TripleSystemOn V)
    (q s : ℕ) (T T' : TripleOn V) (w : ℝ≥0)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (hchosen₀ : S₀.chosen = ∅) (hD : 0 < D) (hw : 1 ≤ w)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).expectation
      (fun z ↦ (selectedCount (fun u : CommonThreatWitness F F T T' ↦ u.remainder) z.2.chosen) ^ s) ≤
      absorberCommonThreatMomentUpper q s B (w ^ (s * (2 * q))) := by
  refine absorberForbiddenCommonThreat_selected_moment_le
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀)
    (fun z : FiniteLaw.TimedState (GreedyStateOn V) n ↦ z.2.chosen)
    q s B F T T' (w ^ (s * (2 * q))) hF ?_
  intro U hU
  exact timedStoppedGreedyProcess_probability_subset_le_scaled_weight n F active D (s * (2 * q))
    (Fintype.card V + 1 : ℝ≥0)⁻¹ w hD hw hfloor hratio S₀ U (by simp [hchosen₀]) hU

theorem timedStoppedAbsorber_commonThreatSelectedTailBound
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (B : TripleSystemOn V)
    (q s : ℕ) (T T' : TripleOn V) (w K : ℝ≥0)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (hchosen₀ : S₀.chosen = ∅) (hD : 0 < D) (hw : 1 ≤ w) (hK : 0 < K)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ K ≤ selectedCount (fun u : CommonThreatWitness F F T T' ↦ u.remainder) z.2.chosen) ≤
      absorberCommonThreatMomentUpper q s B (w ^ (s * (2 * q))) / K ^ s := by
  let L := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀
  let X : FiniteLaw.TimedState (GreedyStateOn V) n → ℝ≥0 := fun z ↦
    (selectedCount (fun u : CommonThreatWitness F F T T' ↦ u.remainder) z.2.chosen) ^ s
  have hpos : 0 < K ^ s := pow_pos hK s
  have hmono : L.probability (fun z ↦ K ≤
      selectedCount (fun u : CommonThreatWitness F F T T' ↦ u.remainder) z.2.chosen) ≤
      L.probability (fun z ↦ K ^ s ≤ X z) :=
    L.probability_mono (fun _ hz ↦ pow_le_pow_left' hz s)
  refine hmono.trans ((L.probability_le_expectation_div X hpos).trans ?_)
  apply (div_le_div_iff_of_pos_right hpos).mpr
  exact timedStoppedAbsorber_commonThreatSelectedMomentBound n F active D S₀ B q s T T' w
    hF hchosen₀ hD hw hfloor hratio

end

end Erdos207
