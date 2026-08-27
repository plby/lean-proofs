/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedTwoAwayRelativePowerTail
import ErdosProblems.Erdos207.PatternLocalizedJump
import ErdosProblems.Erdos207.AbsorberPadding

/-! # Simultaneous localized cutoffs for a fixed family of vortex levels -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

abbrev LocalizedTwoAwayIndex (I V : Type*) [DecidableEq V] := I × (TripleOn V × (V × V))

def AllLocalizedTwoAwayBounds
    {I V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (sets : I → Finset V) (cutoff : I → ℝ≥0) (S : GreedyStateOn V) : Prop :=
  ∀ i T a b, a ≠ b → selectedCount
    (fun u : LocalizedTwoAwayWitness V F T a b (sets i) ↦ localizedTwoAwayRemainder u) S.chosen < cutoff i

theorem card_localizedTwoAwayIndex_le
    (I V : Type*) [Fintype I] [Fintype V] [DecidableEq V] :
    Fintype.card (LocalizedTwoAwayIndex I V) ≤ Fintype.card I * Fintype.card V ^ 5 := by
  simp only [LocalizedTwoAwayIndex, Fintype.card_prod]
  calc
    _ ≤ Fintype.card I * (Fintype.card V ^ 3 * (Fintype.card V * Fintype.card V)) := by
      gcongr
      exact card_tripleOn_le_cube V
    _ = _ := by ring

theorem timedStoppedAbsorber_allLocalizedTwoAway_relative_power_tail
    {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (q t r v : ℕ)
    (H : SimpleGraph V) (B : TripleSystemOn V) (X : Finset V) (sets : I → Finset V) (w : ℝ≥0)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (hsep : ∀ i, AbsorberSeparatedLevel H X B (sets i))
    (hrootLocal : HasPaddedAbsorberRootLocalization q X B)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hD : 0 < D) (hw : 1 ≤ w) (ht : 1 ≤ t) (hU : ∀ i, (sets i).Nonempty)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hwscale : w ≤ (t : ℝ≥0) ^ v)
    (hsize : ∀ i, (45 * (q + 1) + 28 : ℕ) * (t : ℝ≥0) ^ (r + q * (v + 1) + 1) ≤ ((sets i).card : ℝ≥0))
    (hbank : pairExactBankExtensionCoefficient q B * (t : ℝ≥0) ^ (r + q * (v + 1) + 1) ≤
      (Fintype.card V + 1 : ℝ≥0))
    (hconst : (4 * (q + 1) ^ (q + 2) : ℕ) ≤ t) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ ¬ AllLocalizedTwoAwayBounds F sets
        (fun i ↦ ((sets i).card : ℝ≥0) / (t : ℝ≥0) ^ r) z.2) ≤
      (Fintype.card I : ℝ≥0) * (Fintype.card V : ℝ≥0) ^ 5 * (1 / 2 : ℝ≥0) ^ t := by
  classical
  let law := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀
  let event := fun i : LocalizedTwoAwayIndex I V ↦ fun z : FiniteLaw.TimedState (GreedyStateOn V) n ↦
    i.2.2.1 ≠ i.2.2.2 ∧ ((sets i.1).card : ℝ≥0) / (t : ℝ≥0) ^ r ≤ selectedCount
      (fun u : LocalizedTwoAwayWitness V F i.2.1 i.2.2.1 i.2.2.2 (sets i.1) ↦ localizedTwoAwayRemainder u) z.2.chosen
  have hpoint : ∀ i : LocalizedTwoAwayIndex I V, law.probability (event i) ≤ (1 / 2 : ℝ≥0) ^ t := by
    intro i
    by_cases hab : i.2.2.1 = i.2.2.2
    · simp only [event, hab, ne_eq, not_true_eq_false, false_and, FiniteLaw.probability_false]
      exact bot_le
    · have h := timedStoppedAbsorber_localizedTwoAway_relative_power_tail n F active D S₀ q t r v
        H B X (sets i.1) i.2.1 hab w hF (hsep i.1) hrootLocal hInv₀ hchosen₀ hD hw ht
        (hU i.1) hfloor hratio hwscale (hsize i.1) hbank hconst
      simpa only [event, ne_eq, hab, not_false_eq_true, true_and] using h
  have heq : (fun z : FiniteLaw.TimedState (GreedyStateOn V) n ↦
      ¬ AllLocalizedTwoAwayBounds F sets (fun i ↦ ((sets i).card : ℝ≥0) / (t : ℝ≥0) ^ r) z.2) =
      (fun z ↦ ∃ i : LocalizedTwoAwayIndex I V, event i z) := by
    funext z
    simp only [AllLocalizedTwoAwayBounds, not_forall, not_lt, event, Prod.exists, exists_prop]
  rw [heq]
  calc
    _ ≤ ∑ i : LocalizedTwoAwayIndex I V, law.probability (event i) := by
      simpa only [mem_univ, true_and] using law.probability_exists_le (univ : Finset (LocalizedTwoAwayIndex I V)) event
    _ ≤ ∑ _i : LocalizedTwoAwayIndex I V, (1 / 2 : ℝ≥0) ^ t := sum_le_sum fun i _ ↦ hpoint i
    _ = (Fintype.card (LocalizedTwoAwayIndex I V) : ℝ≥0) * (1 / 2 : ℝ≥0) ^ t := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast card_localizedTwoAwayIndex_le I V) (by positivity)

theorem AllLocalizedTwoAwayBounds.pattern_loss_bound
    {I V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {sets : I → Finset V} {cutoff : I → ℝ≥0} {S : GreedyStateOn V}
    (h : AllLocalizedTwoAwayBounds F sets cutoff S) (hS : GreedyInvariant F S)
    (i : I) (Q : SimpleGraph V) (T : TripleOn V) (hT : T ∈ patternSurvivalSelectors Q S) :
    ((patternExtensionLoss F Q (sets i) S T).card : ℝ≥0) ≤ 3 + (graphEdges Q).card * cutoff i := by
  exact patternExtensionLoss_card_le_localized_cutoff hS Q (sets i) T hT (cutoff i)
    (fun e ↦ (h i T e.1.out.1 e.1.out.2 (out_fst_ne_snd_of_mem_graphEdges e.2)).le)

theorem localized_pattern_loss_relative_scale
    (M t m : ℝ) (r : ℕ) (ht : 0 < t) (hsize : t ^ (r + 2) ≤ M)
    (hm : 0 ≤ m) (hcoeff : 3 + m ≤ t ^ 2) :
    3 + m * (M / t ^ (r + 2)) ≤ M / t ^ r := by
  have hM : 0 < M := (pow_pos ht _).trans_le hsize
  have hK : 1 ≤ M / t ^ (r + 2) := (le_div_iff₀ (pow_pos ht _)).mpr (by simpa only [one_mul] using hsize)
  calc
    _ ≤ (3 + m) * (M / t ^ (r + 2)) := by nlinarith only [hK]
    _ ≤ t ^ 2 * (M / t ^ (r + 2)) := mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = _ := by rw [pow_add]; field_simp

end

end Erdos207
