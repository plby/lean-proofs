/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PatternBaseSelectors
import ErdosProblems.Erdos207.PatternSelectorArithmetic
import ErdosProblems.Erdos207.KSSSPowerActive

/-! # Actual surviving-pattern denominators on the coupled trajectory event -/

namespace Erdos207

open Finset

noncomputable section

theorem ksssAvailableTrajectory_eq_clock_pair
    (orders : Finset ℕ) (a : ℕ → ℝ) (E A time : ℝ)
    (hE : E ≠ 0) (hp : ksssEdgeDensity E time ≠ 0) :
    ksssAvailableTrajectory orders a E A time =
      E * ksssEdgeDensity E time * ksssPairTrajectory orders a E A time / 3 := by
  unfold ksssPairTrajectory
  field_simp

theorem KSSSOnTrajectories.pattern_selector_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q : ℕ} {Q₀ : Finset (Finset V)}
    {a : ℕ → ℝ} {E A scale time : ℝ} {B : ℕ}
    (h : KSSSOnTrajectories F S q (ksssResidualPairs Q₀ S) a E A scale B time)
    (hgeometry : KSSSResidualGeometry Q₀ S E time)
    (hE : 0 < E) (hp : 0 < ksssEdgeDensity E time)
    (he : 0 ≤ ksssErrorEnvelope E scale B time)
    (hsmall : ksssErrorEnvelope E scale B time ≤ ksssPairTrajectory (ksssOrders q) a E A time / 4)
    (Q : SimpleGraph V)
    (hsize : (graphEdges Q).card * (Fintype.card V : ℝ) ≤
      E * ksssEdgeDensity E time * ksssErrorEnvelope E scale B time / 3) :
    |((patternSurvivalSelectors Q S).card : ℝ) - ksssAvailableTrajectory (ksssOrders q) a E A time| ≤
        2 * (E * ksssEdgeDensity E time) * ksssErrorEnvelope E scale B time / 3 ∧
      E * ksssEdgeDensity E time * ksssPairTrajectory (ksssOrders q) a E A time / 6 ≤
        ((patternSurvivalSelectors Q S).card : ℝ) := by
  have hglobal := h.availability_error hgeometry.pair_card hgeometry.cover
  rw [hgeometry.count] at hglobal
  have hcount : (S.available.card : ℝ) =
      ((patternSurvivalSelectors Q S).card : ℝ) + (patternBasePairStars Q S).card := by
    exact_mod_cast (patternSurvivalSelectors_card_add_base Q S).symm
  have hexcluded : ((patternBasePairStars Q S).card : ℝ) ≤
      E * ksssEdgeDensity E time * ksssErrorEnvelope E scale B time / 3 := by
    calc
      _ ≤ (graphEdges Q).card * (Fintype.card V : ℝ) := by
        exact_mod_cast card_patternBasePairStars_le_order Q S
      _ ≤ _ := hsize
  rw [ksssAvailableTrajectory_eq_clock_pair _ _ _ _ _ hE.ne' hp.ne']
  exact pattern_selector_denominator_bounds _ _ _ _ _ _ (mul_pos hE hp).le he hcount
    (Nat.cast_nonneg _) hexcluded hglobal hsmall

end

end Erdos207
