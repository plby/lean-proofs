/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialNeighborMargins
import ErdosProblems.Erdos207.ProperPatternExtensions
import ErdosProblems.Erdos207.KSSSPatternLowerBound
import ErdosProblems.Erdos207.RelativePatternEnvelope
import ErdosProblems.Erdos207.PatternRelativeCentered

/-! # Initial relative pattern margins from the proved absorber loss bounds -/

namespace Erdos207

open Finset

noncomputable section

theorem properPatternExtensions_loss_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (Q : SimpleGraph V) (U : Finset V) :
    (U \ properPatternExtensions A Q U).card ≤
      (U \ iterationExtensionVertices A Q U).card + (graphSupportFinset Q).card := by
  have hcount := card_sdiff_add_card_eq_card (iterationExtensionVertices_subset A Q U)
  have hcomparison := (properPatternExtensions_card_comparison A Q U).2
  rw [card_sdiff_of_subset (properPatternExtensions_subset A Q U)]
  omega

theorem properPatternExtensions_abs_initial_error_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (Q : SimpleGraph V) (U : Finset V) (D h : ℕ)
    (hD : (U \ iterationExtensionVertices A Q U).card ≤ D)
    (hh : (graphSupportFinset Q).card ≤ h) :
    |((properPatternExtensions A Q U).card : ℝ) - U.card| ≤ (D + h : ℕ) := by
  rw [abs_card_sub_eq_card_sdiff_of_subset _ U (properPatternExtensions_subset A Q U)]
  exact_mod_cast (properPatternExtensions_loss_le A Q U).trans (Nat.add_le_add hD hh)

theorem initial_separated_proper_pattern_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {q h : ℕ} {H : SimpleGraph V} {X U : Finset V} {B : TripleSystemOn V} {Q : SimpleGraph V}
    (hsep : AbsorberSeparatedLevel H X B U) (hroot : HasPaddedAbsorberRootBounds q H X B)
    (hQ : Q ≤ graphDifference (SimpleGraph.completeGraph V) H)
    (hQsupport : (graphSupportFinset Q).card ≤ h) :
    |((properPatternExtensions (absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q B) (outsideAvailableTriangles H B)).available Q U).card : ℝ) - U.card| ≤
      (2 * h + h ^ 2 * 36 : ℕ) := by
  have h := properPatternExtensions_abs_initial_error_le _ Q U (h + h ^ 2 * 36) h
    (card_initial_separated_extension_loss_le hsep hroot hQ hQsupport) hQsupport
  convert h using 1 <;> congr 1 <;> omega

theorem initial_ambient_proper_pattern_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {q h C : ℕ} {H : SimpleGraph V} [DecidableRel H.Adj] {B : TripleSystemOn V} {Q : SimpleGraph V}
    (hdegree : ∀ x, H.degree x ≤ C) (hbankSupport : (verticesOn B).card ≤ C)
    (hQ : Q ≤ graphDifference (SimpleGraph.completeGraph V) H)
    (hQsupport : (graphSupportFinset Q).card ≤ h) :
    |((properPatternExtensions (absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q B) (outsideAvailableTriangles H B)).available Q univ).card : ℝ) - Fintype.card V| ≤
      (2 * h + h ^ 2 * (3 * C) : ℕ) := by
  have hbound := properPatternExtensions_abs_initial_error_le _ Q univ (h + h ^ 2 * (3 * C)) h
    (card_initial_ambient_extension_loss_le (q := q) hdegree hbankSupport hQ hQsupport) hQsupport
  simpa only [card_univ, show h + h ^ 2 * (3 * C) + h = 2 * h + h ^ 2 * (3 * C) by omega] using hbound

theorem ksssPatternTrajectory_zero
    (q : ℕ) (a : ℕ → ℝ) (E M : ℝ) (h m : ℕ) (hE : E ≠ 0) :
    ksssPatternTrajectory (ksssOrders q) a E M h m 0 = M := by
  simp only [ksssPatternTrajectory, ksssEdgeDensity_zero E hE, one_pow,
    ksssPoissonExponent_zero (ksssOrders q) a (fun _ hd ↦ (mem_Icc.mp hd).1),
    mul_zero, Real.exp_zero, mul_one]

theorem properPatternRelativeCount_initial_error
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : SimpleGraph V) (U : Finset V) (S : GreedyStateOn V) (margin : ℝ) (hU : U.Nonempty)
    (herror : |((properPatternExtensions S.available Q U).card : ℝ) - U.card| ≤ U.card * margin) :
    |properPatternRelativeCount Q U U.card S - 1| ≤ margin := by
  have hM : (0 : ℝ) < U.card := by exact_mod_cast card_pos.mpr hU
  have hid : properPatternRelativeCount Q U U.card S - 1 =
      (((properPatternExtensions S.available Q U).card : ℝ) - U.card) / U.card := by
    unfold properPatternRelativeCount
    field_simp
  rw [hid, abs_div, abs_of_pos hM]
  apply (div_le_iff₀ hM).mpr
  simpa only [mul_comm] using herror

theorem initial_relative_pattern_margin
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (a : ℕ → ℝ) (E t : ℝ) (s B : ℕ) (Q : SimpleGraph V) (U : Finset V)
    (S₀ : GreedyStateOn V) (hE : E ≠ 0) (hU : U.Nonempty)
    (herror : |((properPatternExtensions S₀.available Q U).card : ℝ) - U.card| ≤
      U.card * (8 * t ^ 2 / t ^ s)) :
    |properPatternRelativeCount Q U
        (ksssPatternTrajectory (ksssOrders q) a E U.card (graphSupportFinset Q).card (graphEdges Q).card 0) S₀ - 1| +
      8 * t ^ 2 / t ^ s ≤ relativePatternEnvelope E t s B 0 := by
  rw [ksssPatternTrajectory_zero q a E U.card _ _ hE]
  have h := properPatternRelativeCount_initial_error Q U S₀ (8 * t ^ 2 / t ^ s) hU herror
  unfold relativePatternEnvelope
  rw [ksssErrorEnvelope_zero E _ _ hE]
  calc
    _ ≤ 8 * t ^ 2 / t ^ s + 8 * t ^ 2 / t ^ s := add_le_add h le_rfl
    _ = _ := by ring

end

end Erdos207
