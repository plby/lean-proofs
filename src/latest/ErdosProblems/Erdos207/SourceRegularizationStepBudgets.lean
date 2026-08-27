/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceRegularizationOrderStep
import ErdosProblems.Erdos207.ForbiddenDegreePowerBudget
import ErdosProblems.Erdos207.RegularizationDensityScale
import ErdosProblems.Erdos207.SourceRegularizationHazard

/-! # Uniform scalar budgets for a step after any valid earlier regularized orders -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem sourceRegularization_order_scalar_conditions
    {V I K : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    [Nonempty I] [DecidableEq K] {ell j : ℕ}
    (W : Vortex V ell) (e : I ↪ TripleOn V)
    (hsupport : ∀ i, (e i).1 ⊆ W.U (Fin.last ell)) (hj : 4 ≤ j)
    (hterminal : 0 < W.terminalSize) (hm : 2 * (j - 3) ≤ Fintype.card I)
    (L : Finset (Finset I)) (orders : Finset K) (earlier : K → Finset (Finset I))
    (size : K → ℕ) (horders : orders.card ≤ W.terminalSize)
    (hsize : ∀ i ∈ orders, 2 ≤ size i ∧ size i ≤ j - 2)
    (huniform : ∀ i ∈ orders, ∀ E ∈ earlier i, E.card = size i)
    (hearlier : ∀ i ∈ orders, finiteHypergraphMaxDegree (earlier i) ≤ W.terminalSize ^ (size i - 1))
    (hLpower : finiteHypergraphMaxDegree L ≤ W.terminalSize ^ (j - 3))
    (sigma C B delta : ℝ≥0) (hsigma : 0 < sigma) (hC : 0 < C)
    (hmass : sigma * (W.terminalSize : ℝ≥0) ^ 3 / C ≤ Fintype.card I)
    (hdegree : (finiteHypergraphMaxDegree L : ℝ≥0) ≤
      B * sigma ^ (j - 3) * (W.terminalSize : ℝ≥0) ^ (j - 3))
    (hdensity : 324 * (2 : ℝ≥0) ^ (j - 2) * (2 * C) ^ (j - 3) * (j - 3).factorial ≤
      sigma ^ (j - 3) * W.terminalSize)
    (hcoefficient : (2 : ℝ≥0) ^ (j - 1) * (2 * C) ^ (j - 3) * (j - 3).factorial * B ≤ delta)
    (b s : ℕ)
    (hsmall : finiteHypergraphMaxDegree L * (2 * Fintype.card I * Real.exp (-(b : ℝ) / 8192)) +
      (sourceRandomFailureCoefficient W j : ℝ) * ((2 : ℝ) ^ s)⁻¹ < 1) :
    let G := trimForbiddenSupersets L (orders.biUnion earlier)
    let H := regularizationForbiddenFamily e (j - 2) G (orders.biUnion earlier)
    ((2 : ℝ≥0) ^ (j - 2) * finiteHypergraphMaxDegree H ≤
      (1 / 36 : ℝ≥0) * Nat.choose (Fintype.card I) (j - 2 - 1)) ∧
    (2 * regularizationBaseHazard G (j - 2) ≤ sourceRandomConfigurationProbability W.terminalSize delta j) ∧
    (finiteHypergraphDegreeGap G * (2 * Fintype.card I * Real.exp (-(b : ℝ) / 8192)) +
      (sourceRandomFailureCoefficient W j : ℝ) * ((2 : ℝ) ^ s)⁻¹ < 1) := by
  dsimp only
  let G := trimForbiddenSupersets L (orders.biUnion earlier)
  have hGL : finiteHypergraphMaxDegree G ≤ finiteHypergraphMaxDegree L :=
    finiteHypergraphMaxDegree_mono (trimForbiddenSupersets_subset L (orders.biUnion earlier))
  have he : j - 2 - 1 = j - 3 := by omega
  have hH := regularizationForbiddenFamily_max_degree_le_nine_power e (W.U (Fin.last ell))
    hsupport hterminal (j - 2) (by omega) G orders earlier size horders hsize huniform hearlier
    (by simpa only [he, Vortex.terminalSize] using hGL.trans hLpower)
  have hn : (0 : ℝ≥0) < W.terminalSize := by exact_mod_cast hterminal
  refine ⟨?_, ?_, ?_⟩
  · apply regularization_density_of_power_bound (Fintype.card I) (j - 2) (by omega)
      (by simpa only [he] using hm) W.terminalSize sigma C
      (finiteHypergraphMaxDegree (regularizationForbiddenFamily e (j - 2) G (orders.biUnion earlier)))
      hn hsigma hC hmass
    · exact_mod_cast hH
    · simpa only [he] using hdensity
  · apply regularization_source_probability_le G j hj hm W.terminalSize sigma C B delta
      hn hsigma hC hmass _ hcoefficient
    exact (show (finiteHypergraphMaxDegree G : ℝ≥0) ≤ finiteHypergraphMaxDegree L by exact_mod_cast hGL).trans hdegree
  · have hgap : (finiteHypergraphDegreeGap G : ℝ) ≤ finiteHypergraphMaxDegree L := by
      exact_mod_cast (Nat.sub_le (finiteHypergraphMaxDegree G) (finiteHypergraphMinDegree G)).trans hGL
    have hfactor : 0 ≤ (2 : ℝ) * Fintype.card I * Real.exp (-(b : ℝ) / 8192) := by positivity
    have hbound : (finiteHypergraphDegreeGap G : ℝ) *
        (2 * Fintype.card I * Real.exp (-(b : ℝ) / 8192)) +
        (sourceRandomFailureCoefficient W j : ℝ) * ((2 : ℝ) ^ s)⁻¹ ≤
        finiteHypergraphMaxDegree L * (2 * Fintype.card I * Real.exp (-(b : ℝ) / 8192)) +
        (sourceRandomFailureCoefficient W j : ℝ) * ((2 : ℝ) ^ s)⁻¹ :=
      add_le_add (mul_le_mul_of_nonneg_right hgap hfactor) le_rfl
    exact hbound.trans_lt hsmall

end

end Erdos207
