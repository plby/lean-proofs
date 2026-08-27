/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveCliqueUniformConcentration
import ErdosProblems.Erdos207.ReserveCliqueErrorTransfer

/-! # Every surviving clique satisfies the regularizer's input estimates -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem reserveProtected_clique_regularization_inputs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U D : Finset V) (A : TripleSystemOn V)
    (p tau xi r : ℝ≥0) (omega : Sym2 V → Bool)
    (hG : GraphSupportedOn G (D : Set V)) (hp1 : p ≤ 1) (htau1 : tau ≤ 1)
    (hxi : xi ≤ 1 / 1536) (hr : r ≤ 1 / 24576)
    (hdensity : 6144 ≤ p ^ 4 * tau ^ 6 * D.card)
    (hinner : (U.card : ℝ≥0) ≤ p ^ 4 * tau ^ 6 * D.card / 1536)
    (hold : ∀ S ∈ smallCliqueFamily G D,
      |((properPatternExtensions A (cliquePattern S) univ).card : ℝ) -
        (p : ℝ) ^ S.card * (tau : ℝ) ^ (S.card.choose 2) * D.card| ≤
      (xi : ℝ) * ((p : ℝ) ^ S.card * (tau : ℝ) ^ (S.card.choose 2) * D.card) + S.card)
    (hgood : ∀ S ∈ smallCliqueFamily G D, ¬ ReserveCliqueExtensionLossEvent G U A S r omega) :
    ∀ S : Finset V, 2 ≤ S.card → S.card ≤ 4 →
      cliquePattern S ≤ reserveProtectedOuterGraph G U (reserveEdges G U omega) →
      let f := (p : ℝ) ^ S.card * (tau : ℝ) ^ (S.card.choose 2) * D.card
      let y : ℝ := (properPatternExtensions
        (reserveProtectedOuterAvailable G U (reserveEdges G U omega) A) (cliquePattern S) univ).card
      |f - y| ≤ f / (12 * (2 : ℝ) ^ 5) ∧ f / 2 ≤ y ∧ y ≤ 2 * f := by
  intro S hS2 hS4 hSG
  let X := properPatternExtensions A (cliquePattern S) univ
  let Y := properPatternExtensions (reserveProtectedOuterAvailable G U (reserveEdges G U omega) A)
    (cliquePattern S) univ
  let f := (p : ℝ) ^ S.card * (tau : ℝ) ^ (S.card.choose 2) * D.card
  have hSGold := hSG.trans (reserveProtectedOuterGraph_le G U (reserveEdges G U omega))
  have hSindex : S ∈ smallCliqueFamily G D := (mem_smallCliqueFamily_iff G D S).mpr
    ⟨cliquePattern_subset_supported_graph G S D hS2 hSGold hG, hS2, hS4, hSGold⟩
  have hmin : (p : ℝ) ^ 4 * (tau : ℝ) ^ 6 * D.card ≤ f :=
    small_clique_target_lower p tau D.card S.card p.coe_nonneg (by exact_mod_cast hp1)
      tau.coe_nonneg (by exact_mod_cast htau1) (by positivity) hS4
  have hdensityR : (6144 : ℝ) ≤ (p : ℝ) ^ 4 * (tau : ℝ) ^ 6 * D.card := by exact_mod_cast hdensity
  have hinnerR : (U.card : ℝ) ≤ (p : ℝ) ^ 4 * (tau : ℝ) ^ 6 * D.card / 1536 := by
    exact_mod_cast hinner
  have hmono : (Y.card : ℝ) ≤ X.card := by
    exact_mod_cast card_le_card (properPatternExtensions_mono_available
      (reserveProtectedOuterAvailable_subset G U (reserveEdges G U omega) A) (cliquePattern S) univ)
  have hloss : (X.card : ℝ) ≤ Y.card + (U.card : ℝ) + 2 * S.card * (r : ℝ) * X.card := by
    apply le_of_not_gt
    intro hbad
    exact hgood S hSindex ⟨hSG, hbad⟩
  exact reserve_clique_regularization_margins X.card Y.card f xi r U.card S.card
    (by positivity) (hdensityR.trans hmin) (by exact_mod_cast hxi) hS4
    (by linarith) r.coe_nonneg (by exact_mod_cast hr) (hold S hSindex) hmono hloss

end

end Erdos207
