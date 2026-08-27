/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveCliqueExtensionLoss
import ErdosProblems.Erdos207.ReserveSpokeConcentration

/-! # Actual reserve-law tails for proper clique-extension loss -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem reserveEdgeLaw_probability_clique_spoke_bad
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (A : TripleSystemOn V) (S : Finset V)
    (r : ℝ≥0) (hr : r ≤ 1) :
    let X := properPatternExtensions A (cliquePattern S) univ
    ((reserveEdgeLaw G U r hr).probability (fun omega ↦ ∃ w ∈ S,
      2 * (r : ℝ) * X.card ≤
        ((reserveCliqueSpokeVertices A S (reserveEdges G U omega) w).card : ℝ)) : ℝ) ≤
      S.card * Real.exp (-(r : ℝ) * X.card / 4) := by
  classical
  dsimp only
  let X := properPatternExtensions A (cliquePattern S) univ
  let L := reserveEdgeLaw G U r hr
  have hunion : (L.probability (fun omega ↦ ∃ w ∈ S,
      2 * (r : ℝ) * X.card ≤
        ((reserveCliqueSpokeVertices A S (reserveEdges G U omega) w).card : ℝ)) : ℝ) ≤
      ∑ w ∈ S, (L.probability (fun omega ↦
        2 * (r : ℝ) * X.card ≤
          ((reserveCliqueSpokeVertices A S (reserveEdges G U omega) w).card : ℝ)) : ℝ) := by
    exact_mod_cast L.probability_exists_le S (fun w omega ↦
      2 * (r : ℝ) * X.card ≤
        ((reserveCliqueSpokeVertices A S (reserveEdges G U omega) w).card : ℝ))
  apply hunion.trans
  calc
    _ ≤ ∑ _w ∈ S, Real.exp (-(r : ℝ) * X.card / 4) :=
      sum_le_sum (fun w _ ↦ reserveEdgeLaw_probability_spoke_count_ge G U X w r hr)
    _ = _ := by simp only [sum_const, nsmul_eq_mul, X]

theorem reserveEdgeLaw_probability_clique_extension_loss
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (A : TripleSystemOn V) (S : Finset V)
    (r : ℝ≥0) (hr : r ≤ 1) (hS : 2 ≤ S.card)
    (hA : ∀ T ∈ A, tripleEdgeFinset T ⊆ graphEdges G) :
    let X := properPatternExtensions A (cliquePattern S) univ
    ((reserveEdgeLaw G U r hr).probability (fun omega ↦
      cliquePattern S ≤ reserveProtectedOuterGraph G U (reserveEdges G U omega) ∧
      ((properPatternExtensions (reserveProtectedOuterAvailable G U (reserveEdges G U omega) A)
        (cliquePattern S) univ).card : ℝ) + U.card + 2 * S.card * (r : ℝ) * X.card < X.card) : ℝ) ≤
      S.card * Real.exp (-(r : ℝ) * X.card / 4) := by
  classical
  dsimp only
  let X := properPatternExtensions A (cliquePattern S) univ
  let L := reserveEdgeLaw G U r hr
  have hcover : L.probability (fun omega ↦
      cliquePattern S ≤ reserveProtectedOuterGraph G U (reserveEdges G U omega) ∧
      ((properPatternExtensions (reserveProtectedOuterAvailable G U (reserveEdges G U omega) A)
        (cliquePattern S) univ).card : ℝ) + U.card + 2 * S.card * (r : ℝ) * X.card < X.card) ≤
      L.probability (fun omega ↦ ∃ w ∈ S, 2 * (r : ℝ) * X.card ≤
        ((reserveCliqueSpokeVertices A S (reserveEdges G U omega) w).card : ℝ)) := by
    apply L.probability_mono
    intro omega homega
    by_contra hnot
    push Not at hnot
    have hdet := (properCliqueExtension_reserve_card_bounds G U (reserveEdges G U omega) A S
      hS homega.1 hA).2
    have hdetR : (X.card : ℝ) ≤
        (properPatternExtensions (reserveProtectedOuterAvailable G U (reserveEdges G U omega) A)
          (cliquePattern S) univ).card + (U.card : ℝ) +
          ∑ w ∈ S, ((reserveCliqueSpokeVertices A S (reserveEdges G U omega) w).card : ℝ) := by
      exact_mod_cast hdet
    have hsum : (∑ w ∈ S, ((reserveCliqueSpokeVertices A S (reserveEdges G U omega) w).card : ℝ)) ≤
        S.card * (2 * (r : ℝ) * X.card) := by
      simpa only [sum_const, nsmul_eq_mul] using sum_le_sum (fun w hw ↦ (hnot w hw).le)
    nlinarith [homega.2]
  have hcoverR := show (L.probability (fun omega ↦
      cliquePattern S ≤ reserveProtectedOuterGraph G U (reserveEdges G U omega) ∧
      ((properPatternExtensions (reserveProtectedOuterAvailable G U (reserveEdges G U omega) A)
        (cliquePattern S) univ).card : ℝ) + U.card + 2 * S.card * (r : ℝ) * X.card < X.card) : ℝ) ≤
      L.probability (fun omega ↦ ∃ w ∈ S, 2 * (r : ℝ) * X.card ≤
        ((reserveCliqueSpokeVertices A S (reserveEdges G U omega) w).card : ℝ)) from by exact_mod_cast hcover
  exact hcoverR.trans (reserveEdgeLaw_probability_clique_spoke_bad G U A S r hr)

end

end Erdos207
