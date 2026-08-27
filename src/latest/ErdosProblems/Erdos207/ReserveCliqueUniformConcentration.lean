/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveCliqueConcentration
import ErdosProblems.Erdos207.SmallCliqueFamily

/-! # Simultaneous reserve-loss control before selecting the surviving clique patterns -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def ReserveCliqueExtensionLossEvent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (A : TripleSystemOn V) (S : Finset V)
    (r : ℝ≥0) (omega : Sym2 V → Bool) : Prop :=
  let X := properPatternExtensions A (cliquePattern S) univ
  cliquePattern S ≤ reserveProtectedOuterGraph G U (reserveEdges G U omega) ∧
    ((properPatternExtensions (reserveProtectedOuterAvailable G U (reserveEdges G U omega) A)
      (cliquePattern S) univ).card : ℝ) + U.card + 2 * S.card * (r : ℝ) * X.card < X.card

theorem reserveEdgeLaw_probability_any_clique_extension_loss
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U D : Finset V) (A : TripleSystemOn V)
    (r : ℝ≥0) (hr : r ≤ 1) (a : ℝ)
    (hA : ∀ T ∈ A, tripleEdgeFinset T ⊆ graphEdges G)
    (hmin : ∀ S ∈ smallCliqueFamily G D,
      a ≤ ((properPatternExtensions A (cliquePattern S) univ).card : ℝ)) :
    ((reserveEdgeLaw G U r hr).probability (fun omega ↦ ∃ S ∈ smallCliqueFamily G D,
      ReserveCliqueExtensionLossEvent G U A S r omega) : ℝ) ≤
      12 * (D.card + 1 : ℝ) ^ 4 * Real.exp (-(r : ℝ) * a / 4) := by
  classical
  let L := reserveEdgeLaw G U r hr
  have hpoint (S : Finset V) (hS : S ∈ smallCliqueFamily G D) :
      (L.probability (ReserveCliqueExtensionLossEvent G U A S r) : ℝ) ≤
        4 * Real.exp (-(r : ℝ) * a / 4) := by
    have hm := (mem_smallCliqueFamily_iff G D S).mp hS
    apply (reserveEdgeLaw_probability_clique_extension_loss G U A S r hr hm.2.1 hA).trans
    have hScard : (S.card : ℝ) ≤ 4 := by exact_mod_cast hm.2.2.1
    apply mul_le_mul hScard _ (Real.exp_pos _).le (by norm_num)
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left (hmin S hS) r.coe_nonneg
    linarith
  have hunion : (L.probability (fun omega ↦ ∃ S ∈ smallCliqueFamily G D,
      ReserveCliqueExtensionLossEvent G U A S r omega) : ℝ) ≤
      ∑ S ∈ smallCliqueFamily G D, (L.probability (ReserveCliqueExtensionLossEvent G U A S r) : ℝ) := by
    exact_mod_cast L.probability_exists_le (smallCliqueFamily G D)
      (fun S omega ↦ ReserveCliqueExtensionLossEvent G U A S r omega)
  have hcard : ((smallCliqueFamily G D).card : ℝ) ≤ 3 * (D.card + 1 : ℝ) ^ 4 := by
    exact_mod_cast smallCliqueFamily_card_le G D
  apply hunion.trans
  calc
    _ ≤ ∑ _S ∈ smallCliqueFamily G D, 4 * Real.exp (-(r : ℝ) * a / 4) := sum_le_sum hpoint
    _ = ((smallCliqueFamily G D).card : ℝ) * (4 * Real.exp (-(r : ℝ) * a / 4)) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ (3 * (D.card + 1 : ℝ) ^ 4) * (4 * Real.exp (-(r : ℝ) * a / 4)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

end

end Erdos207
