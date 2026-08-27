/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SimultaneousReserveWedgeLaw
import ErdosProblems.Erdos207.IterationLinkRealWindows
import ErdosProblems.Erdos207.ReserveProtectedPreliminaryGeometry
import ErdosProblems.Erdos207.BoundedPatternIndex

/-! # Quantitative internal supply under the original reserve law -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem IsIterationTypical.reserveEdgeLaw_internalSupplies_failure_le
    {V J : Type*} [Fintype V] [DecidableEq V] [DecidableEq J]
    {ell : ℕ} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {G : SimpleGraph V} {A : TripleSystemOn V} {p eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta xi h)
    (htri : ConsistsOfTriangles G A) (hxi : (xi : ℝ) ≤ 1 / 2)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (E : Finset J) (u v : J → V)
    (huv : ∀ j ∈ E, u j ≠ v j)
    (huOuter : ∀ j ∈ E, u j ∈ W.U i.castSucc)
    (hvOuter : ∀ j ∈ E, v j ∈ W.U i.castSucc)
    (huInner : ∀ j ∈ E, u j ∉ W.U i.succ)
    (hvInner : ∀ j ∈ E, v j ∉ W.U i.succ)
    (huvG : ∀ j ∈ E, G.Adj (u j) (v j))
    (hh : 2 ≤ h) (r : ℝ≥0) (hr : r ≤ 1) (a : J → ℕ)
    (ha : ∀ j ∈ E, (a j : ℝ) ≤ (r : ℝ) ^ 2 * (p : ℝ) ^ 2 * eta * (W.U i.succ).card / 8) :
    let S : J → Finset V := fun j ↦
      iterationExtensionVertices A (SimpleGraph.edge (u j) (v j)) (W.U i.succ)
    ((reserveEdgeLaw G (W.U i.succ) r hr).probability
      (fun bits ↦ ¬ AllReserveWedgeSupplies G (W.U i.succ) E u v S a bits) : ℝ) ≤
      (E.card : ℝ) * Real.exp (-(r : ℝ) ^ 2 * (p : ℝ) ^ 2 * eta * (W.U i.succ).card / 8) := by
  dsimp only
  let S : J → Finset V := fun j ↦
    iterationExtensionVertices A (SimpleGraph.edge (u j) (v j)) (W.U i.succ)
  have hxi1 : xi ≤ 1 := by exact_mod_cast (show (xi : ℝ) ≤ 1 by linarith only [hxi])
  have hS : ∀ j ∈ E, (p : ℝ) ^ 2 * eta * (W.U i.succ).card / 2 ≤ ((S j).card : ℝ) := by
    intro j hj
    have hw := (htyp.edge_extension_window i hstage (huv j hj)
      (huOuter j hj) (hvOuter j hj) (huvG j hj) hh).real_window hxi1
    have hw' : (1 - (xi : ℝ)) * ((p : ℝ) ^ 2 * eta * (W.U i.succ).card) ≤ ((S j).card : ℝ) := by
      exact_mod_cast hw.1
    have hc := mul_le_mul_of_nonneg_right hxi
      (show 0 ≤ (p : ℝ) ^ 2 * eta * (W.U i.succ).card by positivity)
    nlinarith only [hw', hc]
  have hscale : ∀ j ∈ E,
      (r : ℝ) ^ 2 * (p : ℝ) ^ 2 * eta * (W.U i.succ).card / 8 ≤
        ((r ^ 2 : ℝ≥0) : ℝ) * (S j).card / 4 := by
    intro j hj
    have hb := mul_le_mul_of_nonneg_left (hS j hj) (sq_nonneg (r : ℝ))
    simp only [NNReal.coe_pow]
    nlinarith only [hb]
  have hSU : ∀ j ∈ E, S j ⊆ W.U i.succ := fun j _ ↦
    iterationExtensionVertices_subset A (SimpleGraph.edge (u j) (v j)) (W.U i.succ)
  have hadj : ∀ j ∈ E, ∀ w ∈ S j, G.Adj (u j) w ∧ G.Adj (v j) w := by
    intro j hj w hw
    have hwU := hSU j hj hw
    apply iterationExtensionVertices_edge_adjacencies (huv j hj)
    · intro heq
      subst w
      exact huInner j hj hwU
    · intro heq
      subst w
      exact hvInner j hj hwU
    · exact htri
    · exact hw
  calc
    _ ≤ ∑ j ∈ E, Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * (S j).card) / 4) :=
      reserveEdgeLaw_probability_not_allReserveWedgeSupplies_le
        G (W.U i.succ) E u v S a r hr huv huInner hvInner hSU hadj
        (fun j hj ↦ (ha j hj).trans (hscale j hj))
    _ ≤ ∑ _j ∈ E, Real.exp (-(r : ℝ) ^ 2 * (p : ℝ) ^ 2 * eta * (W.U i.succ).card / 8) := by
      apply sum_le_sum
      intro j hj
      apply Real.exp_le_exp.mpr
      linarith only [hscale j hj]
    _ = _ := by simp

def InternalReserveSupplyGood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : TripleSystemOn V) (U : Finset V)
    (a : ℕ) (bits : Sym2 V → Bool) : Prop :=
  AllReserveWedgeSupplies G U (internalOuterEdges G U)
    (fun e ↦ e.out.1) (fun e ↦ e.out.2)
    (fun e ↦ iterationExtensionVertices A (SimpleGraph.edge e.out.1 e.out.2) U)
    (fun _ ↦ a) bits

theorem IsIterationTypical.internalReserveSupply_failure_probability_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {stage : Fin (ell + 1)}
    {G : SimpleGraph V} {A : TripleSystemOn V} {p eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta xi h)
    (htri : ConsistsOfTriangles G A) (hxi : (xi : ℝ) ≤ 1 / 2)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hh : 2 ≤ h) (r : ℝ≥0) (hr : r ≤ 1) (a : ℕ)
    (ha : (a : ℝ) ≤ (r : ℝ) ^ 2 * (p : ℝ) ^ 2 * eta * (W.U i.succ).card / 8) :
    ((reserveEdgeLaw G (W.U i.succ) r hr).probability
      (fun bits ↦ ¬ InternalReserveSupplyGood G A (W.U i.succ) a bits) : ℝ) ≤
      (Fintype.card V : ℝ) ^ 2 * Real.exp (-(r : ℝ) ^ 2 * (p : ℝ) ^ 2 * eta * (W.U i.succ).card / 8) := by
  have hadj : ∀ e ∈ internalOuterEdges G (W.U i.succ), G.Adj e.out.1 e.out.2 :=
    fun _ he ↦ graph_adj_out_of_mem_graphEdges (mem_internalOuterEdges_iff.mp he).1
  have hb := htyp.reserveEdgeLaw_internalSupplies_failure_le htri hxi i hstage
    (internalOuterEdges G (W.U i.succ)) (fun e ↦ e.out.1) (fun e ↦ e.out.2)
    (fun e he ↦ (hadj e he).ne)
    (fun e he ↦ (hGsupp (hadj e he)).1) (fun e he ↦ (hGsupp (hadj e he)).2)
    (fun _ he ↦ (mem_internalOuterEdges_iff.mp he).2.1)
    (fun _ he ↦ (mem_internalOuterEdges_iff.mp he).2.2) hadj hh r hr (fun _ ↦ a) (fun _ _ ↦ ha)
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact_mod_cast (card_le_univ (internalOuterEdges G (W.U i.succ))).trans (card_sym2_le_square V)

theorem InternalReserveSupplyGood.preliminary_pairSafe_supply
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A P M : TripleSystemOn V} {U : Finset V}
    {a target : ℕ} {bits : Sym2 V → Bool}
    (hgood : InternalReserveSupplyGood G A U a bits) (htarget : target ≤ a)
    (hold : G ≤ leaveGraph P)
    (hM : M ⊆ reserveProtectedAvailable (reserveEdges G U bits) A) :
    ∀ e ∈ preliminaryResidualInternalEdges G U (P ∪ M),
      target ≤ (activeReserveWedgeVertices G U
        (iterationExtensionVertices (pairSafeAvailable A (P ∪ M))
          (SimpleGraph.edge e.out.1 e.out.2) U) e.out.1 e.out.2 bits).card := by
  intro e he
  have hs := hgood e (preliminaryResidualInternalEdges_subset_internalOuterEdges G U (P ∪ M) he)
  exact (htarget.trans hs.le).trans (card_activeReserveWedgeVertices_pairSafe_ge he hold hM)

end

end Erdos207
