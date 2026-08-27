/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ProtectedGraphMass
import ErdosProblems.Erdos207.TriangleIncidenceMass

/-! # The actual protected regularized family supplies the auxiliary mass lower bound -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem reserveProtected_regularized_triangle_mass
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D U : Finset V) (R : Finset (Sym2 V)) (A B : TripleSystemOn V)
    (hG : GraphSupportedOn G (D : Set V)) (hR : R ⊆ crossingEdges G U)
    (hB : B ⊆ reserveProtectedOuterAvailable G U R A) (p tau eta : ℝ)
    (_hp : 0 ≤ p) (htau : 0 ≤ tau) (heta : eta ≤ 1 / 2)
    (hdegree : ∀ v ∈ D, p * D.card / 2 ≤ (neighborsIn G D v).card)
    (hinner : (U.card : ℝ) ≤ p * D.card / 8)
    (hregular : ∀ e ∈ graphEdges (reserveProtectedOuterGraph G U R),
      |((B.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card : ℝ) - p ^ 2 * tau * D.card / 4| ≤
        eta * (p ^ 2 * tau * D.card / 4)) :
    p ^ 3 * tau * (D.card : ℝ) ^ 3 / 192 ≤ (B.card : ℝ) := by
  have hBedge : ∀ T ∈ B, tripleEdgeFinset T ⊆ graphEdges (reserveProtectedOuterGraph G U R) := by
    intro T hT
    rw [graphEdges_reserveProtectedOuterGraph]
    exact (mem_reserveProtectedOuterAvailable_iff.mp (hB hT)).2
  have hmass := triangle_family_mass_of_regular_degrees (reserveProtectedOuterGraph G U R) B hBedge
    (p ^ 2 * tau * D.card / 4) eta (by positivity) heta hregular
  have hgraph := reserveProtected_graph_mass_of_neighbor_lower G D U R hG hR p hdegree hinner
  calc
    _ = (p * (D.card : ℝ) ^ 2 / 8) * (p ^ 2 * tau * D.card / 24) := by ring
    _ ≤ (graphEdges (reserveProtectedOuterGraph G U R)).card * (p ^ 2 * tau * D.card / 24) :=
      mul_le_mul_of_nonneg_right hgraph (by positivity)
    _ = (graphEdges (reserveProtectedOuterGraph G U R)).card * (p ^ 2 * tau * D.card / 4) / 6 := by ring
    _ ≤ _ := hmass

theorem IsIterationTypical.reserveProtected_regularized_triangle_mass
    {V : Type*} [Fintype V] [DecidableEq V] {ell h : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V} {A : TripleSystemOn V}
    {p tau xi : ℝ≥0} (htyp : IsIterationTypical W k G A p tau xi h)
    (i : Fin ell) (hki : k.val ≤ i.val) (hxi : xi ≤ 1 / 2)
    (hG : GraphSupportedOn G (W.U i.castSucc : Set V))
    (U : Finset V) (R : Finset (Sym2 V)) (hR : R ⊆ crossingEdges G U)
    (B : TripleSystemOn V) (hB : B ⊆ reserveProtectedOuterAvailable G U R A)
    (eta : ℝ) (heta : eta ≤ 1 / 2)
    (hinner : (U.card : ℝ≥0) ≤ p * (W.U i.castSucc).card / 8)
    (hregular : ∀ e ∈ graphEdges (reserveProtectedOuterGraph G U R),
      |((B.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card : ℝ) -
        (p : ℝ) ^ 2 * tau * (W.U i.castSucc).card / 4| ≤
        eta * ((p : ℝ) ^ 2 * tau * (W.U i.castSucc).card / 4)) :
    (p : ℝ) ^ 3 * tau * ((W.U i.castSucc).card : ℝ) ^ 3 / 192 ≤ (B.card : ℝ) := by
  apply Erdos207.reserveProtected_regularized_triangle_mass G (W.U i.castSucc) U R A B hG hR hB p tau eta
    p.coe_nonneg tau.coe_nonneg heta _ (by exact_mod_cast hinner) hregular
  intro v hv
  have hbound := (((htyp.1 i hki).1 v hv).mono hxi).1
  have hhalf : (1 - (1 / 2 : ℝ≥0)) = 1 / 2 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub (by norm_num)]
    norm_num
  rw [hhalf] at hbound
  have hr : (1 / 2 : ℝ) * ((p : ℝ) * (W.U i.castSucc).card) ≤ (neighborsIn G (W.U i.castSucc) v).card := by
    exact_mod_cast hbound
  linarith

end

end Erdos207
