/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveRegularizationProbability
import ErdosProblems.Erdos207.IterationTriangleRegularization

/-! # Actual iteration data and reserve sampling supply protected triangle regularization -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsIterationTypical.proper_clique_error_on_stage
    {V : Type*} [Fintype V] [DecidableEq V] {ell h : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V} {A : TripleSystemOn V}
    {p tau xi : ℝ≥0} (htyp : IsIterationTypical W k G A p tau xi h)
    (i : Fin ell) (hki : k.val ≤ i.val) (hh : 4 ≤ h)
    (hG : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hA : ∀ T ∈ A, tripleEdgeFinset T ⊆ graphEdges G) :
    ∀ S ∈ smallCliqueFamily G (W.U i.castSucc),
      |((properPatternExtensions A (cliquePattern S) univ).card : ℝ) -
        (p : ℝ) ^ S.card * (tau : ℝ) ^ (S.card.choose 2) * (W.U i.castSucc).card| ≤
      (xi : ℝ) * ((p : ℝ) ^ S.card * (tau : ℝ) ^ (S.card.choose 2) * (W.U i.castSucc).card) + S.card := by
  intro S hS
  have hm := (mem_smallCliqueFamily_iff G (W.U i.castSucc) S).mp hS
  have hvertices : ∀ T ∈ A, T.1 ⊆ W.U i.castSucc :=
    fun T hT ↦ triple_supported_of_graph_edges G (W.U i.castSucc) T hG (hA T hT)
  rw [properPatternExtensions_univ_eq_of_supported A (cliquePattern S) (W.U i.castSucc)
    (cliquePattern_edges_nonempty S hm.2.1) hvertices]
  exact htyp.clique_proper_extension_error i hki i.castSucc (Or.inl rfl) S hm.2.1
    (hm.2.2.1.trans hh) hm.1 hm.2.2.2

theorem IsIterationTypical.reserve_probability_no_regularized_triangles
    {V : Type*} [Fintype V] [DecidableEq V] {ell h : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V} {A : TripleSystemOn V}
    {p tau xi : ℝ≥0} (htyp : IsIterationTypical W k G A p tau xi h)
    (i : Fin ell) (hki : k.val ≤ i.val) (hh : 4 ≤ h)
    (U : Finset V) (r : ℝ≥0) (hr1 : r ≤ 1)
    (hG : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hA : ∀ T ∈ A, tripleEdgeFinset T ⊆ graphEdges G)
    (hp : 0 < p) (hp1 : p ≤ 1) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hxi : xi ≤ 1 / 1536) (hr : r ≤ 1 / 24576)
    (hdensity : 6144 ≤ p ^ 4 * tau ^ 6 * (W.U i.castSucc).card)
    (hinner : (U.card : ℝ≥0) ≤ p ^ 4 * tau ^ 6 * (W.U i.castSucc).card / 1536)
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hfailure : 2 * ((W.U i.castSucc).card : ℝ) ^ 2 *
      Real.exp (-eta ^ 2 * ((p : ℝ) ^ 2 * tau * (W.U i.castSucc).card) / 16) < 1) :
    ((reserveEdgeLaw G U r hr1).probability
      (fun omega ↦ ¬ HasReserveRegularizedTriangles G U (W.U i.castSucc) A p tau eta omega) : ℝ) ≤
      12 * ((W.U i.castSucc).card + 1 : ℝ) ^ 4 *
        Real.exp (-(r : ℝ) * ((p : ℝ) ^ 4 * (tau : ℝ) ^ 6 * (W.U i.castSucc).card) / 8) :=
  reserveEdgeLaw_probability_no_regularized_triangles G U (W.U i.castSucc) A p tau xi r hr1 hG hA
    hp hp1 htau htau1 hxi hr hdensity hinner
    (htyp.proper_clique_error_on_stage i hki hh hG hA) eta heta heta1 hfailure

end

end Erdos207
