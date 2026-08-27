/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ProtectedTriangleMass
import ErdosProblems.Erdos207.RegularizedAuxiliaryMassScalars
import ErdosProblems.Erdos207.ReserveRegularizationProbability

/-! # A nonempty auxiliary vertex universe from actual reserve regularization -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsIterationTypical.exists_reserve_regularized_auxiliary_mass
    {V : Type*} [Fintype V] [DecidableEq V] {ell h : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V} {A : TripleSystemOn V}
    {p tau xi : ℝ≥0} (htyp : IsIterationTypical W k G A p tau xi h)
    (i : Fin ell) (hki : k.val ≤ i.val) (hxi : xi ≤ 1 / 2)
    (hG : GraphSupportedOn G (W.U i.castSucc : Set V))
    (U : Finset V) (omega : Sym2 V → Bool)
    (hp : 0 < p) (hp1 : p ≤ 1) (htau1 : tau ≤ 1)
    (tau0 : ℝ≥0) (htau0 : 0 < tau0) (htau : tau0 ≤ tau)
    (hn : 0 < (W.U i.castSucc).card)
    (hinner : (U.card : ℝ≥0) ≤ p ^ 4 * tau ^ 6 * (W.U i.castSucc).card / 1536)
    (eta : ℝ) (heta : eta ≤ 1 / 2)
    (hregular : HasReserveRegularizedTriangles G U (W.U i.castSucc) A p tau eta omega) :
    ∃ B ⊆ reserveProtectedOuterAvailable G U (reserveEdges G U omega) A,
      B.Nonempty ∧
      p ^ 3 * ((W.U i.castSucc).card : ℝ≥0) ^ 3 / (192 / tau0) ≤ B.card ∧
      (∀ e ∈ graphEdges (reserveProtectedOuterGraph G U (reserveEdges G U omega)),
        |((B.filter (fun T ↦ e ∈ tripleEdgeFinset T)).card : ℝ) -
          (p : ℝ) ^ 2 * tau * (W.U i.castSucc).card / 4| ≤
          eta * ((p : ℝ) ^ 2 * tau * (W.U i.castSucc).card / 4)) := by
  obtain ⟨B, hB, hreg⟩ := hregular
  have hmass := htyp.reserveProtected_regularized_triangle_mass i hki hxi hG U
    (reserveEdges G U omega) (reserveEdges_subset_crossingEdges G U omega) B hB eta heta
    (reserve_inner_margin_for_graph_mass U.card (W.U i.castSucc).card p tau hp1 htau1 hinner) hreg
  have hnormalized := regularized_auxiliary_mass_normalization (W.U i.castSucc).card B.card p tau tau0
    htau0 htau hmass
  have hn' : (0 : ℝ≥0) < (W.U i.castSucc).card := by exact_mod_cast hn
  have hpositive : (0 : ℝ≥0) < p ^ 3 * ((W.U i.castSucc).card : ℝ≥0) ^ 3 / (192 / tau0) := by positivity
  have hcard : 0 < B.card := by exact_mod_cast hpositive.trans_le hnormalized
  exact ⟨B, hB, card_pos.mp hcard, hnormalized, hreg⟩

end

end Erdos207
