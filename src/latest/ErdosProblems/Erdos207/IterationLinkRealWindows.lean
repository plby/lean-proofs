/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IterationLinkTypicality

/-! # Exact real-valued source windows, including the one-vertex link-degree loss -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem WithinMultiplicativeError.real_window
    {xi actual target : ℝ≥0} (h : WithinMultiplicativeError xi actual target) (hxi : xi ≤ 1) :
    (1-(xi : ℝ))*(target : ℝ) ≤ actual ∧ (actual : ℝ) ≤ (1+(xi : ℝ))*(target : ℝ) := by
  constructor
  · have hh : (((1-xi)*target : ℝ≥0) : ℝ) ≤ actual := by exact_mod_cast h.1
    simpa only [NNReal.coe_mul, NNReal.coe_sub hxi, NNReal.coe_one] using hh
  · exact_mod_cast h.2

theorem IsIterationTypical.neighbor_real_window
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell+1)} {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ} (htyp : IsIterationTypical W k G A p eta xi h)
    (hxi : xi ≤ 1) (i : Fin ell) (hki : k.val ≤ i.val) (v : V) (hv : v ∈ W.U i.castSucc) :
    (1-(xi : ℝ))*((p : ℝ)*(W.U i.succ).card) ≤ ((neighborsIn G (W.U i.succ) v).card : ℝ) ∧
      ((neighborsIn G (W.U i.succ) v).card : ℝ) ≤ (1+(xi : ℝ))*((p : ℝ)*(W.U i.succ).card) := by
  have hb := ((htyp.1 i hki).2 v hv).real_window hxi
  exact_mod_cast hb

theorem IsIterationTypical.ambientLinkDegree_real_window
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell+1)} {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ} (htyp : IsIterationTypical W k G A p eta xi h)
    (hxi : xi ≤ 1) (i : Fin ell) (hki : k.val ≤ i.val)
    {center x : V} (hcx : G.Adj center x)
    (hc : center ∈ W.U i.castSucc) (hx : x ∈ W.U i.castSucc)
    (hcInner : center ∉ W.U i.succ) (hh : 2 ≤ h) :
    (1-(xi : ℝ))*((p : ℝ)^2*eta*(W.U i.succ).card)-1 ≤
        ((ambientLinkNeighborsIn center A (W.U i.succ) x).card : ℝ) ∧
      ((ambientLinkNeighborsIn center A (W.U i.succ) x).card : ℝ) ≤
        (1+(xi : ℝ))*((p : ℝ)^2*eta*(W.U i.succ).card) := by
  have hwindow := (htyp.edge_extension_window i hki hcx.ne hc hx hcx hh).real_window hxi
  have hwindow' : (1-(xi : ℝ))*((p : ℝ)^2*eta*(W.U i.succ).card) ≤
        ((iterationExtensionVertices A (SimpleGraph.edge center x) (W.U i.succ)).card : ℝ) ∧
      ((iterationExtensionVertices A (SimpleGraph.edge center x) (W.U i.succ)).card : ℝ) ≤
        (1+(xi : ℝ))*((p : ℝ)^2*eta*(W.U i.succ).card) := by exact_mod_cast hwindow
  have hcount : ((iterationExtensionVertices A (SimpleGraph.edge center x) (W.U i.succ)).card : ℝ) ≤
      (ambientLinkNeighborsIn center A (W.U i.succ) x).card+1 := by
    exact_mod_cast card_iterationExtensionVertices_edge_le_ambient_add_one hcx.ne A (W.U i.succ) hcInner
  have hcount' : ((ambientLinkNeighborsIn center A (W.U i.succ) x).card : ℝ) ≤
      (iterationExtensionVertices A (SimpleGraph.edge center x) (W.U i.succ)).card := by
    exact_mod_cast card_le_card (ambientLinkNeighborsIn_subset_iterationExtensionVertices_edge hcx.ne A (W.U i.succ))
  exact ⟨by linarith only [hwindow'.1, hcount], hcount'.trans hwindow'.2⟩

theorem IsIterationTypical.ambientLinkCodegree_real_upper
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell+1)} {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ} (htyp : IsIterationTypical W k G A p eta xi h)
    (hxi : xi ≤ 1) (i : Fin ell) (hki : k.val ≤ i.val)
    {center x y : V} (hcx : G.Adj center x) (hcy : G.Adj center y) (hxy : x ≠ y)
    (hc : center ∈ W.U i.castSucc) (hx : x ∈ W.U i.castSucc) (hy : y ∈ W.U i.castSucc) (hh : 3 ≤ h) :
    ((ambientLinkCommonNeighborsIn center A (W.U i.succ) x y).card : ℝ) ≤
      (1+(xi : ℝ))*((p : ℝ)^3*eta^2*(W.U i.succ).card) := by
  have hwindow := (htyp.linkStar_extension_window i hki hcx.ne hcy.ne hxy hc hx hy hcx hcy hh).real_window hxi
  have hupper : ((iterationExtensionVertices A (linkStarGraph center x y) (W.U i.succ)).card : ℝ) ≤
      (1+(xi : ℝ))*((p : ℝ)^3*eta^2*(W.U i.succ).card) := by exact_mod_cast hwindow.2
  have hcount : ((ambientLinkCommonNeighborsIn center A (W.U i.succ) x y).card : ℝ) ≤
      (iterationExtensionVertices A (linkStarGraph center x y) (W.U i.succ)).card := by
    exact_mod_cast card_le_card
      (ambientLinkCommonNeighborsIn_subset_iterationExtensionVertices_star hcx.ne hcy.ne A (W.U i.succ))
  exact hcount.trans hupper

end

end Erdos207
