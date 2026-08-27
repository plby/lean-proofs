/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IterationLinkExtensions

/-!
# Degree and codegree windows for iteration-typical links

This file specializes KSSS iteration typicality to the one-edge and
two-edge-star patterns.  The resulting natural-number bounds are stated with
explicit scalar rounding hypotheses, so later parameter selection can use
them without concealing floor or ceiling operations.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The two-edge-star instance of iteration typicality. -/
theorem IsIterationTypical.linkStar_extension_window
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta ξ : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W k G A p eta ξ h)
    (i : Fin ell) (hki : k.val ≤ i.val)
    {center x y : V}
    (hcx : center ≠ x) (hcy : center ≠ y) (hxy : x ≠ y)
    (hc : center ∈ W.U i.castSucc)
    (hx : x ∈ W.U i.castSucc) (hy : y ∈ W.U i.castSucc)
    (hcxG : G.Adj center x) (hcyG : G.Adj center y) (hh : 3 ≤ h) :
    WithinMultiplicativeError ξ
      ((iterationExtensionVertices A (linkStarGraph center x y)
        (W.U i.succ)).card : ℝ≥0)
      (p ^ 3 * eta ^ 2 * (W.U i.succ).card) := by
  have hraw := htyp.2 i hki i.succ (Or.inr rfl)
    (linkStarGraph center x y)
    (linkStarGraph_le hcxG hcyG)
    (linkStarGraph_supportedOn hc hx hy) (by
      rw [graphSupportFinset_linkStarGraph_card hcx hcy hxy]
      exact hh)
  have hedge : s(center, x) ≠ s(center, y) := by
    intro he
    exact hxy (Sym2.congr_right.mp he)
  rw [graphSupportFinset_linkStarGraph_card hcx hcy hxy,
    graphEdges_linkStarGraph hcx hcy, card_pair hedge] at hraw
  exact hraw

/-- Iteration typicality gives rounded lower and upper bounds for every full
available link degree into the next vortex level.  The lower scalar includes
the exact one-vertex endpoint loss from `iterationExtensionVertices`. -/
theorem IsIterationTypical.ambientLinkDegree_bounds
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta ξ : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W k G A p eta ξ h)
    (i : Fin ell) (hki : k.val ≤ i.val)
    {center x : V} (hcx : center ≠ x)
    (hc : center ∈ W.U i.castSucc) (hx : x ∈ W.U i.castSucc)
    (hcInner : center ∉ W.U i.succ)
    (hcxG : G.Adj center x) (hh : 2 ≤ h)
    (m D : ℕ)
    (hlower : (m + 1 : ℝ≥0) ≤
      (1 - ξ) * (p ^ 2 * eta * (W.U i.succ).card))
    (hupper : (1 + ξ) * (p ^ 2 * eta * (W.U i.succ).card) ≤
      (D : ℝ≥0)) :
    m ≤ (ambientLinkNeighborsIn center A (W.U i.succ) x).card ∧
      (ambientLinkNeighborsIn center A (W.U i.succ) x).card ≤ D := by
  have hwindow := htyp.edge_extension_window i hki hcx hc hx hcxG hh
  let E := iterationExtensionVertices A (SimpleGraph.edge center x)
    (W.U i.succ)
  let N := ambientLinkNeighborsIn center A (W.U i.succ) x
  have hEcast : (m + 1 : ℝ≥0) ≤ (E.card : ℝ≥0) := by
    exact hlower.trans hwindow.1
  have hEnat : m + 1 ≤ E.card := by
    exact_mod_cast hEcast
  have hEN : E.card ≤ N.card + 1 := by
    simpa only [E, N] using
      card_iterationExtensionVertices_edge_le_ambient_add_one hcx A
        (W.U i.succ) hcInner
  have hNsubset : N ⊆ E := by
    simpa only [N, E] using
      ambientLinkNeighborsIn_subset_iterationExtensionVertices_edge
        hcx A (W.U i.succ)
  have hNupperCast : (N.card : ℝ≥0) ≤ (D : ℝ≥0) := by
    calc
      (N.card : ℝ≥0) ≤ (E.card : ℝ≥0) := by
        exact_mod_cast card_le_card hNsubset
      _ ≤ (1 + ξ) * (p ^ 2 * eta * (W.U i.succ).card) := hwindow.2
      _ ≤ (D : ℝ≥0) := hupper
  constructor
  · change m ≤ N.card
    omega
  · exact_mod_cast hNupperCast

/-- The two-edge-star window gives the rounded upper bound for every full
ambient link codegree into the next vortex level. -/
theorem IsIterationTypical.ambientLinkCodegree_upper
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta ξ : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W k G A p eta ξ h)
    (i : Fin ell) (hki : k.val ≤ i.val)
    {center x y : V}
    (hcx : center ≠ x) (hcy : center ≠ y) (hxy : x ≠ y)
    (hc : center ∈ W.U i.castSucc)
    (hx : x ∈ W.U i.castSucc) (hy : y ∈ W.U i.castSucc)
    (hcxG : G.Adj center x) (hcyG : G.Adj center y) (hh : 3 ≤ h)
    (codegree : ℕ)
    (hupper : (1 + ξ) *
      (p ^ 3 * eta ^ 2 * (W.U i.succ).card) ≤ (codegree : ℝ≥0)) :
    (ambientLinkCommonNeighborsIn center A (W.U i.succ) x y).card ≤
      codegree := by
  have hwindow := htyp.linkStar_extension_window i hki hcx hcy hxy hc hx hy
    hcxG hcyG hh
  let C := ambientLinkCommonNeighborsIn center A (W.U i.succ) x y
  let E := iterationExtensionVertices A (linkStarGraph center x y)
    (W.U i.succ)
  have hCE : C ⊆ E := by
    simpa only [C, E] using
      ambientLinkCommonNeighborsIn_subset_iterationExtensionVertices_star
        hcx hcy A (W.U i.succ)
  have hcast : (C.card : ℝ≥0) ≤ (codegree : ℝ≥0) := by
    calc
      (C.card : ℝ≥0) ≤ (E.card : ℝ≥0) := by
        exact_mod_cast card_le_card hCE
      _ ≤ (1 + ξ) * (p ^ 3 * eta ^ 2 * (W.U i.succ).card) := hwindow.2
      _ ≤ (codegree : ℝ≥0) := hupper
  exact_mod_cast hcast

end

end Erdos207
