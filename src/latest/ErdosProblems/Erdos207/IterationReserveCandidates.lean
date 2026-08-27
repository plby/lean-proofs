/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveWedgeSampling
import ErdosProblems.Erdos207.GreedyObstruction

/-!
# Iteration-typical candidate supply in the reserve graph

This is the exact finite bridge from KSSS iteration-typicality to the
internal-edge reserve calculation in Section 10.2.1.  The one-edge rooted
extension set has the prescribed size, and independent reserve sampling
retains its two-edge wedges with the proved binomial lower-tail bound.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

lemma graphEdges_edge
    {V : Type*} [Fintype V] [DecidableEq V] {u v : V} (huv : u ≠ v) :
    graphEdges (SimpleGraph.edge u v) = {s(u, v)} := by
  ext e
  rw [mem_graphEdges_iff, SimpleGraph.edgeSet_edge]
  simp only [Set.mem_sdiff, Set.mem_singleton_iff, Sym2.mem_diagSet,
    mem_singleton]
  constructor
  · exact fun h ↦ h.1
  · intro h
    subst e
    exact ⟨rfl, by simpa [Sym2.mk_isDiag_iff] using huv⟩

lemma graphSupportFinset_edge
    {V : Type*} [Fintype V] [DecidableEq V] {u v : V} (huv : u ≠ v) :
    graphSupportFinset (SimpleGraph.edge u v) = {u, v} := by
  ext x
  rw [mem_graphSupportFinset_iff]
  simp only [SimpleGraph.edge_adj, mem_insert, mem_singleton]
  constructor
  · rintro ⟨w, ⟨hx | hx, _⟩⟩
    · exact Or.inl hx.1
    · exact Or.inr hx.1
  · intro hx
    rcases hx with rfl | rfl
    · exact ⟨v, ⟨Or.inl ⟨rfl, rfl⟩, huv⟩⟩
    · exact ⟨u, ⟨Or.inr ⟨rfl, rfl⟩, huv.symm⟩⟩

lemma edge_graphSupportedOn
    {V : Type*} [DecidableEq V] {U : Finset V} {u v : V}
    (hu : u ∈ U) (hv : v ∈ U) :
    GraphSupportedOn (SimpleGraph.edge u v) (U : Set V) := by
  intro x y hxy
  rw [SimpleGraph.edge_adj] at hxy
  rcases hxy.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hu, hv⟩
  · exact ⟨hv, hu⟩

/-- An extension vertex for the one-edge pattern gives both wedge edges in
the ambient graph. -/
lemma iterationExtensionVertices_edge_adjacencies
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A : TripleSystemOn V} {U : Finset V}
    {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (htri : ConsistsOfTriangles G A)
    (hw : w ∈ iterationExtensionVertices A (SimpleGraph.edge u v) U) :
    G.Adj u w ∧ G.Adj v w := by
  have hwdata := mem_iterationExtensionVertices_iff.mp hw
  have hedge : s(u, v) ∈ graphEdges (SimpleGraph.edge u v) := by
    rw [graphEdges_edge huv]
    simp
  obtain ⟨T, hTA, hwT, heT⟩ := hwdata.2 s(u, v) hedge
  have huvT := mk_mem_tripleEdgeFinset_iff.mp heT
  exact ⟨htri T hTA u huvT.1 w hwT huw,
    htri T hTA v huvT.2.1 w hwT hvw⟩

/-- For a one-edge pattern, an extension vertex is represented by the
canonical triple through the two endpoints and that vertex. -/
lemma iterationExtensionVertices_edge_thirdVertexTriple_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : TripleSystemOn V} {U : Finset V}
    {u v w : V} (huv : u ≠ v) (hu : u ∉ U) (hv : v ∉ U)
    (hw : w ∈ iterationExtensionVertices A (SimpleGraph.edge u v) U) :
    let w' : ThirdVertex u v :=
      ⟨w, fun h ↦ hu (h ▸ iterationExtensionVertices_subset A
        (SimpleGraph.edge u v) U hw),
        fun h ↦ hv (h ▸ iterationExtensionVertices_subset A
          (SimpleGraph.edge u v) U hw)⟩
    thirdVertexTriple huv w' ∈ A := by
  dsimp only
  have hwdata := mem_iterationExtensionVertices_iff.mp hw
  have hedge : s(u, v) ∈ graphEdges (SimpleGraph.edge u v) := by
    rw [graphEdges_edge huv]
    simp
  obtain ⟨T, hTA, hwT, heT⟩ := hwdata.2 s(u, v) hedge
  have huvT := mk_mem_tripleEdgeFinset_iff.mp heT
  have hsub :
      (thirdVertexTriple huv
        ⟨w, fun h ↦ hu (h ▸ hwdata.1), fun h ↦ hv (h ▸ hwdata.1)⟩).1 ⊆ T.1 := by
    intro x hx
    simp only [thirdVertexTriple, tripleOfThree, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact huvT.1
    · exact huvT.2.1
    · exact hwT
  have heq :
      thirdVertexTriple huv
        ⟨w, fun h ↦ hu (h ▸ hwdata.1), fun h ↦ hv (h ▸ hwdata.1)⟩ = T := by
    apply Subtype.ext
    exact Finset.eq_of_subset_of_card_le hsub (by
      rw [T.2]
      exact (thirdVertexTriple huv
        ⟨w, fun h ↦ hu (h ▸ hwdata.1), fun h ↦ hv (h ▸ hwdata.1)⟩).2.ge)
  rw [heq]
  exact hTA

/-- The one-edge instance of iteration-typicality. -/
theorem IsIterationTypical.edge_extension_window
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta ξ : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W k G A p eta ξ h)
    (i : Fin ell) (hki : k.val ≤ i.val)
    {u v : V} (huv : u ≠ v) (hu : u ∈ W.U i.castSucc)
    (hv : v ∈ W.U i.castSucc) (huvG : G.Adj u v) (hh : 2 ≤ h) :
    WithinMultiplicativeError ξ
      ((iterationExtensionVertices A (SimpleGraph.edge u v)
        (W.U i.succ)).card : ℝ≥0)
      (p ^ 2 * eta * (W.U i.succ).card) := by
  have hraw := htyp.2 i hki i.succ (Or.inr rfl)
    (SimpleGraph.edge u v)
    (SimpleGraph.edge_le_iff G |>.mpr (Or.inr huvG))
    (edge_graphSupportedOn hu hv) (by
      rw [graphSupportFinset_edge huv, card_pair huv]
      exact hh)
  rw [graphSupportFinset_edge huv, card_pair huv,
    graphEdges_edge huv, card_singleton, pow_one] at hraw
  exact hraw

/-- Iteration-typicality supplies the deterministic candidate count, while
the reserve law supplies the exact probability that too few of those
candidates retain both crossing edges. -/
theorem iterationTypical_reserve_internal_candidate_supply
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {stage : Fin (ell + 1)}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta ξ : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta ξ h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    {u v : V} (huv : u ≠ v)
    (huOuter : u ∈ W.U i.castSucc) (hvOuter : v ∈ W.U i.castSucc)
    (huInner : u ∉ W.U i.succ) (hvInner : v ∉ W.U i.succ)
    (huvG : G.Adj u v) (hh : 2 ≤ h)
    (r : ℝ≥0) (hr : r ≤ 1) (a : ℕ) :
    let S := iterationExtensionVertices A (SimpleGraph.edge u v) (W.U i.succ)
    WithinMultiplicativeError ξ (S.card : ℝ≥0)
        (p ^ 2 * eta * (W.U i.succ).card) ∧
      (reserveEdgeLaw G (W.U i.succ) r hr).probability
          (fun ω ↦
            (activeReserveWedgeVertices G (W.U i.succ) S u v ω).card ≤ a) ≤
        (Nat.choose S.card (S.card - a) : ℝ≥0) *
          (1 - r ^ 2) ^ (S.card - a) := by
  dsimp only
  let S := iterationExtensionVertices A (SimpleGraph.edge u v) (W.U i.succ)
  have hwindow := htyp.edge_extension_window i hstage huv huOuter hvOuter huvG hh
  have hSU : S ⊆ W.U i.succ :=
    iterationExtensionVertices_subset A (SimpleGraph.edge u v) (W.U i.succ)
  have hadj : ∀ w ∈ S, G.Adj u w ∧ G.Adj v w := by
    intro w hw
    have hwInner := hSU hw
    apply iterationExtensionVertices_edge_adjacencies huv
    · intro huw
      subst w
      exact huInner hwInner
    · intro hvw
      subst w
      exact hvInner hwInner
    · exact htri
    · exact hw
  exact ⟨hwindow,
    reserveEdgeLaw_probability_activeReserveWedgeVertices_card_le_le
      G (W.U i.succ) S u v r hr huv huInner hvInner hSU hadj a⟩

/-- Exponentially small failure probability for the same internal-edge
candidate supply.  This removes the combinatorial loss in the elementary
union bound and is the estimate needed uniformly over all leftover edges. -/
theorem iterationTypical_reserve_internal_candidate_supply_exp
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {stage : Fin (ell + 1)}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta ξ : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta ξ h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    {u v : V} (huv : u ≠ v)
    (huOuter : u ∈ W.U i.castSucc) (hvOuter : v ∈ W.U i.castSucc)
    (huInner : u ∉ W.U i.succ) (hvInner : v ∉ W.U i.succ)
    (huvG : G.Adj u v) (hh : 2 ≤ h)
    (r : ℝ≥0) (hr : r ≤ 1) (a : ℕ)
    (ha : let S :=
        iterationExtensionVertices A (SimpleGraph.edge u v) (W.U i.succ)
      (a : ℝ) ≤ ((r ^ 2 : ℝ≥0) : ℝ) * S.card / 4) :
    let S := iterationExtensionVertices A (SimpleGraph.edge u v) (W.U i.succ)
    WithinMultiplicativeError ξ (S.card : ℝ≥0)
        (p ^ 2 * eta * (W.U i.succ).card) ∧
      ((reserveEdgeLaw G (W.U i.succ) r hr).probability
          (fun ω ↦
            (activeReserveWedgeVertices G (W.U i.succ) S u v ω).card ≤ a) : ℝ) ≤
        Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * S.card) / 4) := by
  dsimp only at ha ⊢
  let S := iterationExtensionVertices A (SimpleGraph.edge u v) (W.U i.succ)
  have hwindow := htyp.edge_extension_window i hstage huv huOuter hvOuter huvG hh
  have hSU : S ⊆ W.U i.succ :=
    iterationExtensionVertices_subset A (SimpleGraph.edge u v) (W.U i.succ)
  have hadj : ∀ w ∈ S, G.Adj u w ∧ G.Adj v w := by
    intro w hw
    have hwInner := hSU hw
    apply iterationExtensionVertices_edge_adjacencies huv
    · intro huw
      subst w
      exact huInner hwInner
    · intro hvw
      subst w
      exact hvInner hwInner
    · exact htri
    · exact hw
  exact ⟨hwindow,
    reserveEdgeLaw_probability_activeReserveWedgeVertices_card_le_le_exp
      G (W.U i.succ) S u v r hr huv huInner hvInner hSU hadj a ha⟩

end

end Erdos207
