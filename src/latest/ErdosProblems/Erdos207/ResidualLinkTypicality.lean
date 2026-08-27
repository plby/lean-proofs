/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IterationLinkTypicality
import ErdosProblems.Erdos207.CrossingLinkGraph

/-!
# Restricting typical links to residual neighbors

The chosen bipartition is made on the exact residual-neighbor set after the
first two cover stages.  Full next-level link degrees come from iteration
typicality.  A full-level link neighbor missing from the residual set must
lie on a center edge already covered by the preliminary packing, so the only
lower-degree loss is the covered degree at that center.  Upper degrees and
codegrees pass to the residual set by monotonicity.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- An ambient link triple has three pairwise distinct displayed vertices. -/
lemma ambientLinkRelation_pairwise_ne
    {V : Type*} [DecidableEq V] {center : V}
    {A : TripleSystemOn V} {x y : V}
    (h : ambientLinkRelation center A x y) :
    center ≠ x ∧ center ≠ y ∧ x ≠ y := by
  obtain ⟨T, _hTA, hval⟩ := h
  have hcard : ({center, x, y} : Finset V).card = 3 := by
    rw [← hval]
    exact T.2
  constructor
  · intro hcx
    subst x
    have hle : ({center, center, y} : Finset V).card ≤ 2 := by
      have hsub : ({center, center, y} : Finset V) ⊆ {center, y} := by simp
      have hp := card_pair_eq_one_or_two (a := center) (b := y)
      exact (card_le_card hsub).trans (by omega)
    omega
  constructor
  · intro hcy
    subst y
    have hle : ({center, x, center} : Finset V).card ≤ 2 := by
      have hsub : ({center, x, center} : Finset V) ⊆ {center, x} := by
        intro z hz
        simp only [mem_insert, mem_singleton] at hz ⊢
        tauto
      have hp := card_pair_eq_one_or_two (a := center) (b := x)
      exact (card_le_card hsub).trans (by omega)
    omega
  · intro hxy
    subst y
    have hle : ({center, x, x} : Finset V).card ≤ 2 := by
      have hsub : ({center, x, x} : Finset V) ⊆ {center, x} := by simp
      have hp := card_pair_eq_one_or_two (a := center) (b := x)
      exact (card_le_card hsub).trans (by omega)
    omega

/-- Every pair represented by an available ambient link triple is an edge
of the graph in which the available family consists of triangles. -/
lemma ambientLinkRelation_graph_adjacencies
    {V : Type*} [DecidableEq V] {center : V}
    {G : SimpleGraph V} {A : TripleSystemOn V} {x y : V}
    (htri : ConsistsOfTriangles G A)
    (h : ambientLinkRelation center A x y) :
    G.Adj center x ∧ G.Adj center y ∧ G.Adj x y := by
  have hne := ambientLinkRelation_pairwise_ne h
  obtain ⟨T, hTA, hval⟩ := h
  have hcT : center ∈ T.1 := by rw [hval]; simp
  have hxT : x ∈ T.1 := by rw [hval]; simp
  have hyT : y ∈ T.1 := by rw [hval]; simp
  exact ⟨htri T hTA center hcT x hxT hne.1,
    htri T hTA center hcT y hyT hne.2.1,
    htri T hTA x hxT y hyT hne.2.2⟩

/-- Full-level link neighbors are covered by residual link neighbors plus
neighbors already covered by the preliminary family. -/
lemma ambientLinkNeighborsIn_subset_residual_union_covered
    {V : Type*} [Fintype V] [DecidableEq V]
    {center : V} {G : SimpleGraph V} [DecidableRel G.Adj]
    {A R : TripleSystemOn V} (htri : ConsistsOfTriangles G A)
    (U : Finset V) (x : V) :
    ambientLinkNeighborsIn center A U x ⊆
      ambientLinkNeighborsIn center A (residualNeighbors G R center) x ∪
        (coveredGraph R).neighborFinset center := by
  intro y hy
  have hydata := mem_ambientLinkNeighborsIn_iff.mp hy
  have hcyG := (ambientLinkRelation_graph_adjacencies htri hydata.2).2.1
  by_cases hcovered : (coveredGraph R).Adj center y
  · exact mem_union_right _ (by
      simpa only [SimpleGraph.mem_neighborFinset] using hcovered)
  · apply mem_union_left
    exact mem_ambientLinkNeighborsIn_iff.mpr
      ⟨mem_residualNeighbors_iff.mpr ⟨hcyG, hcovered⟩, hydata.2⟩

/-- Only already-covered neighbors which lie in the tested vortex level can
be lost when a full-level link is restricted to the residual neighbors. -/
lemma ambientLinkNeighborsIn_subset_residual_union_coveredIn
    {V : Type*} [Fintype V] [DecidableEq V]
    {center : V} {G : SimpleGraph V} [DecidableRel G.Adj]
    {A R : TripleSystemOn V} (htri : ConsistsOfTriangles G A)
    (U : Finset V) (x : V) :
    ambientLinkNeighborsIn center A U x ⊆
      ambientLinkNeighborsIn center A (residualNeighbors G R center) x ∪
        ((coveredGraph R).neighborFinset center ∩ U) := by
  intro y hy
  have hydata := mem_ambientLinkNeighborsIn_iff.mp hy
  have hcyG := (ambientLinkRelation_graph_adjacencies htri hydata.2).2.1
  by_cases hcovered : (coveredGraph R).Adj center y
  · apply mem_union_right
    exact mem_inter.mpr
      ⟨by simpa only [SimpleGraph.mem_neighborFinset] using hcovered,
        hydata.1⟩
  · apply mem_union_left
    exact mem_ambientLinkNeighborsIn_iff.mpr
      ⟨mem_residualNeighbors_iff.mpr ⟨hcyG, hcovered⟩, hydata.2⟩

/-- Restricting from a full vortex level to exact residual neighbors loses
at most the preliminary covered degree at the center. -/
lemma card_ambientLinkNeighborsIn_le_residual_add_coveredDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    {center : V} {G : SimpleGraph V} [DecidableRel G.Adj]
    {A R : TripleSystemOn V} (htri : ConsistsOfTriangles G A)
    (U : Finset V) (x : V) :
    (ambientLinkNeighborsIn center A U x).card ≤
      (ambientLinkNeighborsIn center A
        (residualNeighbors G R center) x).card +
        (coveredGraph R).degree center := by
  calc
    (ambientLinkNeighborsIn center A U x).card ≤
        (ambientLinkNeighborsIn center A (residualNeighbors G R center) x ∪
          (coveredGraph R).neighborFinset center).card :=
      card_le_card
        (ambientLinkNeighborsIn_subset_residual_union_covered htri U x)
    _ ≤ (ambientLinkNeighborsIn center A
          (residualNeighbors G R center) x).card +
        ((coveredGraph R).neighborFinset center).card := card_union_le _ _
    _ = (ambientLinkNeighborsIn center A
          (residualNeighbors G R center) x).card +
        (coveredGraph R).degree center := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]

/-- Localized form of the preceding cardinality estimate.  Preliminary
triangles wholly outside `U` make no contribution to this loss term. -/
lemma card_ambientLinkNeighborsIn_le_residual_add_coveredIn
    {V : Type*} [Fintype V] [DecidableEq V]
    {center : V} {G : SimpleGraph V} [DecidableRel G.Adj]
    {A R : TripleSystemOn V} (htri : ConsistsOfTriangles G A)
    (U : Finset V) (x : V) :
    (ambientLinkNeighborsIn center A U x).card ≤
      (ambientLinkNeighborsIn center A
        (residualNeighbors G R center) x).card +
        ((coveredGraph R).neighborFinset center ∩ U).card := by
  calc
    (ambientLinkNeighborsIn center A U x).card ≤
        (ambientLinkNeighborsIn center A (residualNeighbors G R center) x ∪
          ((coveredGraph R).neighborFinset center ∩ U)).card :=
      card_le_card
        (ambientLinkNeighborsIn_subset_residual_union_coveredIn htri U x)
    _ ≤ (ambientLinkNeighborsIn center A
          (residualNeighbors G R center) x).card +
        ((coveredGraph R).neighborFinset center ∩ U).card := card_union_le _ _

/-- Iteration typicality, one center-degree loss budget, and containment of
the residual neighbors in the next vortex level give full residual-link
degree and codegree bounds. -/
theorem IsIterationTypical.residualLink_degree_codegree_bounds_localized
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A R : TripleSystemOn V}
    {p eta ξ : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W k G A p eta ξ h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hki : k.val ≤ i.val)
    (center : V)
    (hcOuter : center ∈ W.U i.castSucc)
    (hcInner : center ∉ W.U i.succ)
    (hresInner : residualNeighbors G R center ⊆ W.U i.succ)
    (m D codegree loss : ℕ)
    (hcovered :
      ((coveredGraph R).neighborFinset center ∩ W.U i.succ).card ≤ loss)
    (hh : 3 ≤ h)
    (hlower : (m + loss + 1 : ℝ≥0) ≤
      (1 - ξ) * (p ^ 2 * eta * (W.U i.succ).card))
    (hupper : (1 + ξ) * (p ^ 2 * eta * (W.U i.succ).card) ≤
      (D : ℝ≥0))
    (hcodegree : (1 + ξ) *
      (p ^ 3 * eta ^ 2 * (W.U i.succ).card) ≤ (codegree : ℝ≥0)) :
    (∀ x ∈ residualNeighbors G R center,
      m ≤ (ambientLinkNeighborsIn center A
        (residualNeighbors G R center) x).card ∧
      (ambientLinkNeighborsIn center A
        (residualNeighbors G R center) x).card ≤ D) ∧
    (∀ x ∈ residualNeighbors G R center,
      ∀ y ∈ residualNeighbors G R center, x ≠ y →
        (ambientLinkCommonNeighborsIn center A
          (residualNeighbors G R center) x y).card ≤ codegree) := by
  have hinnerOuter : W.U i.succ ⊆ W.U i.castSucc := by
    exact W.antitone i.castSucc i.succ i.castSucc_lt_succ.le
  constructor
  · intro x hxRes
    have hxInner := hresInner hxRes
    have hxOuter := hinnerOuter hxInner
    have hcxG := (mem_residualNeighbors_iff.mp hxRes).1
    have hcx : center ≠ x := hcxG.ne
    have hfull := htyp.ambientLinkDegree_bounds i hki hcx hcOuter hxOuter
      hcInner hcxG (by omega) (m + loss) D (by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hlower) hupper
    constructor
    · have hloss :=
        card_ambientLinkNeighborsIn_le_residual_add_coveredIn
          (center := center) (R := R) htri (W.U i.succ) x
      omega
    · exact (card_le_card
        (BalancedBisection.ambientLinkNeighborsIn_mono hresInner x)).trans
          hfull.2
  · intro x hxRes y hyRes hxy
    have hxInner := hresInner hxRes
    have hyInner := hresInner hyRes
    have hxOuter := hinnerOuter hxInner
    have hyOuter := hinnerOuter hyInner
    have hcxG := (mem_residualNeighbors_iff.mp hxRes).1
    have hcyG := (mem_residualNeighbors_iff.mp hyRes).1
    have hcx : center ≠ x := hcxG.ne
    have hcy : center ≠ y := hcyG.ne
    exact (card_le_card
      (BalancedBisection.ambientLinkCommonNeighborsIn_mono hresInner x y)).trans
        (htyp.ambientLinkCodegree_upper i hki hcx hcy hxy hcOuter hxOuter
          hyOuter hcxG hcyG hh codegree hcodegree)

/-- Backwards-compatible consequence using the full covered degree as a
coarser loss budget. -/
theorem IsIterationTypical.residualLink_degree_codegree_bounds
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A R : TripleSystemOn V}
    {p eta ξ : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W k G A p eta ξ h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hki : k.val ≤ i.val)
    (center : V)
    (hcOuter : center ∈ W.U i.castSucc)
    (hcInner : center ∉ W.U i.succ)
    (hresInner : residualNeighbors G R center ⊆ W.U i.succ)
    (m D codegree loss : ℕ)
    (hcovered : (coveredGraph R).degree center ≤ loss)
    (hh : 3 ≤ h)
    (hlower : (m + loss + 1 : ℝ≥0) ≤
      (1 - ξ) * (p ^ 2 * eta * (W.U i.succ).card))
    (hupper : (1 + ξ) * (p ^ 2 * eta * (W.U i.succ).card) ≤
      (D : ℝ≥0))
    (hcodegree : (1 + ξ) *
      (p ^ 3 * eta ^ 2 * (W.U i.succ).card) ≤ (codegree : ℝ≥0)) :
    (∀ x ∈ residualNeighbors G R center,
      m ≤ (ambientLinkNeighborsIn center A
        (residualNeighbors G R center) x).card ∧
      (ambientLinkNeighborsIn center A
        (residualNeighbors G R center) x).card ≤ D) ∧
    (∀ x ∈ residualNeighbors G R center,
      ∀ y ∈ residualNeighbors G R center, x ≠ y →
        (ambientLinkCommonNeighborsIn center A
          (residualNeighbors G R center) x y).card ≤ codegree) := by
  apply htyp.residualLink_degree_codegree_bounds_localized htri i hki center
    hcOuter hcInner hresInner m D codegree loss _ hh hlower hupper hcodegree
  calc
    ((coveredGraph R).neighborFinset center ∩ W.U i.succ).card ≤
        ((coveredGraph R).neighborFinset center).card :=
      card_le_card inter_subset_left
    _ = (coveredGraph R).degree center := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ loss := hcovered

end

end Erdos207
