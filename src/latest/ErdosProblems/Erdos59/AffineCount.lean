import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import ErdosProblems.Erdos59.AffinePolarity

/-!
# Counting and relabelling the affine polarity graph

This file packages the coordinate construction from `AffinePolarity` in the
standard finite-graph language used by the rest of the development.  In
particular, it records all cardinalities with `q = 2^(2a+1)`, relabels the
graph on `Fin (q^3)`, and converts the explicit labelled-cycle exclusions to
Mathlib's `CliqueFree` and `Free` predicates.
-/

open Finset Function

namespace Erdos59.AffineCount

noncomputable section

open AffinePolarity

/-- The order of the finite field in the affine construction. -/
abbrev q (a : ℕ) : ℕ := 2 ^ (2 * a + 1)

/-- Absolute points are exactly parametrized by two field coordinates. -/
def absolutePointEquiv (a : ℕ) :
    F a × F a ≃ {p : Point a // IsAbsolute p} :=
  absoluteEquiv a

/-- There are exactly `q²` absolute points. -/
theorem card_absolutePoints (a : ℕ) :
    Fintype.card {p : Point a // IsAbsolute p} = q a ^ 2 := by
  exact absolute_card a

/-- The affine polarity graph has `q³` vertices. -/
theorem card_polarityGraph_vertices (a : ℕ) :
    Fintype.card (Point a) = q a ^ 3 := by
  exact coord_card a

/-- Every point has one neighbor for each incident line, except that an
absolute point loses the loop corresponding to its polar line. -/
theorem polarityGraph_degree_eq (a : ℕ) (p : Point a) :
    (polarityGraph a).degree p =
      if IsAbsolute p then q a - 1 else q a := by
  exact polarityGraph_degree a p

/-- The exact number of (undirected) edges in the affine polarity graph. -/
theorem card_polarityGraph_edges (a : ℕ) :
    (polarityGraph a).edgeFinset.card = (q a ^ 4 - q a ^ 2) / 2 := by
  exact polarityGraph_edge_card a

/-- A coordinate-free relabelling of the affine graph on `Fin (q³)`. -/
def graph (a : ℕ) : SimpleGraph (Fin (q a ^ 3)) :=
  (polarityGraph a).overFin (card_polarityGraph_vertices a)

noncomputable instance graphAdjDecidable (a : ℕ) : DecidableRel (graph a).Adj :=
  Classical.decRel _

/-- Relabelling by `Fin (q³)` is a graph isomorphism. -/
def graphIso (a : ℕ) : polarityGraph a ≃g graph a :=
  (polarityGraph a).overFinIso (card_polarityGraph_vertices a)

/-- The exact edge count is unchanged by the relabelling. -/
theorem card_graph_edges (a : ℕ) :
    (graph a).edgeFinset.card = (q a ^ 4 - q a ^ 2) / 2 := by
  rw [← (graphIso a).card_edgeFinset_eq]
  exact card_polarityGraph_edges a

/-- The degree formula on the relabelled graph. -/
theorem graph_degree_eq (a : ℕ) (v : Fin (q a ^ 3)) :
    (graph a).degree v =
      if IsAbsolute ((graphIso a).symm v) then q a - 1 else q a := by
  calc
    (graph a).degree v =
        (polarityGraph a).degree ((graphIso a).symm v) := by
      convert (graphIso a).degree_eq ((graphIso a).symm v) using 1
      simp
    _ = if IsAbsolute ((graphIso a).symm v) then q a - 1 else q a :=
      polarityGraph_degree_eq a _

/-- An explicit exclusion of labelled triangles implies Mathlib's
`CliqueFree 3` predicate. -/
theorem cliqueFree_three_of_no_C3 {V : Type*} {G : SimpleGraph V}
    (hG : ¬ ∃ v₀ v₁ v₂, IsC3 G v₀ v₁ v₂) : G.CliqueFree 3 := by
  by_contra h
  let f := SimpleGraph.topEmbeddingOfNotCliqueFree h
  apply hG
  refine ⟨f 0, f 1, f 2, f.injective.ne (by decide),
    f.injective.ne (by decide), f.injective.ne (by decide), ?_, ?_, ?_⟩
  · exact f.toHom.map_adj (by simp)
  · exact f.toHom.map_adj (by simp)
  · exact f.toHom.map_adj (by simp)

/-- An explicit exclusion of labelled simple hexagons implies that the graph
contains no copy of Mathlib's six-cycle. -/
theorem cycleGraph_six_free_of_no_C6 {V : Type*} {G : SimpleGraph V}
    (hG : ¬ ∃ v₀ v₁ v₂ v₃ v₄ v₅,
      IsC6 G v₀ v₁ v₂ v₃ v₄ v₅) :
    (SimpleGraph.cycleGraph 6).Free G := by
  rintro ⟨f⟩
  apply hG
  refine ⟨f 0, f 1, f 2, f 3, f 4, f 5,
    f.injective.ne (by decide), f.injective.ne (by decide),
    f.injective.ne (by decide), f.injective.ne (by decide),
    f.injective.ne (by decide), f.injective.ne (by decide),
    f.injective.ne (by decide), f.injective.ne (by decide),
    f.injective.ne (by decide), f.injective.ne (by decide),
    f.injective.ne (by decide), f.injective.ne (by decide),
    f.injective.ne (by decide), f.injective.ne (by decide),
    f.injective.ne (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals exact f.toHom.map_adj (by decide)

/-- The coordinate polarity graph is triangle-free in Mathlib's standard
sense. -/
theorem polarityGraph_cliqueFree_three (a : ℕ) :
    (polarityGraph a).CliqueFree 3 :=
  cliqueFree_three_of_no_C3 (polarityGraph_no_C3 a)

/-- The coordinate polarity graph is free of Mathlib's six-cycle. -/
theorem polarityGraph_cycleGraph_six_free (a : ℕ) :
    (SimpleGraph.cycleGraph 6).Free (polarityGraph a) :=
  cycleGraph_six_free_of_no_C6 (polarityGraph_no_C6 a)

/-- Triangle-freeness transfers to the graph on `Fin (q³)`. -/
theorem graph_cliqueFree_three (a : ℕ) : (graph a).CliqueFree 3 :=
  (polarityGraph_cliqueFree_three a).comap
    (graphIso a).symm.toEmbedding.isContained

/-- Six-cycle-freeness transfers to the graph on `Fin (q³)`. -/
theorem graph_cycleGraph_six_free (a : ℕ) :
    (SimpleGraph.cycleGraph 6).Free (graph a) :=
  (SimpleGraph.free_congr_right (graphIso a)).mp
    (polarityGraph_cycleGraph_six_free a)

end

end Erdos59.AffineCount
