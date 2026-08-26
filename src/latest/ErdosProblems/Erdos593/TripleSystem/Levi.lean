import ErdosProblems.Erdos593.TripleSystem.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Levi graphs

The Levi graph of a triple system has point-nodes on the left and hyperedge-nodes
on the right, with adjacency given by incidence.
-/

namespace Erdos593

universe u v

namespace TripleSystem

variable {V : Type u} {E : Type v} (F : TripleSystem V E)

/-- Directed point-to-edge incidence before `SimpleGraph.fromRel` symmetrizes it. -/
def incidenceRel : V ⊕ E → V ⊕ E → Prop
  | .inl x, .inr e => F.Inc x e
  | _, _ => False

/-- The bipartite point-edge incidence graph of a triple system. -/
def levi : _root_.SimpleGraph (V ⊕ E) :=
  _root_.SimpleGraph.fromRel F.incidenceRel

@[simp]
theorem levi_adj_point_edge {x : V} {e : E} :
    F.levi.Adj (.inl x) (.inr e) ↔ F.Inc x e := by
  simp [levi, incidenceRel]

@[simp]
theorem levi_adj_edge_point {x : V} {e : E} :
    F.levi.Adj (.inr e) (.inl x) ↔ F.Inc x e := by
  simp [levi, incidenceRel]

@[simp]
theorem not_levi_adj_point_point {x y : V} :
    ¬F.levi.Adj (.inl x) (.inl y) := by
  simp [levi, incidenceRel]

@[simp]
theorem not_levi_adj_edge_edge {e f : E} :
    ¬F.levi.Adj (.inr e) (.inr f) := by
  simp [levi, incidenceRel]

/-- A Levi hyperedge-node has exactly the three point-neighbours incident with
the corresponding hyperedge. -/
-- ARISTOTLE_TARGET B2
theorem levi_edge_neighbor_ncard (e : E) :
    (F.levi.neighborSet (.inr e)).ncard = 3 := by
  rw [show F.levi.neighborSet (.inr e) =
    Set.image (fun x : V => Sum.inl x) {x : V | F.Inc x e} by
      ext x
      cases x <;> simp +decide]
  rw [Set.ncard_image_of_injective _ Sum.inl_injective]
  exact F.edgeSet_ncard e

end TripleSystem

end Erdos593
