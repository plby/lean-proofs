import Mathlib.Data.Set.Card

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Triple systems

An edge-indexed incidence representation of simple 3-uniform hypergraphs.  Edge
indices make the Levi graph live on the transparent sum type `V ⊕ E`, while the
external finiteness assumptions used by the structural theorem can be added as
typeclasses without changing the representation needed for later infinite hosts.
-/

namespace Erdos593

universe u v

/-- A simple 3-uniform hypergraph with vertex type `V` and edge-index type `E`. -/
structure TripleSystem (V : Type u) (E : Type v) where
  /-- Vertex-edge incidence. -/
  Inc : V → E → Prop
  /-- Every indexed edge contains exactly three vertices. -/
  edge_ncard : ∀ e, Set.ncard {x | Inc x e} = 3
  /-- Distinct edge indices determine distinct vertex sets. -/
  simple : Function.Injective (fun e => {x | Inc x e})

namespace TripleSystem

variable {V : Type u} {E : Type v} (F : TripleSystem V E)

/-- A point is isolated when it belongs to no hyperedge. -/
def IsIsolated (x : V) : Prop :=
  ∀ e, ¬F.Inc x e

/-- Any two distinct hyperedges of a linear triple system share at most one point. -/
def Linear : Prop :=
  ∀ ⦃e f : E⦄ ⦃x y : V⦄, e ≠ f →
    F.Inc x e → F.Inc x f → F.Inc y e → F.Inc y f → x = y

/-- An edge is represented extensionally by its set of incident vertices. -/
def edgeSet (e : E) : Set V :=
  {x | F.Inc x e}

@[simp]
theorem mem_edgeSet {x : V} {e : E} : x ∈ F.edgeSet e ↔ F.Inc x e :=
  Iff.rfl

theorem edgeSet_ncard (e : E) : (F.edgeSet e).ncard = 3 :=
  F.edge_ncard e

theorem edgeSet_injective : Function.Injective F.edgeSet :=
  F.simple

/-- Linearity can equivalently be stated as subsingleton intersection of every
pair of distinct edge sets. -/
-- ARISTOTLE_TARGET B1
theorem linear_iff_pairwise_inter_subsingleton :
    F.Linear ↔ ∀ ⦃e f : E⦄, e ≠ f →
      (F.edgeSet e ∩ F.edgeSet f).Subsingleton := by
  constructor
  · intro h e f hef x hx y hy
    exact h hef hx.1 hx.2 hy.1 hy.2
  · intro h e f x y hef hxe hxf hye hyf
    exact h hef ⟨hxe, hxf⟩ ⟨hye, hyf⟩

end TripleSystem

end Erdos593
