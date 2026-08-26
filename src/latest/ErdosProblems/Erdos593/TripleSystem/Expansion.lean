import ErdosProblems.Erdos593.TripleSystem.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Private-vertex expansions

The private-vertex expansion of a simple graph `G` has one core point for each
vertex of `G`, one private point for each edge of `G`, and one triple for each
edge.  The triple indexed by `e` consists of the two ends of `e` together with
its private point.

No finiteness or decidable-equality hypothesis is needed for this construction.
-/

namespace Erdos593

universe u

namespace TripleSystem

namespace PrivateVertexExpansion

variable {V : Type u} (G : _root_.SimpleGraph V)

/-- The old graph vertices, viewed as the core-vertex type of the expansion. -/
abbrev CoreVertex (_G : _root_.SimpleGraph V) := V

/-- One private vertex for each graph edge. -/
abbrev PrivateVertex := G.edgeSet

/-- The point type of the private-vertex expansion. -/
abbrev Point := CoreVertex G ⊕ PrivateVertex G

/-- Hyperedges of the expansion are indexed by the edges of the original graph. -/
abbrev Edge := G.edgeSet

/-- Include a graph vertex as a core point of the expansion. -/
def core (x : CoreVertex G) : Point G :=
  .inl x

/-- The private point belonging to a graph edge. -/
def privateVertex (e : PrivateVertex G) : Point G :=
  .inr e

/-- Incidence in the expansion: core incidence is endpoint membership, while a
private point is incident only with the edge that indexes it. -/
def Inc (p : Point G) (e : Edge G) : Prop :=
  match p with
  | .inl x => x ∈ (e : Sym2 V)
  | .inr f => f = e

@[simp]
theorem inc_core (x : CoreVertex G) (e : Edge G) :
    Inc G (core G x) e ↔ x ∈ (e : Sym2 V) :=
  Iff.rfl

@[simp]
theorem inc_privateVertex (f : PrivateVertex G) (e : Edge G) :
    Inc G (privateVertex G f) e ↔ f = e :=
  Iff.rfl

/-- An expanded edge consists exactly of its two core endpoints and its private
point. -/
theorem incidenceSet_eq {x y : V} (he : s(x, y) ∈ G.edgeSet) :
    {p : Point G | Inc G p ⟨s(x, y), he⟩} =
      {core G x, core G y, privateVertex G ⟨s(x, y), he⟩} := by
  ext p
  rcases p with z | f <;> simp [Inc, core, privateVertex]

theorem incidenceSet_ncard (e : Edge G) :
    Set.ncard {p : Point G | Inc G p e} = 3 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : x ≠ y := (show G.Adj x y from he).ne
      rw [incidenceSet_eq G he]
      exact Set.ncard_eq_three.mpr
        ⟨core G x, core G y, privateVertex G ⟨s(x, y), he⟩,
          by simpa [core] using! hxy, by simp [core, privateVertex],
          by simp [core, privateVertex], rfl⟩

theorem incidenceSet_injective :
    Function.Injective (fun e : Edge G => {p : Point G | Inc G p e}) := by
  intro e f hef
  have h := Set.ext_iff.mp hef (privateVertex G e)
  simpa [Inc, privateVertex] using! h

end PrivateVertexExpansion

/-- The private-vertex expansion of a simple graph as an edge-indexed simple
3-uniform triple system. -/
def privateVertexExpansion (G : _root_.SimpleGraph V) :
    TripleSystem (PrivateVertexExpansion.Point G) (PrivateVertexExpansion.Edge G) where
  Inc := PrivateVertexExpansion.Inc G
  edge_ncard := PrivateVertexExpansion.incidenceSet_ncard G
  simple := PrivateVertexExpansion.incidenceSet_injective G

@[simp]
theorem privateVertexExpansion_inc_core
    (G : _root_.SimpleGraph V) (x : PrivateVertexExpansion.CoreVertex G)
    (e : PrivateVertexExpansion.Edge G) :
    (privateVertexExpansion G).Inc (PrivateVertexExpansion.core G x) e ↔
      x ∈ (e : Sym2 V) :=
  Iff.rfl

@[simp]
theorem privateVertexExpansion_inc_privateVertex
    (G : _root_.SimpleGraph V) (f : PrivateVertexExpansion.PrivateVertex G)
    (e : PrivateVertexExpansion.Edge G) :
    (privateVertexExpansion G).Inc (PrivateVertexExpansion.privateVertex G f) e ↔
      f = e :=
  Iff.rfl

end TripleSystem

end Erdos593
