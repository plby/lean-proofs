import ErdosProblems.Erdos593.Graph.CompleteBipartite
import Mathlib.Combinatorics.SimpleGraph.Bipartite

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Coordinates of edges in a balanced complete bipartite graph

Every edge of `K_{n,n}` has a unique ordered pair of endpoints, one from each
distinguished part.  This module makes that representation explicit for the
universe-compatible atom used by the formalization.  It is the graph-level
API needed when a rainbow matrix is packaged as an embedding of a
private-vertex expansion.
-/

namespace Erdos593

universe u

namespace CompleteBipartiteEdges

/-- The left or right finite part of the universe-compatible `K_{n,n}`. -/
abbrev Part (n : Nat) := FiniteBipartitePart.{u} n

/-- The balanced graph whose edge coordinates are considered here. -/
abbrev Graph (n : Nat) := completeBipartiteNN.{u} n

/-- The canonical edge joining a left-part point to a right-part point. -/
def edge (n : Nat) (a b : Part n) : (Graph n).edgeSet :=
  ⟨s(Sum.inl a, Sum.inr b), by simp [Graph, completeBipartiteNN]⟩

/-- Extract the unique ordered left/right coordinates of an edge of
`K_{n,n}`. -/
noncomputable def coords (n : Nat) (e : (Graph n).edgeSet) : Part n × Part n := by
  classical
  let eVal : Sym2 (Part n ⊕ Part n) := e.1
  have he : eVal ∈ (_root_.completeBipartiteGraph (Part n) (Part n)).edgeSet := by
    exact e.2
  rw [SimpleGraph.edgeSet_completeBipartiteGraph] at he
  exact Classical.choose he

/-- The extracted coordinates reconstruct the underlying unordered edge. -/
theorem coords_spec (n : Nat) (e : (Graph n).edgeSet) :
    s(Sum.inl (coords n e).1, Sum.inr (coords n e).2) = e.1 := by
  classical
  let eVal : Sym2 (Part n ⊕ Part n) := e.1
  have he : eVal ∈ Set.range
      (fun x : Part n × Part n => s(Sum.inl x.1, Sum.inr x.2)) := by
    have he' : eVal ∈ (_root_.completeBipartiteGraph (Part n) (Part n)).edgeSet := by
      exact e.2
    rw [SimpleGraph.edgeSet_completeBipartiteGraph] at he'
    exact he'
  change s(Sum.inl (coords n e).1, Sum.inr (coords n e).2) = eVal
  unfold coords
  exact Classical.choose_spec he

/-- Rebuilding an edge from its extracted coordinates is the identity. -/
theorem edge_coords (n : Nat) (e : (Graph n).edgeSet) :
    edge n (coords n e).1 (coords n e).2 = e := by
  apply Subtype.ext
  exact coords_spec n e

/-- Coordinate extraction is injective on the edges of `K_{n,n}`. -/
theorem coords_injective (n : Nat) : Function.Injective (coords n) := by
  intro e f hef
  apply Subtype.ext
  calc
    e.1 = s(Sum.inl (coords n e).1, Sum.inr (coords n e).2) :=
      (coords_spec n e).symm
    _ = s(Sum.inl (coords n f).1, Sum.inr (coords n f).2) := by rw [hef]
    _ = f.1 := coords_spec n f

/-- The canonical left/right edge constructor is injective. -/
theorem edge_injective (n : Nat) :
    Function.Injective (fun ab : Part n × Part n => edge n ab.1 ab.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h' := congrArg Subtype.val h
  rcases Sym2.eq_iff.mp h' with h' | h'
  · exact Prod.ext (Sum.inl.inj h'.1) (Sum.inr.inj h'.2)
  · simp at h'

/-- Extracting coordinates from a canonical cross edge returns the original
ordered pair. -/
theorem coords_edge (n : Nat) (a b : Part n) :
    coords n (edge n a b) = (a, b) := by
  apply edge_injective n
  change edge n (coords n (edge n a b)).1 (coords n (edge n a b)).2 =
    edge n a b
  exact edge_coords n (edge n a b)

end CompleteBipartiteEdges
end Erdos593
