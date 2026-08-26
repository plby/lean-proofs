import ErdosProblems.Erdos593.TripleSystem.Embedding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Canonical one-edge pieces

Hyperedge-nodes isolated after bridge deletion still contribute a one-edge
piece.  This module packages the edge as a triple system on its three incident
points and embeds that piece back into the ambient system.
-/

namespace Erdos593

universe u v

namespace TripleSystem

variable {V : Type u} {E : Type v} (F : TripleSystem V E)

/-- A universe-polymorphic singleton edge-index type.  Keeping this in the
vertex universe lets a one-edge piece participate in the universe-uniform
constructive class. -/
abbrev SingleEdgeIndex : Type u := ULift.{u} Unit

/-- The one-edge subsystem carried by a selected hyperedge. -/
def singleEdgePiece (e : E) :
    TripleSystem (F.edgeSet e) SingleEdgeIndex where
  Inc _ _ := True
  edge_ncard := by
    intro d
    rw [show {x : F.edgeSet e | True} =
        {x : F.edgeSet e | (x.1 : V) ∈ (Set.univ : Set V)} by simp]
    rw [Set.ncard_subtype]
    simpa using! F.edge_ncard e
  simple := by
    intro a b _
    exact Subsingleton.elim a b

/-- The canonical embedding of a one-edge subsystem into its ambient triple
system. -/
def singleEdgePieceEmbedding (e : E) : (F.singleEdgePiece e).Embedding F where
  vertex := ⟨Subtype.val, Subtype.val_injective⟩
  edge _ := e
  map_edge := by
    intro d
    cases d
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩

end TripleSystem
end Erdos593
