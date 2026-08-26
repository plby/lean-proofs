import ErdosProblems.Erdos593.TripleSystem.Basic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Triple-system embeddings

The manuscript uses non-induced embeddings: vertices are injected and every
source hyperedge is carried onto a host hyperedge, while additional host edges
among the image vertices are allowed.
-/

namespace Erdos593

universe u v w x y z

namespace TripleSystem

/-- A non-induced embedding of one edge-indexed triple system into another. -/
structure Embedding {V : Type u} {E : Type v} {W : Type w} {D : Type x}
    (F : TripleSystem V E) (H : TripleSystem W D) where
  /-- Injective map on vertices. -/
  vertex : V ↪ W
  /-- Choice of host hyperedge for every source hyperedge. -/
  edge : E → D
  /-- The selected host edge is exactly the image of the source edge. -/
  map_edge : ∀ e, vertex '' F.edgeSet e = H.edgeSet (edge e)

namespace Embedding

variable {V : Type u} {E : Type v} {W : Type w} {D : Type x}
variable {X : Type y} {A : Type z}
variable {F : TripleSystem V E} {H : TripleSystem W D} {K : TripleSystem X A}

/-- The identity embedding. -/
def refl (F : TripleSystem V E) : F.Embedding F where
  vertex := Function.Embedding.refl V
  edge := id
  map_edge := by
    intro e
    ext x
    simp

/-- Composition of non-induced triple-system embeddings. -/
def trans (f : F.Embedding H) (g : H.Embedding K) : F.Embedding K where
  vertex := f.vertex.trans g.vertex
  edge := g.edge ∘ f.edge
  map_edge := by
    intro e
    change (fun x => g.vertex (f.vertex x)) '' F.edgeSet e =
      K.edgeSet (g.edge (f.edge e))
    rw [← Set.image_image, f.map_edge, g.map_edge]

/-- The induced map on edge indices is injective, even though this is not a
separate field of a non-induced embedding. -/
theorem edge_injective (f : F.Embedding H) : Function.Injective f.edge := by
  intro e e' h
  apply F.edgeSet_injective
  apply Set.image_injective.mpr f.vertex.injective
  rw [f.map_edge, f.map_edge, h]

end Embedding

end TripleSystem

end Erdos593
