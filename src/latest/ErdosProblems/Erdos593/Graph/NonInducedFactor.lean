import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Non-induced graph factors

The finite-trace reconstruction only needs a graph `J` to occur inside an
ambient graph `G` through an injective vertex map that preserves edges.  It
does *not* need the map to reflect adjacency: `G` may have additional edges
between vertices of the image.  This file makes that distinction explicit,
instead of using `J ↪g G`, whose induced-embedding condition is too strong.

Mathlib calls the same notion a `SimpleGraph.Copy`; the wrapper below keeps
the two proof obligations visible at finite-trace interfaces and provides the
standard conversion to the library API when an isomorphic image subgraph is
needed.
-/

namespace Erdos593

universe u v w

namespace SimpleGraph

variable {X : Type u} {V : Type v} {W : Type w}
variable {J : _root_.SimpleGraph X} {G : _root_.SimpleGraph V}
variable {H : _root_.SimpleGraph W}

/-- A non-induced factor map from `J` into `G`: vertices are injected and
source edges are preserved.  No adjacency-reflection condition is imposed. -/
structure NonInducedFactor (J : _root_.SimpleGraph X) (G : _root_.SimpleGraph V) where
  /-- The injective vertex map. -/
  vertex : X ↪ V
  /-- Every source edge maps to a host edge. -/
  map_adj : ∀ {x y : X}, J.Adj x y → G.Adj (vertex x) (vertex y)

namespace NonInducedFactor

/-- Regard a non-induced factor as an adjacency-preserving graph homomorphism. -/
def toHom (f : NonInducedFactor J G) : J →g G where
  toFun := f.vertex
  map_rel' := f.map_adj

@[simp]
theorem toHom_apply (f : NonInducedFactor J G) (x : X) : f.toHom x = f.vertex x := rfl

/-- Convert to Mathlib's non-induced copy interface. -/
def toCopy (f : NonInducedFactor J G) : _root_.SimpleGraph.Copy J G where
  toHom := f.toHom
  injective' := f.vertex.injective

@[simp]
theorem toCopy_apply (f : NonInducedFactor J G) (x : X) : f.toCopy x = f.vertex x := rfl

/-- Build a non-induced factor from Mathlib's non-induced copy interface. -/
def ofCopy (f : _root_.SimpleGraph.Copy J G) : NonInducedFactor J G where
  vertex := f.toEmbedding
  map_adj := f.toHom.map_adj

@[simp]
theorem ofCopy_vertex (f : _root_.SimpleGraph.Copy J G) (x : X) :
    (ofCopy f).vertex x = f x := rfl

/-- The identity non-induced factor. -/
def refl (G : _root_.SimpleGraph V) : NonInducedFactor G G where
  vertex := Function.Embedding.refl V
  map_adj := fun hxy => hxy

@[simp]
theorem refl_vertex (G : _root_.SimpleGraph V) (x : V) : (refl G).vertex x = x := rfl

/-- Compose non-induced factor maps. -/
def trans (f : NonInducedFactor J G) (g : NonInducedFactor G H) :
    NonInducedFactor J H where
  vertex := f.vertex.trans g.vertex
  map_adj := fun hxy => g.map_adj (f.map_adj hxy)

@[simp]
theorem trans_vertex (f : NonInducedFactor J G) (g : NonInducedFactor G H) (x : X) :
    (f.trans g).vertex x = g.vertex (f.vertex x) := rfl

/-- Edge-set transport under a non-induced factor map. -/
theorem map_mem_edgeSet (f : NonInducedFactor J G) {e : Sym2 X}
    (he : e ∈ J.edgeSet) : e.map f.vertex ∈ G.edgeSet :=
  f.toHom.map_mem_edgeSet he

/-- Transport a walk along a non-induced factor map. -/
def mapWalk (f : NonInducedFactor J G) {x y : X} (w : J.Walk x y) :
    G.Walk (f.vertex x) (f.vertex y) :=
  w.map f.toHom

@[simp]
theorem mapWalk_length (f : NonInducedFactor J G) {x y : X} (w : J.Walk x y) :
    (f.mapWalk w).length = w.length := by
  exact _root_.SimpleGraph.Walk.length_map f.toHom w

/-- The (possibly non-induced) image subgraph selected by a factor map.  It
contains exactly the transported source edges; it is not the induced subgraph
of `G` on the vertex image. -/
abbrev imageSubgraph (f : NonInducedFactor J G) : G.Subgraph := f.toCopy.toSubgraph

/-- A factor map identifies its source with its selected image subgraph. -/
noncomputable def isoToImageSubgraph (f : NonInducedFactor J G) :
    J ≃g f.imageSubgraph.coe :=
  f.toCopy.isoToSubgraph

end NonInducedFactor

end SimpleGraph

end Erdos593
