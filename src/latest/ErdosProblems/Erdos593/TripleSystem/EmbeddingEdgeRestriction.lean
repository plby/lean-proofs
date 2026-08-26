import ErdosProblems.Erdos593.TripleSystem.EdgeRestriction
import ErdosProblems.Erdos593.TripleSystem.Isolated
import ErdosProblems.Erdos593.TripleSystem.Isomorph
import ErdosProblems.Erdos593.TripleSystem.IsomorphIntrinsic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact edge restrictions of embeddings

An embedding need not be induced, but it is an isomorphism onto the
restriction formed by the host-edge indices it explicitly selects, provided
the source has no isolated vertices.  This is the first exact bridge from a
finite linear source to a finite linear host-edge restriction.
-/

namespace Erdos593

universe u v w x

namespace TripleSystem

namespace Embedding

variable {V : Type u} {E : Type v} {W : Type w} {D : Type x}
variable {F : TripleSystem V E} {H : TripleSystem W D}

/-- The host edge indices selected by an embedding. -/
def edgeImage (f : F.Embedding H) : Set D := Set.range f.edge

/-- The embedding identifies the source edge-index type with its image. -/
noncomputable def edgeImageEdgeEquiv (f : F.Embedding H) : E ≃ f.edgeImage :=
  Equiv.ofBijective (fun e => ⟨f.edge e, ⟨e, rfl⟩⟩) (by
    constructor
    · intro e e' h
      exact f.edge_injective (congrArg Subtype.val h)
    · intro d
      rcases d.property with ⟨e, he⟩
      refine ⟨e, ?_⟩
      exact Subtype.ext he)

/-- If the source has no isolated points, its vertices identify with the
support of the selected host edges. -/
noncomputable def edgeImageVertexEquiv (f : F.Embedding H)
    (hF : F.HasNoIsolatedPoints) : V ≃ H.EdgeSupport f.edgeImage := by
  let phi : V → H.EdgeSupport f.edgeImage := fun x =>
    ⟨f.vertex x, by
      rcases F.not_isolated_iff_exists_inc.mp (hF x) with ⟨e, hxe⟩
      change ∃ d : D, d ∈ f.edgeImage ∧ H.Inc (f.vertex x) d
      refine ⟨f.edge e, ⟨e, rfl⟩, ?_⟩
      have hset := Set.ext_iff.mp (f.map_edge e) (f.vertex x)
      exact hset.mp ⟨x, hxe, rfl⟩⟩
  apply Equiv.ofBijective phi
  constructor
  · intro x y hxy
    exact f.vertex.injective (congrArg Subtype.val hxy)
  · intro y
    rcases y.property with ⟨d, ⟨e, rfl⟩, hye⟩
    have hset := Set.ext_iff.mp (f.map_edge e) y.1
    rcases hset.mpr hye with ⟨x, hxe, hxy⟩
    refine ⟨x, ?_⟩
    exact Subtype.ext hxy

/-- An embedding is an isomorphism onto the exact restriction to its selected
host edges, once isolated source vertices have been removed. -/
noncomputable def imageEdgeRestrictionIso (f : F.Embedding H)
    (hF : F.HasNoIsolatedPoints) :
    Iso F (H.edgeRestriction f.edgeImage) where
  vertexEquiv := f.edgeImageVertexEquiv hF
  edgeEquiv := f.edgeImageEdgeEquiv
  map_inc_iff := by
    intro x e
    change F.Inc x e ↔ H.Inc (f.vertex x) (f.edge e)
    have hset := Set.ext_iff.mp (f.map_edge e) (f.vertex x)
    constructor
    · intro hxe
      exact hset.mp ⟨x, hxe, rfl⟩
    · intro hxe
      rcases hset.mpr hxe with ⟨y, hye, hyx⟩
      have hyx' : y = x := f.vertex.injective hyx
      simpa [hyx'] using! hye

/-- Exact edge restrictions preserve linearity along embeddings. -/
theorem imageEdgeRestriction_linear (f : F.Embedding H)
    (hF : F.HasNoIsolatedPoints) (hlinear : F.Linear) :
    (H.edgeRestriction f.edgeImage).Linear :=
  (f.imageEdgeRestrictionIso hF).linear_iff.mp hlinear

end Embedding

end TripleSystem

end Erdos593
