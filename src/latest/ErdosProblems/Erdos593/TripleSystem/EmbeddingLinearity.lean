import ErdosProblems.Erdos593.TripleSystem.EmbeddingEdgeRestriction

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Linearity reflected by triple-system embeddings

Although triple-system embeddings are non-induced, they carry each source
edge exactly onto a selected target edge.  Consequently target linearity
reflects back to the source.
-/

namespace Erdos593

universe u v w x

namespace TripleSystem

namespace Embedding

variable {V : Type u} {E : Type v} {W : Type w} {D : Type x}
variable {F : TripleSystem V E} {H : TripleSystem W D}

/-- A non-induced embedding into a linear target has a linear source. -/
theorem source_linear_of_target_linear
    (f : F.Embedding H) (hlinear : H.Linear) : F.Linear := by
  intro e d x y hed hxe hxd hye hyd
  apply f.vertex.injective
  apply hlinear (f.edge_injective.ne hed)
  · have hset := Set.ext_iff.mp (f.map_edge e) (f.vertex x)
    exact hset.mp ⟨x, hxe, rfl⟩
  · have hset := Set.ext_iff.mp (f.map_edge d) (f.vertex x)
    exact hset.mp ⟨x, hxd, rfl⟩
  · have hset := Set.ext_iff.mp (f.map_edge e) (f.vertex y)
    exact hset.mp ⟨y, hye, rfl⟩
  · have hset := Set.ext_iff.mp (f.map_edge d) (f.vertex y)
    exact hset.mp ⟨y, hyd, rfl⟩

/-- It is enough for the exact restriction to the selected image edges to be
linear, provided the source has no isolated vertices. -/
theorem source_linear_of_imageEdgeRestriction_linear
    (f : F.Embedding H) (hF : F.HasNoIsolatedPoints)
    (hlinear : (H.edgeRestriction f.edgeImage).Linear) : F.Linear :=
  (f.imageEdgeRestrictionIso hF).linear_iff.mpr hlinear
end Embedding

end TripleSystem

end Erdos593
