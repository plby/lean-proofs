import Wikipedia.NoExoticSixSphere.CompactAdjunctionTopology

/-!
# Gluing continuous maps on the actual compact adjunction space

Maps on the original space and the attached target descend precisely
when they agree on the attaching domain. The resulting map is checked
on both original parts, using the actual quotient presentation.
-/

noncomputable section

universe u v

open Set Topology

namespace NoExoticSixSphere.CompactAdjunction

variable {A X Y : Type u} {Z : Type v}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (D : Data A X Y) (F : C(X, Z)) (G : C(Y, Z))
    (h : ∀ a, F (D.embedding a) = G (D.attaching a))

def glueFunction : Space D → Z
  | Sum.inl x => F x.val
  | Sum.inr y => G y

include h in
theorem glueFunction_projection (x : X) : glueFunction D F G (projection D x) = F x := by
  by_cases hx : x ∈ Set.range D.embedding
  · obtain ⟨a, rfl⟩ := hx
    rw [projection_embedding]
    exact (h a).symm
  · rw [projection_of_notMem D x hx]
    rfl

include h in
theorem continuous_glueFunction : Continuous (glueFunction D F G) := by
  apply (projection_isQuotientMap D).continuous_iff.mpr
  exact F.continuous.congr (fun x ↦ (glueFunction_projection D F G h x).symm)

def glue : C(Space D, Z) := ⟨glueFunction D F G, continuous_glueFunction D F G h⟩

theorem glue_quotientMap (x : X) : glue D F G h (quotientMap D x) = F x :=
  glueFunction_projection D F G h x

theorem glue_inclusion [CompactSpace A] [T2Space Y] (y : Y) :
    glue D F G h (inclusion D y) = G y := rfl

end NoExoticSixSphere.CompactAdjunction
