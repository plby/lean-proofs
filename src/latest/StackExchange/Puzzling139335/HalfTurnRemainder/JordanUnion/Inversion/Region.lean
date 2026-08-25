import StackExchange.Puzzling139335.JordanCurveRigidity
import Wikipedia.SchoenfliesTheorem.Inversion

/-!
# Jordan regions and inversion of arcs

The interior and complement of a closed Jordan region are the two regions of
its frontier.  Inversion about a point outside an arc preserves the arc and
its named endpoints.
-/

open Set

namespace Puzzling139335.IsJordanRegion

variable {A : Set Plane}

/-- The complement of a closed Jordan region is the outside of its frontier. -/
theorem compl_eq_outside_frontier (hA : IsJordanRegion A) :
    Aᶜ = Schoenflies.outside (frontier A) := by
  obtain ⟨C, hC, rfl⟩ := hA
  have hsep := Schoenflies.jordan_curve_theorem hC
  rw [frontier_closure_inside hsep, (Schoenflies.IsRegionOf.inside C).closure_eq hsep]
  ext x
  constructor
  · intro hx
    have hxC : x ∉ C := fun h => hx (Or.inr h)
    have hxregions : x ∈ Schoenflies.inside C ∪ Schoenflies.outside C := by
      rw [Schoenflies.inside_union_outside]
      exact hxC
    exact hxregions.resolve_left (fun h => hx (Or.inl h))
  · intro hx hxunion
    rcases hxunion with hxinside | hxC
    · exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hxinside hx
    · exact hx.1 hxC

end Puzzling139335.IsJordanRegion

namespace Schoenflies

/-- Inversion preserves an arc that avoids its center, including its named endpoints. -/
theorem IsArcBetween.invert_image {K : Set Plane} {p q a : Plane}
    (hK : IsArcBetween K p q) (ha : a ∉ K) :
    IsArcBetween (invert a '' K) (invert a p) (invert a q) := by
  obtain ⟨f, hf, hfi, hfK, hf0, hf1⟩ := hK
  have hmaps : MapsTo f unitInterval ({a}ᶜ : Set Plane) := by
    intro t ht
    exact (Set.subset_compl_singleton_iff.2 ha) (hfK ▸ mem_image_of_mem f ht)
  refine ⟨invert a ∘ f, (continuousOn_invert a).comp hf hmaps, ?_, ?_,
    by simp [hf0], by simp [hf1]⟩
  · intro s hs t ht hst
    exact hfi hs ht (invert_injective a hst)
  · rw [Set.image_comp, hfK]

end Schoenflies
