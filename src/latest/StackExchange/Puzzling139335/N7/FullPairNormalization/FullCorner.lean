import StackExchange.Puzzling139335.N7.FullPairNormalization

/-!
# Transporting a placed full corner

An intrinsic corner occurrence remains an occurrence after a square symmetry.
If its intrinsic type is full, the transported corner has exactly one owner.
-/

open Set

namespace Puzzling139335.N7.FullPairNormalization

/-- A placed intrinsic corner belongs to its piece after mapping the square. -/
theorem placed_intrinsic_mem_map (d : SquareDissection) {i j : Fin 4} {v : Plane}
    (hv : v ∈ N8.intrinsicPair d i)
    (f : Plane ≃ᵃⁱ[ℝ] Plane) (hfS : f '' unitSquare = unitSquare)
    (hf : f (d.placement i v) = corner j) :
    corner j ∈ (d.map f hfS).piece i := by
  obtain ⟨a, ha, hav⟩ := (N8.mem_intrinsicPair d i v).mp hv
  have hfa : f (corner a) = corner j := by
    simpa only [← hav, d.placement_intrinsicCorner] using hf
  exact ⟨corner a, ha, hfa⟩

/-- Full intrinsic types give uniquely owned corners in any square frame. -/
theorem corner_count_one_of_placed_full_type (d : SquareDissection)
    {i j : Fin 4} {v : Plane} (hv : v ∈ N8.intrinsicPair d i)
    (hfull : v ∈ N5.fullCornerTypes d)
    (f : Plane ≃ᵃⁱ[ℝ] Plane) (hfS : f '' unitSquare = unitSquare)
    (hf : f (d.placement i v) = corner j) :
    (d.map f hfS).cornerTileCount j = 1 := by
  obtain ⟨a, ha, hav⟩ := (N8.mem_intrinsicPair d i v).mp hv
  have hfa : f (corner a) = corner j := by
    simpa only [← hav, d.placement_intrinsicCorner] using hf
  rw [cornerTileCount_map_of_corner_image d f hfS hfa]
  apply N5.corner_count_one_of_unique_owner d ha
  apply N5.unique_corner_of_type_mem_full d
  rwa [hav]

end Puzzling139335.N7.FullPairNormalization
