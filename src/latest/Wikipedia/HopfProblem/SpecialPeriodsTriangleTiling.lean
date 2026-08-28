import Wikipedia.HopfProblem.SpecialPeriodsTriangleTilingFord
import Wikipedia.HopfProblem.SpecialPeriodsTriangleTilingHalf
import Wikipedia.HopfProblem.SpecialPeriodsTriangleTilingLocalFinite

/-!
# A genuine locally finite tiling by the source reflection triangles

The tiles are actual images of the closed half-Ford triangle under a
triangle transformation, optionally preceded by the vertical reflection.
They cover the upper half-plane, have pairwise disjoint topological
interiors, and form a locally finite closed family.  The base interior is
exactly the complex domain used for the normalized Riemann map.

This establishes the geometric tiling and side-pairing input.  It does
not assume or claim the boundary extension of a Riemann map, or the
global uniformization obtained after that analytic gluing step.
-/

noncomputable section

open Set UpperHalfPlane
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The two orientation choices after an actual triangle transformation. -/
def halfTriangleMap (i : TriangleGroup × Bool) : ℍ ≃ₜ ℍ :=
  (halfFold i.2).trans (triangleGeometricBiholomorph i.1).toHomeomorph

@[simp] theorem halfTriangleMap_apply (i : TriangleGroup × Bool) (z : ℍ) :
    halfTriangleMap i z = triangleGeometricRepresentation i.1 (halfFold i.2 z) := rfl

/-- A closed reflected half-Ford triangle in the actual upper half-plane. -/
def halfTriangleTile (i : TriangleGroup × Bool) : Set ℍ :=
  halfTriangleMap i '' halfFordRegion

/-- The corresponding open triangle. -/
def halfTriangleOpenTile (i : TriangleGroup × Bool) : Set ℍ :=
  halfTriangleMap i '' halfFordInterior

theorem halfTriangleTile_eq (i : TriangleGroup × Bool) :
    halfTriangleTile i =
      triangleGeometricRepresentation i.1 '' (halfFold i.2 '' halfFordRegion) := by
  rw [Set.image_image]
  rfl

theorem halfTriangleOpenTile_eq (i : TriangleGroup × Bool) :
    halfTriangleOpenTile i =
      triangleGeometricRepresentation i.1 '' (halfFold i.2 '' halfFordInterior) := by
  rw [Set.image_image]
  rfl

theorem halfTriangleTile_isClosed (i : TriangleGroup × Bool) : IsClosed (halfTriangleTile i) :=
  (halfTriangleMap i).isClosedMap halfFordRegion halfFordRegion_isClosed

theorem halfTriangleOpenTile_isOpen (i : TriangleGroup × Bool) :
    IsOpen (halfTriangleOpenTile i) :=
  (halfTriangleMap i).isOpenMap halfFordInterior halfFordInterior_isOpen

/-- The open tiles are the full topological interiors of the closed tiles. -/
theorem interior_halfTriangleTile (i : TriangleGroup × Bool) :
    interior (halfTriangleTile i) = halfTriangleOpenTile i := by
  change interior (halfTriangleMap i '' halfFordRegion) =
    halfTriangleMap i '' halfFordInterior
  rw [← (halfTriangleMap i).image_interior, interior_halfFordRegion]

theorem halfTriangleTile_subset_fordRegion_translate (i : TriangleGroup × Bool) :
    halfTriangleTile i ⊆ triangleGeometricRepresentation i.1 '' fordRegion := by
  rw [halfTriangleTile_eq]
  exact image_mono (halfFold_image_region_subset i.2)

theorem halfTriangleOpenTile_subset_fordInterior_translate (i : TriangleGroup × Bool) :
    halfTriangleOpenTile i ⊆ triangleGeometricRepresentation i.1 '' fordInterior := by
  rw [halfTriangleOpenTile_eq]
  exact image_mono (halfFold_image_interior_subset i.2)

/-- These are all the actual translates of the two reflected halves,
and they cover the whole upper half-plane. -/
theorem halfTriangleTiles_cover :
    (⋃ i : TriangleGroup × Bool, halfTriangleTile i) = univ := by
  apply eq_univ_of_forall
  intro z
  obtain ⟨w, hw, g, hgz⟩ := triangle_exists_fordRegion_preimage z
  have hfold : w ∈ ⋃ b : Bool, halfFold b '' halfFordRegion := by
    rw [halfFold_closed_cover]
    exact hw
  obtain ⟨b, u, hu, hwu⟩ := mem_iUnion.mp hfold
  refine mem_iUnion.mpr ⟨(g, b), u, hu, ?_⟩
  rw [halfTriangleMap_apply, hwu, hgz]

/-- Distinct indexed reflection triangles have disjoint open interiors. -/
theorem halfTriangleOpenTiles_pairwiseDisjoint :
    Pairwise fun i j : TriangleGroup × Bool =>
      Disjoint (halfTriangleOpenTile i) (halfTriangleOpenTile j) := by
  rintro ⟨g, b⟩ ⟨h, c⟩ hne
  by_cases hgh : g = h
  · subst h
    have hbc : b ≠ c := fun hbc => hne (Prod.ext rfl hbc)
    rw [halfTriangleOpenTile_eq, halfTriangleOpenTile_eq]
    exact Set.disjoint_image_of_injective (triangleGeometricRepresentation g).injective
      (halfFold_images_disjoint b c hbc)
  · exact (fordInterior_translates_pairwiseDisjoint hgh).mono
      (halfTriangleOpenTile_subset_fordInterior_translate (g, b))
      (halfTriangleOpenTile_subset_fordInterior_translate (h, c))

theorem halfTriangleTiles_interiors_pairwiseDisjoint :
    Pairwise fun i j : TriangleGroup × Bool =>
      Disjoint (interior (halfTriangleTile i)) (interior (halfTriangleTile j)) := by
  intro i j hij
  rw [interior_halfTriangleTile, interior_halfTriangleTile]
  exact halfTriangleOpenTiles_pairwiseDisjoint hij

/-- Compact subsets meet only finitely many of the actual closed triangles. -/
theorem halfTriangleTiles_finite_inter_compact {K : Set ℍ} (hK : IsCompact K) :
    {i : TriangleGroup × Bool | (halfTriangleTile i ∩ K).Nonempty}.Finite := by
  apply ((fordRegion_translates_finite_inter_compact hK).prod
    (Set.finite_univ : (univ : Set Bool).Finite)).subset
  rintro i ⟨z, hz, hKz⟩
  exact ⟨⟨z, halfTriangleTile_subset_fordRegion_translate i hz, hKz⟩, mem_univ _⟩

/-- Local finiteness is proved for the constructed triangles themselves. -/
theorem halfTriangleTiles_locallyFinite : LocallyFinite halfTriangleTile := by
  intro z
  obtain ⟨K, hK, hKz⟩ := exists_compact_mem_nhds z
  exact ⟨K, hKz, halfTriangleTiles_finite_inter_compact hK⟩

/-- The geometric tiling package, with no supplied tiling assumptions. -/
theorem halfTriangleTiles_tiling :
    (⋃ i : TriangleGroup × Bool, halfTriangleTile i) = univ ∧
      (∀ i, IsClosed (halfTriangleTile i)) ∧
      LocallyFinite halfTriangleTile ∧
      Pairwise fun i j : TriangleGroup × Bool =>
        Disjoint (interior (halfTriangleTile i)) (interior (halfTriangleTile j)) :=
  ⟨halfTriangleTiles_cover, halfTriangleTile_isClosed,
    halfTriangleTiles_locallyFinite, halfTriangleTiles_interiors_pairwiseDisjoint⟩

/-- A function continuous on every actual closed triangle is continuous
globally.  This is available for the later reflected analytic branches. -/
theorem continuous_of_continuousOn_halfTriangleTiles {Y : Type*} [TopologicalSpace Y]
    {f : ℍ → Y} (hf : ∀ i, ContinuousOn f (halfTriangleTile i)) : Continuous f :=
  halfTriangleTiles_locallyFinite.continuous halfTriangleTiles_cover halfTriangleTile_isClosed hf

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
