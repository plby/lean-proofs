import Wikipedia.HopfProblem.SpecialPeriodsTriangleHorodisc
import Wikipedia.HopfProblem.SpecialPeriodsTriangleRegular
import Mathlib.Topology.LocallyFinite

/-!
# Local finiteness of the actual Ford translates

The Shimizu estimate and the primitive cusp stabilizer give a continuous
bound for the height of an entire triangle orbit.  Applied to inverse
translates of a compact set, this gives a single compact truncation of
the Ford polygon containing every possible returning point.  The proved
proper discontinuity then gives finiteness of the returning translates.
No tiling or fundamental-domain hypothesis is used.
-/

noncomputable section

open Set UpperHalfPlane
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

attribute [local instance] triangleGeometricAction
  triangleGeometricAction_properlyDiscontinuous

/-- All inverse translates of a compact set have uniformly bounded height. -/
theorem compact_return_height_bound {K : Set ℍ} (hK : IsCompact K) :
    ∃ hi : ℝ, ∀ (g : TriangleGroup) (z : ℍ),
      triangleGeometricRepresentation g z ∈ K → z.im ≤ hi := by
  obtain ⟨hi, hhi⟩ := hK.bddAbove_image orbitHeightBound_continuous.continuousOn
  refine ⟨hi, fun g z hz => ?_⟩
  have hb := triangle_im_le_orbitHeightBound g⁻¹ (triangleGeometricRepresentation g z)
  have he : triangleGeometricRepresentation g⁻¹ (triangleGeometricRepresentation g z) = z := by
    rw [map_inv]
    exact (triangleGeometricRepresentation g).symm_apply_apply z
  rw [he] at hb
  exact hb.trans (hhi ⟨_, hz, rfl⟩)

/-- A single compact Ford truncation contains all points that can be
translated into a fixed compact set. -/
theorem fordRegion_compact_return_truncation {K : Set ℍ} (hK : IsCompact K) :
    ∃ hi : ℝ, ∀ g : TriangleGroup,
      fordRegion ∩ triangleGeometricRepresentation g ⁻¹' K ⊆ truncatedFordRegion hi := by
  obtain ⟨hi, hhi⟩ := compact_return_height_bound hK
  exact ⟨hi, fun g z hz => ⟨hz.1, hhi g z hz.2⟩⟩

/-- Only finitely many actual Ford translates meet a compact subset of
the upper half-plane. -/
theorem fordRegion_translates_finite_inter_compact {K : Set ℍ} (hK : IsCompact K) :
    {g : TriangleGroup |
      (triangleGeometricRepresentation g '' fordRegion ∩ K).Nonempty}.Finite := by
  obtain ⟨hi, hhi⟩ := compact_return_height_bound hK
  have hf := finite_disjoint_inter_image (Γ := TriangleGroup)
    (truncatedFordRegion_compact hi) hK
  apply hf.subset
  rintro g ⟨z, ⟨w, hw, rfl⟩, hz⟩
  exact ⟨triangleGeometricRepresentation g w, ⟨w, ⟨hw, hhi g w hz⟩, rfl⟩, hz⟩

/-- The closed Ford polygons form an actual locally finite family. -/
theorem fordRegion_translates_locallyFinite :
    LocallyFinite (fun g : TriangleGroup => triangleGeometricRepresentation g '' fordRegion) := by
  intro z
  obtain ⟨K, hK, hKz⟩ := exists_compact_mem_nhds z
  exact ⟨K, hKz, fordRegion_translates_finite_inter_compact hK⟩

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
