import Wikipedia.HopfProblem.ToricComponentTopology
import Wikipedia.HopfProblem.ToricSimplyConnected

/-!
# Simple connectivity of the actual toric ray surfaces

Every ray surface has its original affine two-space charts.  In one chart,
the preimage of a second chart is open and contains the dense coordinate
torus.  It is therefore connected, and local path connectedness of complex
two-space makes it path connected.  These are the actual intersections
needed to apply the proved open-cover simple-connectivity theorem.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.ConstantSheafFirstCohomology.ToricTopology

open ToricCharts ToricFan ToricSpace ToricComponent

variable {v : Fin 2 → ℤ}

/-- The inverse image of one affine chart in another is open in the
original complex two-space coordinates. -/
theorem affineIntersectionPreimage_isOpen (c d : ChartIndex v) :
    IsOpen (affineInclusion c ⁻¹' range (affineInclusion d)) :=
  (affineInclusion_openEmbedding d).isOpen_range.preimage
    (affineInclusion_openEmbedding c).continuous

/-- The coordinate torus lies in every genuine overlap. -/
theorem torus_subset_affineIntersectionPreimage (c d : ChartIndex v) :
    torus ⊆ affineInclusion c ⁻¹' range (affineInclusion d) :=
  fun _ hz => affineInclusion_torus_mem_range c d hz

/-- Genuine chart-overlap preimages are path connected; no description of
the component as an abstract toric surface is assumed. -/
theorem affineIntersectionPreimage_isPathConnected (c d : ChartIndex v) :
    IsPathConnected (affineInclusion c ⁻¹' range (affineInclusion d)) := by
  apply (affineIntersectionPreimage_isOpen c d).isConnected_iff_isPathConnected.mp
  exact torus_isPathConnected.isConnected.subset_closure
    (torus_subset_affineIntersectionPreimage c d) (fun z _ => torus_dense z)

/-- The actual affine-chart intersections in the ray surface are path
connected. -/
theorem affineInclusion_ranges_inter_isPathConnected (c d : ChartIndex v) :
    IsPathConnected (range (affineInclusion c) ∩ range (affineInclusion d)) := by
  rw [← image_preimage_eq_range_inter]
  exact (affineIntersectionPreimage_isPathConnected c d).image
    (affineInclusion_openEmbedding c).continuous

/-- Each original affine chart is simply connected because its model is
the contractible vector space ℂ². -/
theorem affineInclusion_range_isSimplyConnected (c : ChartIndex v) :
    IsSimplyConnected (range (affineInclusion c)) := by
  rw [← image_univ]
  apply (affineInclusion_openEmbedding c).isEmbedding.isSimplyConnected_image.mpr
  change SimplyConnectedSpace (univ : Set (CoordinateSpace 2))
  let := (convex_univ : Convex ℝ (univ : Set (CoordinateSpace 2))).contractibleSpace
    univ_nonempty
  infer_instance

/-- Every actual ray surface is simply connected in its original subspace
topology. -/
theorem rayDivisor_simplyConnectedSpace (v : Fin 2 → ℤ) :
    SimplyConnectedSpace (rayDivisor v) := by
  apply simplyConnectedSpace_of_open_cover
    (fun c : ChartIndex v => range (affineInclusion c))
    (fun c => (affineInclusion_openEmbedding c).isOpen_range)
    (affineInclusions_cover v) affineInclusion_range_isSimplyConnected
    (affineInclusion (baseChart v) (fun _ => 1)) ?_
    affineInclusion_ranges_inter_isPathConnected
  intro c
  exact affineInclusion_torus_mem_range (baseChart v) c (fun _ => one_ne_zero)

/-- Local path connectedness follows from the existing native affine
complex two-manifold atlas. -/
theorem rayDivisor_locallyPathConnectedSpace (v : Fin 2 → ℤ) :
    LocallyPathConnectedSpace (rayDivisor v) :=
  ChartedSpace.locallyPathConnectedSpace (CoordinateSpace 2) (rayDivisor v)

end Wikipedia.HopfProblem.ConstantSheafFirstCohomology.ToricTopology
