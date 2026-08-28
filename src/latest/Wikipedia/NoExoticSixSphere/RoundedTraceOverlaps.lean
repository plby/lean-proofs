import Wikipedia.NoExoticSixSphere.RoundedTraceCoordinateChanges
import Wikipedia.NoExoticSixSphere.OpenOverlapCoordinates

/-!
# Smoothness of the actual nonempty trace overlaps

Each direction uses the constructed partial diffeomorphism between the
actual parameter spaces. Source and target membership follow from the exact
coordinate identities on the corresponding overlap, not from assumed
compatibility of the independently constructed atlases.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  [IsManifold (𝓡 n) ∞ M] {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem contMDiff_collarToCylinder : letI := collarChartedSpace A;
    letI := unchangedCylinderChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector n)) (ProductHalfSpace.model (Vector n)) ∞
      (OpenOverlap.map (collarPart A) (cylinderOnlyPart A)) := by
  let := collarChartedSpace A
  let := unchangedCylinderChartedSpace A
  apply (contMDiff_unchangedCylinder_iff_parameters A _).mpr
  exact OpenOverlap.contMDiff_coordinates (collarPart A) (cylinderOnlyPart A)
    (fun p ↦ ((collarHomeomorph A).symm p).val)
    (fun p ↦ (unchangedCylinderHomeomorph A p).val.val)
    A.tubeHeightCoordinates (contMDiff_collarParameters A)
    (fun p ↦ collarParameters_subset_source A ((collarHomeomorph A).symm p.val).property)
    (fun p ↦ cylinder_collar_coordinate_eq A
      (OpenOverlap.map (collarPart A) (cylinderOnlyPart A) p) p.val rfl)

theorem contMDiff_cylinderToCollar : letI := unchangedCylinderChartedSpace A;
    letI := collarChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector n)) (ProductHalfSpace.model (Vector n)) ∞
      (OpenOverlap.map (cylinderOnlyPart A) (collarPart A)) := by
  let := unchangedCylinderChartedSpace A
  let := collarChartedSpace A
  apply (contMDiff_collar_iff_parameters A _).mpr
  refine OpenOverlap.contMDiff_coordinates (cylinderOnlyPart A) (collarPart A)
    (fun p ↦ (unchangedCylinderHomeomorph A p).val.val)
    (fun p ↦ ((collarHomeomorph A).symm p).val)
    A.tubeHeightCoordinates.symm (contMDiff_unchangedCylinder_parameters A) ?_ ?_
  · intro p
    let q := OpenOverlap.map (cylinderOnlyPart A) (collarPart A) p
    change (unchangedCylinderHomeomorph A p.val).val.val ∈ A.tubeHeightCoordinates.target
    rw [cylinder_collar_coordinate_eq A p.val q rfl]
    exact A.tubeHeightCoordinates.map_source
      (collarParameters_subset_source A ((collarHomeomorph A).symm q).property)
  · intro p
    exact collar_cylinder_coordinate_eq A p.val
      (OpenOverlap.map (cylinderOnlyPart A) (collarPart A) p) rfl

omit [IsManifold (𝓡 n) ∞ M] in
theorem contMDiff_handleToCollar : letI := unchangedHandleChartedSpace A;
    letI := collarChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector n)) (ProductHalfSpace.model (Vector n)) ∞
      (OpenOverlap.map (handleOnlyPart A) (collarPart A)) := by
  let := unchangedHandleChartedSpace A
  let := collarChartedSpace A
  apply (contMDiff_collar_iff_parameters A _).mpr
  exact OpenOverlap.contMDiff_coordinates (handleOnlyPart A) (collarPart A)
    (fun p ↦ (unchangedHandleHomeomorph A p).val.val)
    (fun p ↦ ((collarHomeomorph A).symm p).val)
    (handleCollarChange A) (contMDiff_unchangedHandle_parameters A)
    (fun p ↦ handleCollarChange_source A p.val
      (OpenOverlap.map (handleOnlyPart A) (collarPart A) p) rfl)
    (fun p ↦ (handleCollarChange_apply A p.val
      (OpenOverlap.map (handleOnlyPart A) (collarPart A) p) rfl).symm)

omit [IsManifold (𝓡 n) ∞ M] in
theorem contMDiff_collarToHandle : letI := collarChartedSpace A;
    letI := unchangedHandleChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector n)) (ProductHalfSpace.model (Vector n)) ∞
      (OpenOverlap.map (collarPart A) (handleOnlyPart A)) := by
  let := collarChartedSpace A
  let := unchangedHandleChartedSpace A
  apply (contMDiff_unchangedHandle_iff_parameters A _).mpr
  exact OpenOverlap.contMDiff_coordinates (collarPart A) (handleOnlyPart A)
    (fun p ↦ ((collarHomeomorph A).symm p).val)
    (fun p ↦ (unchangedHandleHomeomorph A p).val.val)
    (handleCollarChange A).symm (contMDiff_collarParameters A)
    (fun p ↦ handleCollarChange_target A
      (OpenOverlap.map (collarPart A) (handleOnlyPart A) p) p.val rfl)
    (fun p ↦ (handleCollarChange_symm_apply A
      (OpenOverlap.map (collarPart A) (handleOnlyPart A) p) p.val rfl).symm)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
