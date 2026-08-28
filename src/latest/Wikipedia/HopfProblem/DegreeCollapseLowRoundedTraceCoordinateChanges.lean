import Wikipedia.HopfProblem.DegreeCollapseLowUnchangedCylinderAtlas
import Wikipedia.HopfProblem.DegreeCollapseLowUnchangedHandleAtlas
import Wikipedia.HopfProblem.DegreeCollapseLowRoundedCollarAtlas

/-!

# Exact coordinate changes between the actual trace pieces

Cylinder/collar coordinates are related by the original attaching tube.
On a handle/collar overlap, exclusion of the compact inner image puts the
handle point in the proved annulus. The exact collar formula then identifies
the native coordinates, without extending a closed-annulus identity outside
its proved domain.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel LowRoundedHandleCorner

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

theorem cylinder_collar_coordinate_eq (p : cylinderOnlyPart A) (q : collarPart A)
    (he : p.val = q.val) : (unchangedCylinderHomeomorph A p).val.val =
      A.tubeHeightCoordinates ((collarHomeomorph A).symm q).val := by
  apply (LowHeightCylinder.injective_heightCylinder d e)
  exact (unchangedCylinderHomeomorph_ambient A p).trans
    ((congrArg Subtype.val he).trans (collarHomeomorph_symm_ambient A q).symm)

theorem collar_cylinder_coordinate_eq (p : cylinderOnlyPart A) (q : collarPart A)
    (he : p.val = q.val) : ((collarHomeomorph A).symm q).val =
      A.tubeHeightCoordinates.symm (unchangedCylinderHomeomorph A p).val.val := by
  rw [cylinder_collar_coordinate_eq A p q he]
  exact (A.tubeHeightCoordinates.left_inv
    (collarParameters_subset_source A ((collarHomeomorph A).symm q).property)).symm

theorem handle_collar_inner_lt (p : handleOnlyPart A) (q : collarPart A)
    (he : p.val = q.val) :
    A.innerRadius < ‖(unchangedHandleHomeomorph A p).val.val.1‖ := by
  obtain ⟨hi, _⟩ := (mem_collarPart_iff A q.val).mp q.property
  by_contra hn
  have hx : (unchangedHandleHomeomorph A p).val.val.1 ∈
      closedBall (0 : Vector (d + 1)) A.innerRadius := by
    simpa only [mem_closedBall, dist_zero_right] using le_of_not_gt hn
  apply hi
  refine ⟨(unchangedHandleHomeomorph A p).val.val,
    ⟨hx, handleSuperlevel_transverse A (unchangedHandleHomeomorph A p).val⟩, ?_⟩
  exact (unchangedHandleHomeomorph_ambient A p).trans (congrArg Subtype.val he)

theorem handle_collar_mem_source (p : handleOnlyPart A) (q : collarPart A)
    (he : p.val = q.val) :
    (unchangedHandleHomeomorph A p).val.val ∈ A.collarCoordinates.source := by
  rw [A.collarCoordinates_source]
  refine ⟨?_, ?_⟩
  · intro hz
    have h := handle_collar_inner_lt A p q he
    rw [hz, norm_zero] at h
    exact (not_lt_of_ge A.innerRadius_pos.le) h
  · exact (closedBall_subset_ball (UnroundedTrace.handleRadius_lt A))
      (handleSuperlevel_transverse A (unchangedHandleHomeomorph A p).val)

theorem handle_collar_coordinate_eq (p : handleOnlyPart A) (q : collarPart A)
    (he : p.val = q.val) :
    A.collarCoordinates (unchangedHandleHomeomorph A p).val.val =
      A.tubeHeightCoordinates ((collarHomeomorph A).symm q).val := by
  apply (LowHeightCylinder.injective_heightCylinder d e)
  let z := unchangedHandleHomeomorph A p
  have hm := A.map_eq_cylinder_collarCoordinates
    (ball_subset_closedBall z.property.1) (handle_collar_inner_lt A p q he).le
    (handleSuperlevel_vector_mem A z.val)
  exact hm.symm.trans ((unchangedHandleHomeomorph_ambient A p).trans
    ((congrArg Subtype.val he).trans (collarHomeomorph_symm_ambient A q).symm))

def handleProductModelDiffeomorph : (Vector (d + 1) × Vector (7 - d)) ≃ₘ⟮
    𝓘(ℝ, Vector (d + 1) × Vector (7 - d)), (𝓡 (d + 1)).prod (𝓡 (7 - d))⟯
      (Vector (d + 1) × Vector (7 - d)) where
  toEquiv := Equiv.refl _
  contMDiff_toFun := contDiff_fst.contMDiff.prodMk contDiff_snd.contMDiff
  contMDiff_invFun := contMDiff_fst.prodMk_space contMDiff_snd

def handleCollarChange : PartialDiffeomorph
    𝓘(ℝ, Vector (d + 1) × Vector (7 - d)) (collarModel d (7 - d))
    (Vector (d + 1) × Vector (7 - d)) (Collar d (7 - d)) ∞ :=
  ((handleProductModelDiffeomorph (d := d)).toPartialDiffeomorph.trans A.collarCoordinates).trans
    A.tubeHeightCoordinates.symm

theorem handleCollarChange_source (p : handleOnlyPart A) (q : collarPart A)
    (he : p.val = q.val) :
    (unchangedHandleHomeomorph A p).val.val ∈ (handleCollarChange A).source := by
  refine ⟨⟨mem_univ _, handle_collar_mem_source A p q he⟩, ?_⟩
  change A.collarCoordinates (unchangedHandleHomeomorph A p).val.val ∈
    A.tubeHeightCoordinates.target
  rw [handle_collar_coordinate_eq A p q he]
  exact A.tubeHeightCoordinates.map_source
    (collarParameters_subset_source A ((collarHomeomorph A).symm q).property)

theorem handleCollarChange_apply (p : handleOnlyPart A) (q : collarPart A)
    (he : p.val = q.val) : handleCollarChange A (unchangedHandleHomeomorph A p).val.val =
      ((collarHomeomorph A).symm q).val := by
  change A.tubeHeightCoordinates.symm
    (A.collarCoordinates (unchangedHandleHomeomorph A p).val.val) = _
  rw [handle_collar_coordinate_eq A p q he]
  exact A.tubeHeightCoordinates.left_inv
    (collarParameters_subset_source A ((collarHomeomorph A).symm q).property)

theorem handleCollarChange_target (p : handleOnlyPart A) (q : collarPart A)
    (he : p.val = q.val) :
    ((collarHomeomorph A).symm q).val ∈ (handleCollarChange A).target := by
  rw [← handleCollarChange_apply A p q he]
  exact (handleCollarChange A).map_source (handleCollarChange_source A p q he)

theorem handleCollarChange_symm_apply (p : handleOnlyPart A) (q : collarPart A)
    (he : p.val = q.val) :
    (handleCollarChange A).symm ((collarHomeomorph A).symm q).val =
      (unchangedHandleHomeomorph A p).val.val := by
  rw [← handleCollarChange_apply A p q he]
  exact (handleCollarChange A).left_inv (handleCollarChange_source A p q he)

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace
