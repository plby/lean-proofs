import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedCollarAtlas
import Wikipedia.NoExoticSixSphere.SuperlevelDifferential
import Wikipedia.NoExoticSixSphere.OpenSubsetDifferential

/-!
# The actual tangent and normal spaces of the open rounded collar

Its parameter differential is bijective, including at boundary points.
Consequently the ambient inclusion is immersive and has the same tangent
image as the original smooth collar sheet. The prescribed sheet frame
therefore gives a smooth orthonormal frame of its actual normal bundle.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel SevenRoundedHandleCorner

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def collarParameterDerivative (p : collarPart A) :
    (ℝ × Vector 7) →L[ℝ] ((Vector 3 × Vector 4) × ℝ) := by
  let := collarChartedSpace A
  exact mfderiv (ProductHalfSpace.model (Vector 7)) collarModel
    (fun q : collarPart A ↦ ((collarHomeomorph A).symm q).val) p

theorem bijective_collarParameterDerivative (p : collarPart A) :
    Bijective (collarParameterDerivative A p) := by
  let := (collarLevelAtlas A).chartedSpace
  let := (collarLevelAtlas A).isManifold
  let := collarChartedSpace A
  let d := collarWindowDiffeomorph A
  have hd := (d.mfderivToContinuousLinearEquiv (by simp) p).bijective
  have ho := mfderiv_openSubset_val_bijective
    (I := ProductHalfSpace.model (Vector 7)) (collarWindow A) (d p)
  have hs := (collarLevelAtlas A).bijective_mfderiv_subtype_val (d p).val
  have hdd := d.contMDiff_toFun.mdifferentiable (by simp) p
  have hod := (_root_.contMDiff_subtype_val (I := ProductHalfSpace.model (Vector 7))
    (U := collarWindow A) (n := ∞)).mdifferentiable (by simp) (d p)
  have hsd := (collarLevelAtlas A).contMDiff_subtype_val.mdifferentiable (by simp) (d p).val
  change Bijective (mfderiv (ProductHalfSpace.model (Vector 7)) collarModel
    ((Subtype.val : CollarSuperlevel A → Collar) ∘
      ((Subtype.val : collarWindow A → CollarSuperlevel A) ∘ d)) p)
  rw [mfderiv_comp p hsd (hod.comp p hdd), mfderiv_comp p hod hdd]
  exact hs.comp (ho.comp hd)

def collarAmbientDerivative (p : collarPart A) :
    (ℝ × Vector 7) →L[ℝ] Vector (e.ambientDimension + 6) := by
  let := collarChartedSpace A
  exact mfderiv (ProductHalfSpace.model (Vector 7)) (𝓡 (e.ambientDimension + 6))
    (fun q : collarPart A ↦ q.val.val) p

theorem collarAmbientDerivative_eq (p : collarPart A) :
    collarAmbientDerivative A p =
      (A.collarSheetDerivative ((collarHomeomorph A).symm p).val).comp
        (collarParameterDerivative A p) := by
  let := collarChartedSpace A
  have heq : (fun q : collarPart A ↦ q.val.val) =
      A.collarSheet ∘ (fun q : collarPart A ↦ ((collarHomeomorph A).symm q).val) :=
    funext (fun q ↦ (collarHomeomorph_symm_ambient A q).symm)
  have hs := A.contMDiffOn_collarSheet.contMDiffAt
    (A.tubeHeightCoordinates.open_source.mem_nhds
      (collarParameters_subset_source A ((collarHomeomorph A).symm p).property))
  change mfderiv (ProductHalfSpace.model (Vector 7)) (𝓡 (e.ambientDimension + 6))
    (fun q : collarPart A ↦ q.val.val) p = _
  rw [heq]
  exact mfderiv_comp p (hs.mdifferentiableAt (by simp))
    ((contMDiff_collarParameters A).mdifferentiableAt (by simp))

theorem injective_collarAmbientDerivative (p : collarPart A) :
    Injective (collarAmbientDerivative A p) := by
  rw [collarAmbientDerivative_eq]
  exact (A.injective_collarSheetDerivative
    (collarParameters_subset_source A ((collarHomeomorph A).symm p).property)).comp
      (bijective_collarParameterDerivative A p).1

theorem range_collarAmbientDerivative (p : collarPart A) :
    (collarAmbientDerivative A p).range =
      (A.collarSheetDerivative ((collarHomeomorph A).symm p).val).range := by
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨collarParameterDerivative A p v, by rw [collarAmbientDerivative_eq]; rfl⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨w, hw⟩ := (bijective_collarParameterDerivative A p).2 v
    refine ⟨w, ?_⟩
    rw [collarAmbientDerivative_eq]
    exact congrArg (A.collarSheetDerivative ((collarHomeomorph A).symm p).val) hw

def collarNormalFrame (p : collarPart A) :
    Vector ((e.ambientDimension - 7) + 5) →L[ℝ] Vector (e.ambientDimension + 6) :=
  A.collarSheetFrame ((collarHomeomorph A).symm p).val

theorem contMDiff_collarNormalFrame : letI := collarChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 7))
      𝓘(ℝ, Vector ((e.ambientDimension - 7) + 5) →L[ℝ] Vector (e.ambientDimension + 6)) ∞
      (collarNormalFrame A) := by
  let := collarChartedSpace A
  intro p
  exact (A.contMDiffOn_collarSheetFrame.contMDiffAt
    (A.tubeHeightCoordinates.open_source.mem_nhds
      (collarParameters_subset_source A ((collarHomeomorph A).symm p).property))).comp p
        ((contMDiff_collarParameters A) p)

theorem collarNormalFrame_norm (p : collarPart A)
    (v : Vector ((e.ambientDimension - 7) + 5)) : ‖collarNormalFrame A p v‖ = ‖v‖ :=
  A.collarSheetFrame_norm _ v

theorem collarNormalFrame_range (p : collarPart A) :
    (collarNormalFrame A p).range = (collarAmbientDerivative A p).rangeᗮ := by
  rw [range_collarAmbientDerivative]
  exact A.collarSheetFrame_range
    (collarParameters_subset_source A ((collarHomeomorph A).symm p).property)

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
