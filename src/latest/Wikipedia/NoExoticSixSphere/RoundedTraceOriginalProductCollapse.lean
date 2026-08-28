import Wikipedia.NoExoticSixSphere.AffineProductCollapseData
import Wikipedia.NoExoticSixSphere.OrthonormalRangeFrame
import Wikipedia.NoExoticSixSphere.RoundedTraceStableClass

/-!
# The trace's original endpoint is the actual six-factor product collapse

The height translation, normal-column permutation, and last-column sign
are all included in explicit coordinates. The old frame is its actual
Gram--Schmidt normalization, packaged as a smooth range frame. Its collapse
is normalized by a positive target rescaling before taking the product.

This constructs a product representative of the surgery class. It does not
assert a nullhomotopy, or silently identify the input frame with its
normalization in the stable group.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace.OriginalEnd

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def productAmbientCoordinates : Vector (embedding A).ambientDimension ≃L[ℝ]
    (Vector e.ambientDimension × Vector 6) := EuclideanSpace.finAddEquivProd

def productNormalCoordinates : (embedding A).NormalModel ≃L[ℝ]
    (e.NormalModel × Vector 6) :=
  let L := (((normalModelCoordinates A).trans (boundaryLastReflection (e := e))).trans
    (boundaryFrameCoordinates (e := e))).trans
      (StabilizedSpanningDisk.endColumnPermutation (e.ambientDimension - 6))
  L.toContinuousLinearEquiv.trans EuclideanSpace.finAddEquivProd

def heightOffset : Vector (embedding A).ambientDimension :=
  StabilizedSpanningDisk.coordinates e.ambientDimension 4 ((0, UnroundedTrace.height A), 0)

theorem productAmbientCoordinates_embedding (x : M) :
    productAmbientCoordinates A ((embedding A).toFun x - heightOffset A) = (e.toFun x, 0) := by
  change EuclideanSpace.finAddEquivProd
    (StabilizedSpanningDisk.coordinates e.ambientDimension 4
      ((e.toFun x, UnroundedTrace.height A), 0) -
        StabilizedSpanningDisk.coordinates e.ambientDimension 4
          ((0, UnroundedTrace.height A), 0)) = _
  rw [← map_sub]
  simp only [Prod.mk_sub_mk, sub_zero, sub_self]
  rw [StabilizedSpanningDisk.coordinates_old]
  change EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd.symm
    (e.toFun x, (0 : Vector 6))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem productAmbientCoordinates_frame (x : M) (v : (embedding A).NormalModel) :
    productAmbientCoordinates A ((normalFraming A).ambient x v) =
      (a.normalized.ambient x (productNormalCoordinates A v).1,
        (productNormalCoordinates A v).2) := by
  rw [normalFraming_ambient, frame_apply, BlockSum.operator_apply]
  change EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd.symm _) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

def productCollapseData (d : e.FramedCollapseData a.normalized) :
    (embedding A).FramedCollapseData (normalFraming A) :=
  AffineProductCollapse.collapseData d (productAmbientCoordinates A) (productNormalCoordinates A)
    (heightOffset A) (productAmbientCoordinates_embedding A) (productAmbientCoordinates_frame A)

theorem productCollapseData_map (d : e.FramedCollapseData a.normalized) :
    (productCollapseData A d).map =
      AffineProductCollapse.productMap d (productAmbientCoordinates A) (productNormalCoordinates A)
        (heightOffset A) := rfl

/-- For an already orthonormal input, the original frame and collapse are retained exactly. -/
def orthonormalInputCollapseData (ha : ∀ x v, ‖a.ambient x v‖ = ‖v‖)
    (d : e.FramedCollapseData a) : (embedding A).FramedCollapseData (normalFraming A) :=
  AffineProductCollapse.collapseData d (productAmbientCoordinates A) (productNormalCoordinates A)
    (heightOffset A) (productAmbientCoordinates_embedding A) (by
      intro x v
      rw [productAmbientCoordinates_frame, a.normalized_eq_self ha])

theorem orthonormalInputCollapseData_map (ha : ∀ x v, ‖a.ambient x v‖ = ‖v‖)
    (d : e.FramedCollapseData a) :
    (orthonormalInputCollapseData A ha d).map =
      AffineProductCollapse.productMap d (productAmbientCoordinates A) (productNormalCoordinates A)
        (heightOffset A) := rfl

variable [T2Space M] (hR : A.radius = 2)

theorem surgery_cubicalStableClass_eq_product (d : e.FramedCollapseData a.normalized) :
    letI := UnitSurgery.targetChartedSpace A hR;
    ∀ dS : (UnitSurgery.inducedEmbedding A hR).FramedCollapseData
      (UnitSurgery.normalFraming A hR),
      dS.cubicalStableClass (endpoint_ambientDimension_ge_eight (e := e) (f (pole 3))) =
        (productCollapseData A d).cubicalStableClass
          (endpoint_ambientDimension_ge_eight (e := e) (f (pole 3))) :=
  endpoint_cubicalStableClass_eq A hR (productCollapseData A d)

theorem surgery_cubicalStableClass_eq_orthonormal_product
    (ha : ∀ x v, ‖a.ambient x v‖ = ‖v‖) (d : e.FramedCollapseData a) :
    letI := UnitSurgery.targetChartedSpace A hR;
    ∀ dS : (UnitSurgery.inducedEmbedding A hR).FramedCollapseData
      (UnitSurgery.normalFraming A hR),
      dS.cubicalStableClass (endpoint_ambientDimension_ge_eight (e := e) (f (pole 3))) =
        (orthonormalInputCollapseData A ha d).cubicalStableClass
          (endpoint_ambientDimension_ge_eight (e := e) (f (pole 3))) :=
  endpoint_cubicalStableClass_eq A hR (orthonormalInputCollapseData A ha d)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace.OriginalEnd
