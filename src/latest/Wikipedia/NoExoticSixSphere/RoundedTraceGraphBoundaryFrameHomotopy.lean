import Wikipedia.NoExoticSixSphere.RoundedTraceGraphBoundaryFrame

/-!
# Actual normal-frame homotopy to reordered boundary stabilization

The slope is multiplied by `1 - t`. Every stage is a full norm-preserving
frame of the fixed native graph boundary normal bundle. The last stage is
identified with the original induced boundary frame plus the positive time
axis, with its coordinate reordering written explicitly.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff unitInterval

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def graphBoundaryPlaneMap :
    C(ℝ × Boundary A, TimeGraphBoundaryFrameSpace (e := e) →L[ℝ] TimeGraphSpace (e := e)) :=
  ⟨fun q ↦ graphBoundaryPlaneFrame A q.2 q.1, continuous_graphBoundaryPlaneFrame A⟩

def boundaryTimeSlopeMap : C(Boundary A, ℝ) :=
  ⟨boundaryTimeSlope A, continuous_boundaryTimeSlope A⟩

def graphBoundaryFrameMap :
    C(Boundary A, TimeGraphBoundaryFrameSpace (e := e) →L[ℝ] TimeGraphSpace (e := e)) :=
  (graphBoundaryPlaneMap A).comp ((boundaryTimeSlopeMap A).prodMk (ContinuousMap.id _))

theorem graphBoundaryFrameMap_apply (p : Boundary A) :
    graphBoundaryFrameMap A p = timeGraphInducedBoundaryFrame A p :=
  graphBoundaryPlaneFrame_actual A p

def graphBoundaryStabilizedFrameMap :
    C(Boundary A, TimeGraphBoundaryFrameSpace (e := e) →L[ℝ] TimeGraphSpace (e := e)) :=
  (graphBoundaryPlaneMap A).comp ((ContinuousMap.const _ (0 : ℝ)).prodMk (ContinuousMap.id _))

def boundaryTimeSlopeHomotopy :
    (boundaryTimeSlopeMap A).Homotopy (ContinuousMap.const _ (0 : ℝ)) where
  toFun q := (1 - (q.1 : ℝ)) * boundaryTimeSlope A q.2
  continuous_toFun := (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    ((continuous_boundaryTimeSlope A).comp continuous_snd)
  map_zero_left p := by change (1 - 0) * boundaryTimeSlope A p = _; rw [sub_zero, one_mul]; rfl
  map_one_left p := by change (1 - 1) * boundaryTimeSlope A p = _; rw [sub_self, zero_mul]; rfl

def graphBoundaryFrameHomotopy :
    (graphBoundaryFrameMap A).Homotopy (graphBoundaryStabilizedFrameMap A) :=
  (ContinuousMap.Homotopy.refl (graphBoundaryPlaneMap A)).comp
    ((boundaryTimeSlopeHomotopy A).prodMk (ContinuousMap.Homotopy.refl (ContinuousMap.id _)))

theorem graphBoundaryFrameHomotopy_norm (t : I) (p : Boundary A)
    (v : TimeGraphBoundaryFrameSpace (e := e)) :
    ‖graphBoundaryFrameHomotopy A (t, p) v‖ = ‖v‖ :=
  norm_graphBoundaryPlaneFrame A p _ v

theorem graphBoundaryFrameHomotopy_range (t : I) (p : Boundary A) :
    (graphBoundaryFrameHomotopy A (t, p)).range = (timeGraphBoundaryDifferential A p).rangeᗮ :=
  graphBoundaryPlaneFrame_range A p _

def graphBoundaryOriginalCoordinates (v : TimeGraphBoundaryFrameSpace (e := e)) :
    Vector (((e.ambientDimension - 6) + 5) + 1) :=
  EuclideanSpace.finAddEquivProd.symm (v.fst.fst, EuclideanTailCoordinates.scalar v.snd)

theorem graphBoundaryStabilizedFrameMap_apply (p : Boundary A)
    (v : TimeGraphBoundaryFrameSpace (e := e)) :
    graphBoundaryStabilizedFrameMap A p v =
      CylinderNormalFrame.liftFrame (inducedBoundaryFrame A p)
        (graphBoundaryOriginalCoordinates (e := e) v) +
      v.fst.snd • timeGraphTimeUnit (e := e) := by
  change graphBoundaryPlaneFrame A p 0 v = _
  rw [graphBoundaryPlaneFrame_zero, CylinderNormalFrame.liftFrame_apply,
    inducedBoundaryFrame_apply]
  simp only [graphBoundaryOriginalCoordinates, ContinuousLinearEquiv.apply_symm_apply,
    LinearIsometryEquiv.symm_apply_apply]
  apply (timeGraphCoordinates (e := e)).injective
  apply Prod.ext
  · change (0 : ℝ) + v.fst.snd * 1 + v.snd * 0 = 0 + v.fst.snd * 1
    ring
  · change traceNormalFrame A p.val v.fst.fst + v.fst.snd • (0 : Vector _) +
      v.snd • outwardNormal A p =
        (traceNormalFrame A p.val v.fst.fst + v.snd • outwardNormal A p) +
          v.fst.snd • (0 : Vector _)
    rw [smul_zero, add_zero, add_zero]

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
