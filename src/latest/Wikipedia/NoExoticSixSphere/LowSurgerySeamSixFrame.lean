import Wikipedia.NoExoticSixSphere.LowSurgerySeamGradient
import Wikipedia.NoExoticSixSphere.OrthogonalFrameAppendStabilization
import Wikipedia.NoExoticSixSphere.RegularTimeZeroNormalFrame

/-!
# The full induced six-frame under the actual native surgery zero diffeomorphism

The new end's seven-frame is already orthonormal. Append its actual outward
time-normal and compare all resulting six-boundary normal columns with the
original induced six-frame plus the new coordinate axes. The comparison is
an explicit constant isometry, including the signed seven-end column change
and the permutation moving the time-normal before the new axes.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.LowSurgerySeam

open GLOrthonormalization Stiefel OrthogonalFrameAppend
open Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
open FramedAttachingProduct RoundedTrace NativeSurgery

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : Sphere d → M} (A : FramedAttachingProduct e a f)

def zeroColumnChange : letI := boundaryChartedSpace A;
    Vector (((otherBoundaryEuclideanEmbedding A).ambientDimension - 7) + 1) ≃ₗᵢ[ℝ]
      Vector (((e.ambientDimension - 7) + 1) + (1 + (1 + (d + 1)))) := by
  let := boundaryChartedSpace A
  exact (extendColumnChange (columnChange A) 1).trans
    (appendBlockPermutation (e.ambientDimension - 7) (1 + (1 + (d + 1))))

theorem zeroColumns_zero (hR : A.radius = 2) (T : TimeData A) (r : e.TubularRetraction) :
    letI := boundaryChartedSpace A;
    letI := originalZeroAtlas A T; letI := resultZeroAtlas A hR T;
    ∀ (r' : (otherBoundaryEuclideanEmbedding A).TubularRetraction) (p : OriginalZero A T) v,
      EmbeddedTime.zeroColumns (n := 6) (otherBoundaryEuclideanEmbedding A) r'
        (resultTimeMap A hR T) (inducedOtherEndNormalFraming A) (zeroDiffeomorph A hR T p) v =
      BlockSum.operator (1 + (1 + (d + 1)))
        (EmbeddedTime.zeroColumns (n := 6) e r (originalTimeMap A T) a p)
        (zeroColumnChange A v) := by
  let := boundaryChartedSpace A
  let := originalZeroAtlas A T
  let := resultZeroAtlas A hR T
  intro r' p v
  have hn : ((inducedOtherEndNormalFraming A).orthonormal
      (zeroDiffeomorph A hR T p).val).val =
        (inducedOtherEndNormalFraming A).ambient (zeroDiffeomorph A hR T p).val :=
    Orthonormalization.operator_eq_self (inducedOtherEndNormalFraming A).ambient
      (zeroDiffeomorph A hR T p).val
      (inducedOtherEndNormalFraming_norm A (zeroDiffeomorph A hR T p).val)
  have hf : (inducedOtherEndNormalFraming A).ambient (zeroDiffeomorph A hR T p).val =
      (BlockSum.operator (1 + (1 + (d + 1))) (a.orthonormal p.val).val).comp
        (columnChange A).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro w
    exact framing_zero A hR T p w
  change OrthogonalFrameAppend.operator
      ((inducedOtherEndNormalFraming A).orthonormal (zeroDiffeomorph A hR T p).val).val
      (EmbeddedTime.outwardNormal (n := 6) (otherBoundaryEuclideanEmbedding A) r'
        (resultTimeMap A hR T) (zeroDiffeomorph A hR T p)) v = _
  rw [hn, hf, outwardNormal_zero A hR T r]
  change OrthogonalFrameAppend.operator
      ((BlockSum.operator (1 + (1 + (d + 1))) (a.orthonormal p.val).val).comp
        (columnChange A).toContinuousLinearMap)
      (appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))
        (EmbeddedTime.outwardNormal (n := 6) e r (originalTimeMap A T) p)) v = _
  rw [operator_comp_columnChange, operator_block]
  rfl

def normalFrameColumnChange (m : M) (m' : otherBoundaryPart A) :
    letI := boundaryChartedSpace A;
    Vector ((otherBoundaryEuclideanEmbedding A).ambientDimension - 6) ≃ₗᵢ[ℝ]
      Vector ((e.ambientDimension - 6) + (1 + (1 + (d + 1)))) := by
  let := boundaryChartedSpace A
  let := boundary_isManifold A
  exact (EmbeddedTime.normalCoordinates (n := 6) (otherBoundaryEuclideanEmbedding A) m').trans
    ((zeroColumnChange A).trans
      (extendColumnChange (EmbeddedTime.normalCoordinates (n := 6) e m)
        (1 + (1 + (d + 1)))).symm)

theorem normalFrameColumnChange_apply (m : M) (m' : otherBoundaryPart A) :
    letI := boundaryChartedSpace A; letI := boundary_isManifold A;
    ∀ v, normalFrameColumnChange A m m' v =
      (extendColumnChange (EmbeddedTime.normalCoordinates (n := 6) e m)
        (1 + (1 + (d + 1)))).symm
          (zeroColumnChange A (EmbeddedTime.normalCoordinates (n := 6)
            (otherBoundaryEuclideanEmbedding A) m' v)) := by
  let := boundaryChartedSpace A
  let := boundary_isManifold A
  intro v
  simp only [normalFrameColumnChange, LinearIsometryEquiv.trans_apply]

theorem normalFrame_zero (hR : A.radius = 2) (T : TimeData A) (r : e.TubularRetraction)
    (m : M) (m' : otherBoundaryPart A) :
    letI := boundaryChartedSpace A; letI := boundary_isManifold A;
    letI : ChartedSpace (Vector 6) {x : M // originalTimeMap A T x = 0} := originalZeroAtlas A T;
    letI : ChartedSpace (Vector 6)
      {x : otherBoundaryPart A // resultTimeMap A hR T x = 0} := resultZeroAtlas A hR T;
    ∀ (r' : (otherBoundaryEuclideanEmbedding A).TubularRetraction) (p : OriginalZero A T)
      (v : Vector ((otherBoundaryEuclideanEmbedding A).ambientDimension - 6)),
      (EmbeddedTime.zeroNormalFrame (n := 6) (otherBoundaryEuclideanEmbedding A) r'
        (resultTimeMap A hR T) (contMDiff_timeFunction A hR T)
        (regular_timeFunction_zero A hR T) (inducedOtherEndNormalFraming A) m').ambient
          (zeroDiffeomorph A hR T p) v =
      BlockSum.operator (1 + (1 + (d + 1)))
        ((EmbeddedTime.zeroNormalFrame (n := 6) e r (originalTimeMap A T)
          T.smooth T.regular a m).ambient p) (normalFrameColumnChange A m m' v) := by
  let := boundaryChartedSpace A
  let := boundary_isManifold A
  let : ChartedSpace (Vector 6) {x : M // originalTimeMap A T x = 0} := originalZeroAtlas A T
  let : ChartedSpace (Vector 6) {x : otherBoundaryPart A // resultTimeMap A hR T x = 0} :=
    resultZeroAtlas A hR T
  intro r' p v
  let C := EmbeddedTime.zeroColumns (n := 6) e r (originalTimeMap A T) a p
  let Q := EmbeddedTime.normalCoordinates (n := 6) e m
  let w := zeroColumnChange A
    (EmbeddedTime.normalCoordinates (n := 6) (otherBoundaryEuclideanEmbedding A) m' v)
  have hc := normalFrameColumnChange_apply A m m' v
  have hb := block_comp_columnChange_symm (1 + (1 + (d + 1))) C Q w
  dsimp only [Q, w] at hb
  have hi := congrArg (fun z : Vector ((e.ambientDimension - 6) + (1 + (1 + (d + 1)))) ↦
    BlockSum.operator (1 + (1 + (d + 1))) (C.comp Q.toContinuousLinearMap) z) hc
  change EmbeddedTime.zeroColumns (n := 6) (otherBoundaryEuclideanEmbedding A) r'
      (resultTimeMap A hR T) (inducedOtherEndNormalFraming A) (zeroDiffeomorph A hR T p)
      (EmbeddedTime.normalCoordinates (n := 6) (otherBoundaryEuclideanEmbedding A) m' v) =
    BlockSum.operator (1 + (1 + (d + 1)))
      (C.comp Q.toContinuousLinearMap) (normalFrameColumnChange A m m' v)
  apply (zeroColumns_zero A hR T r r' p
    (EmbeddedTime.normalCoordinates (n := 6) (otherBoundaryEuclideanEmbedding A) m' v)).trans
  change BlockSum.operator (1 + (1 + (d + 1))) C w =
    BlockSum.operator (1 + (1 + (d + 1))) (C.comp Q.toContinuousLinearMap)
      (normalFrameColumnChange A m m' v)
  apply hb.symm.trans
  dsimp only [Q] at hi ⊢
  convert! hi.symm using 2

end NoExoticSixSphere.LowSurgerySeam
