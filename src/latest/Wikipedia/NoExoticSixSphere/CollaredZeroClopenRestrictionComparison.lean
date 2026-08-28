import Wikipedia.NoExoticSixSphere.CollaredZeroClopenRestrictionFrame
import Wikipedia.NoExoticSixSphere.StabilizedFramedDiffeomorph

/-!
# Full framed comparisons for arbitrary native clopen state restrictions

The restricted state's native zero manifold is compared with the actual
clopen original zero manifold. The embedding and all induced normal
columns agree without adding axes. Thus the comparison can also be
inverted, retaining both native zero atlases and independent tubular choices.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CollaredZero.ClopenRestriction

open GLOrthonormalization Stiefel Wikipedia.HopfProblem.DegreeCollapse

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)
  (U : TopologicalSpace.Opens S.Space) (hU : IsClosed (U : Set S.Space))
  (m : S.Space) (m' : (S.restrictClopen U hU).Space)

def comparison :
    letI := S.zeroAtlas; letI := (S.restrictClopen U hU).zeroAtlas;
    StabilizedFramedDiffeomorph
      (CollaredZero.embedding (S.restrictClopen U hU))
      (CollaredZero.normalFrame (S.restrictClopen U hU) m')
      (ClopenEmbedding.restrict (CollaredZero.embedding S) (S.zeroOpen U) (S.zeroOpen_closed U hU))
      (ClopenEmbedding.restrictNormalFrame (CollaredZero.embedding S) (S.zeroOpen U)
        (S.zeroOpen_closed U hU) (CollaredZero.normalFrame S m)) := by
  let := S.zeroAtlas
  let := (S.restrictClopen U hU).zeroAtlas
  refine
    { extra := 0
      ambient := LinearIsometryEquiv.refl ℝ (Vector S.embedding.ambientDimension)
      normal := LinearIsometryEquiv.refl ℝ (Vector (S.embedding.ambientDimension - 6))
      diffeomorph := S.restrictClopenZeroDiffeomorph U hU
      embedding_eq := ?_
      frame_eq := ?_ }
  · intro p
    change S.embedding.toFun (S.restrictClopenZeroDiffeomorph U hU p).val.val =
      appendZeroMap S.embedding.ambientDimension 0 (S.embedding.toFun p.val.val)
    rw [S.restrictClopenZeroDiffeomorph_point, FramedBlock.appendZero_zero]
  · intro p v
    change (CollaredZero.normalFrame S m).ambient
        (S.restrictClopenZeroDiffeomorph U hU p).val v =
      BlockSum.operator 0 ((CollaredZero.normalFrame (S.restrictClopen U hU) m').ambient p) v
    rw [BlockSum.operator_zero]
    exact (sixFrame S U hU m m' p v).symm

theorem comparison_extra :
    letI := S.zeroAtlas; letI := (S.restrictClopen U hU).zeroAtlas;
    (comparison S U hU m m').extra = 0 := by
  let := S.zeroAtlas
  let := (S.restrictClopen U hU).zeroAtlas
  rfl

def comparisonSymm :
    letI := S.zeroAtlas; letI := (S.restrictClopen U hU).zeroAtlas;
    StabilizedFramedDiffeomorph
      (ClopenEmbedding.restrict (CollaredZero.embedding S) (S.zeroOpen U) (S.zeroOpen_closed U hU))
      (ClopenEmbedding.restrictNormalFrame (CollaredZero.embedding S) (S.zeroOpen U)
        (S.zeroOpen_closed U hU) (CollaredZero.normalFrame S m))
      (CollaredZero.embedding (S.restrictClopen U hU))
      (CollaredZero.normalFrame (S.restrictClopen U hU) m') := by
  let := S.zeroAtlas
  let := (S.restrictClopen U hU).zeroAtlas
  exact StabilizedFramedDiffeomorph.symmOfZero (comparison S U hU m m')
    (comparison_extra S U hU m m')

end NoExoticSixSphere.CollaredZero.ClopenRestriction
