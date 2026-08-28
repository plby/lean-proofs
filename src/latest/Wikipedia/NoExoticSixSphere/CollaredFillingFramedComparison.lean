import Wikipedia.NoExoticSixSphere.CollaredFillingBoundaryFrame
import Wikipedia.NoExoticSixSphere.CollaredZeroFramedComparison
import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenPromotion

/-!
# Promotion retains the actual induced framing on the filling's literal boundary

The comparison uses the original regular-zero atlas, the promoted state's
identity zero diffeomorphism, and the positive half's actual boundary
diffeomorphism. It adds no axes and retains every ambient normal column,
including the outward time-normal. No external boundary-frame equality is
an input.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CollaredFillingBoundary

open GLOrthonormalization Stiefel Wikipedia.HopfProblem
open DegreeCollapse SingularMayerVietoris

variable {B : Type} [TopologicalSpace B]

local instance comparisonStateChartedSpace (U : CollaredSevenState B) :
    ChartedSpace (Vector (6 + 1)) U.Space := U.atlas

local instance comparisonStateIsManifold (U : CollaredSevenState B) :
    IsManifold (𝓡 (6 + 1)) ∞ U.Space := U.smooth

def Comparison (S : LowCollaredSevenState B) (U : CollaredSevenState B) (b : B) : Type :=
  letI := S.zeroAtlas; letI := U.halfBoundaryAtlas;
  StabilizedFramedDiffeomorph (CollaredZero.embedding S)
    (CollaredZero.normalFrame S (CollaredZero.referencePoint S b))
    (embedding U) (normalFrame U (U.collar.zeroPoint b).val)

def fillingOfComparison {S : LowCollaredSevenState B} {U : CollaredSevenState B} {b : B}
    (F : Comparison S U b) : letI := S.zeroAtlas; FramedSevenFilling (𝓡 6) S.Zero := by
  let := S.zeroAtlas
  let := U.zeroAtlas
  let := U.halfChartedSpace
  let := U.halfBoundaryAtlas
  exact { U.framedFilling with boundaryDiffeomorph := F.diffeomorph }

theorem fillingOfComparison_boundary_point
    {S : LowCollaredSevenState B} {U : CollaredSevenState B} {b : B}
    (F : Comparison S U b) (p : S.Zero) :
    letI := S.zeroAtlas; letI := U.halfBoundaryAtlas;
    ((fillingOfComparison F).boundaryDiffeomorph p).val = (F.diffeomorph p).val := by
  let := S.zeroAtlas
  let := U.halfBoundaryAtlas
  rfl

theorem fillingOfComparison_frame
    {S : LowCollaredSevenState B} {U : CollaredSevenState B} {b : B}
    (F : Comparison S U b) (p : U.Half) :
    letI := S.zeroAtlas; letI := U.halfChartedSpace;
    letI := (fillingOfComparison F).topology; letI := (fillingOfComparison F).atlas;
    (fillingOfComparison F).frame.ambient p = U.halfNormalFraming.ambient p := by
  let := S.zeroAtlas
  let := U.halfChartedSpace
  let := (fillingOfComparison F).topology
  let := (fillingOfComparison F).atlas
  rfl

theorem comparison_boundary_columns
    {S : LowCollaredSevenState B} {U : CollaredSevenState B} {b : B}
    (F : Comparison S U b) (p : S.Zero) :
    letI := S.zeroAtlas; letI := U.halfBoundaryAtlas;
    ∀ v : Vector ((S.embedding.ambientDimension - 6) + F.extra),
      columns U (U.collar.zeroPoint b).val (F.diffeomorph p)
        (EmbeddedTime.normalCoordinates (n := 6) U.embedding
          (U.collar.zeroPoint b).val (F.normal v)) =
      F.ambient (BlockSum.operator F.extra
        ((CollaredZero.normalFrame S (CollaredZero.referencePoint S b)).ambient p) v) := by
  let := S.zeroAtlas
  let := U.halfBoundaryAtlas
  intro v
  exact (normalFrame_ambient U (U.collar.zeroPoint b).val (F.diffeomorph p)
    (F.normal v)).symm.trans (F.frame_eq p v)

variable (S : LowCollaredSevenState B) [SimplyConnectedSpace B]
  [Subsingleton (SingularHomology B 1)] [Subsingleton (SingularHomology B 2)]
  [SimplyConnectedSpace S.PositiveHalf] [SimplyConnectedSpace S.NegativeHalf]
  [Subsingleton (SingularHomology S.PositiveHalf 2)]
  [Subsingleton (SingularHomology S.NegativeHalf 2)]

def promotionComparison (b : B) : Comparison S S.toCollaredSevenState b := by
  let U := S.toCollaredSevenState
  let := S.zeroAtlas
  let := U.zeroAtlas
  let := U.halfBoundaryAtlas
  let D := S.promotionZeroDiffeomorph.trans U.halfBoundaryDiffeomorph.symm
  refine
    { extra := 0
      ambient := LinearIsometryEquiv.refl ℝ (Vector S.embedding.ambientDimension)
      normal := LinearIsometryEquiv.refl ℝ (Vector (S.embedding.ambientDimension - 6))
      diffeomorph := D
      embedding_eq := ?_
      frame_eq := ?_ }
  · intro p
    change S.embedding.toFun p.val =
      appendZeroMap S.embedding.ambientDimension 0 (S.embedding.toFun p.val)
    exact (FramedBlock.appendZero_zero S.embedding.ambientDimension _).symm
  · intro p v
    change (normalFrame U (U.collar.zeroPoint b).val).ambient (D p) v =
      BlockSum.operator 0
        ((CollaredZero.normalFrame S (CollaredZero.referencePoint S b)).ambient p) v
    rw [BlockSum.operator_zero]
    rfl

theorem promotionComparison_extra (b : B) :
    letI := S.zeroAtlas; letI := S.toCollaredSevenState.halfBoundaryAtlas;
    (promotionComparison S b).extra = 0 := by
  let := S.zeroAtlas
  let := S.toCollaredSevenState.halfBoundaryAtlas
  rfl

theorem promotionComparison_point (b : B) (p : S.Zero) :
    letI := S.zeroAtlas; letI := S.toCollaredSevenState.halfBoundaryAtlas;
    ((promotionComparison S b).diffeomorph p).val.val = p.val := by
  let := S.zeroAtlas
  let := S.toCollaredSevenState.halfBoundaryAtlas
  rfl

end NoExoticSixSphere.CollaredFillingBoundary
