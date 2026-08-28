import Wikipedia.NoExoticSixSphere.CollaredZeroNormalFrame
import Wikipedia.NoExoticSixSphere.LowSurgerySeamSixFrame
import Wikipedia.NoExoticSixSphere.CollaredSeamFrame

/-!
# The actual induced six-frame of a collared state after native surgery

The generic single-surgery theorem is applied to the constructed state
fields and to the literal native zero diffeomorphism. Equality of the two
source time functions is used only to compare their actual induced columns;
the original zero atlas is retained throughout.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CollaredSeam

open GLOrthonormalization Stiefel Wikipedia.HopfProblem.DegreeCollapse
open LowSurgery FramedAttachingProduct RoundedTrace NativeSurgery

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)

local instance surgeryChartedSpace : ChartedSpace (Vector (6 + 1)) S.Space := S.atlas

local instance surgeryIsManifold : IsManifold (𝓡 (6 + 1)) ∞ S.Space := S.smooth

variable {d : ℕ} {f : Sphere d → S.Space}
  (A : FramedAttachingProduct S.embedding S.normalFrame f) (hA : A.radius = 2)
  (T : TimeData A) (hT : T.time = S.time)

def performSixColumnChange (m : S.Space) (m' : (S.perform A hA T hT).Space) :
    Vector ((S.perform A hA T hT).embedding.ambientDimension - 6) ≃ₗᵢ[ℝ]
      Vector ((S.embedding.ambientDimension - 6) + (1 + (1 + (d + 1)))) := by
  let := boundaryChartedSpace A
  exact LowSurgerySeam.normalFrameColumnChange A m m'

theorem perform_sixFrame (m : S.Space) (m' : (S.perform A hA T hT).Space) (p : S.Zero) :
    letI := S.zeroAtlas; letI := (S.perform A hA T hT).zeroAtlas;
    ∀ v : Vector ((S.perform A hA T hT).embedding.ambientDimension - 6),
      (CollaredZero.normalFrame (S.perform A hA T hT) m').ambient
        (S.performZeroDiffeomorph A hA T hT p) v =
      BlockSum.operator (1 + (1 + (d + 1))) ((CollaredZero.normalFrame S m).ambient p)
        (performSixColumnChange S A hA T hT m m' v) := by
  let := S.zeroAtlas
  let := boundaryChartedSpace A
  let := boundary_isManifold A
  let : ChartedSpace (Vector 6) {x : S.Space // originalTimeMap A T x = 0} :=
    originalZeroAtlas A T
  let : ChartedSpace (Vector 6)
      {x : otherBoundaryPart A // resultTimeMap A hA T x = 0} := resultZeroAtlas A hA T
  let := (S.perform A hA T hT).zeroAtlas
  let E := CollaredSevenState.regularZeroCongr S.zeroTimeMap (originalTimeMap A T)
    S.time_smooth T.smooth S.time_regular T.regular
    (ContinuousMap.ext (fun x ↦ (congrFun hT x).symm))
  have he : (E p).val = p.val := regularZeroCongr_point S.zeroTimeMap (originalTimeMap A T)
    S.time_smooth T.smooth S.time_regular T.regular
    (ContinuousMap.ext (fun x ↦ (congrFun hT x).symm)) p
  have htmap : originalTimeMap A T = S.zeroTimeMap :=
    ContinuousMap.ext (fun x ↦ congrFun hT x)
  have hcols := EmbeddedTime.zeroColumns_congr_time (n := 6) S.embedding
    (CollaredZero.retraction S m) S.zeroTimeMap S.normalFrame (originalTimeMap A T)
    htmap (E p) p he
  have ho : (EmbeddedTime.zeroNormalFrame (n := 6) S.embedding (CollaredZero.retraction S m)
      (originalTimeMap A T) T.smooth T.regular S.normalFrame m).ambient (E p) =
        (CollaredZero.normalFrame S m).ambient p := by
    apply ContinuousLinearMap.ext
    intro w
    change EmbeddedTime.zeroColumns (n := 6) S.embedding (CollaredZero.retraction S m)
        (originalTimeMap A T) S.normalFrame (E p)
        (EmbeddedTime.normalCoordinates (n := 6) S.embedding m w) =
      EmbeddedTime.zeroColumns (n := 6) S.embedding (CollaredZero.retraction S m)
        S.zeroTimeMap S.normalFrame p (EmbeddedTime.normalCoordinates (n := 6) S.embedding m w)
    rw [hcols]
  intro v
  have hs := LowSurgerySeam.normalFrame_zero A hA T (CollaredZero.retraction S m) m m'
    (CollaredZero.retraction (S.perform A hA T hT) m') (E p) v
  have hb := congrArg
    (fun L : Vector (S.embedding.ambientDimension - 6) →L[ℝ]
      Vector S.embedding.ambientDimension ↦
        BlockSum.operator (1 + (1 + (d + 1))) L
          (performSixColumnChange S A hA T hT m m' v)) ho
  exact hs.trans hb

end NoExoticSixSphere.CollaredSeam
