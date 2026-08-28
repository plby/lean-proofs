import Wikipedia.NoExoticSixSphere.CollaredZeroNormalFrame
import Wikipedia.NoExoticSixSphere.EmbeddedTimeNaturality
import Wikipedia.NoExoticSixSphere.OrthogonalFrameAppendReflection
import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenReversal

/-!
# The exact induced six-frame when a collared state's time is reversed

The seven-dimensional embedding and normal frame do not change. The actual
outward time-normal changes sign, so the induced six-frame is precomposed
by the last-column reflection in its own normal-coordinate model.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CollaredSeam

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)

local instance reversalChartedSpace : ChartedSpace (Vector (6 + 1)) S.Space := S.atlas

local instance reversalIsManifold : IsManifold (𝓡 (6 + 1)) ∞ S.Space := S.smooth

def reversalSixColumnChange (m : S.Space) :
    Vector (S.embedding.ambientDimension - 6) ≃ₗᵢ[ℝ]
      Vector (S.embedding.ambientDimension - 6) :=
  (EmbeddedTime.normalCoordinates (n := 6) S.embedding m).trans
    ((OrthogonalFrameAppend.lastReflection (S.embedding.ambientDimension - 7)).trans
      (EmbeddedTime.normalCoordinates (n := 6) S.embedding m).symm)

theorem reversalSixColumnChange_apply (m : S.Space)
    (v : Vector (S.embedding.ambientDimension - 6)) :
    reversalSixColumnChange S m v = (EmbeddedTime.normalCoordinates (n := 6) S.embedding m).symm
      (OrthogonalFrameAppend.lastReflection (S.embedding.ambientDimension - 7)
        (EmbeddedTime.normalCoordinates (n := 6) S.embedding m v)) := by
  simp only [reversalSixColumnChange, LinearIsometryEquiv.trans_apply]

theorem reverse_outwardNormal (m : S.Space) (p : S.Zero) :
    letI := S.zeroAtlas; letI := S.reverse.zeroAtlas;
    EmbeddedTime.outwardNormal (n := 6) S.reverse.embedding (CollaredZero.retraction S.reverse m)
      S.reverse.zeroTimeMap (S.reverseZeroDiffeomorph p) =
    -EmbeddedTime.outwardNormal (n := 6) S.embedding (CollaredZero.retraction S m)
      S.zeroTimeMap p := by
  let := S.zeroAtlas
  let := S.reverse.zeroAtlas
  change -NormedSpace.normalize
      (EmbeddedTime.gradient S.embedding (CollaredZero.retraction S.reverse m)
        (fun x ↦ -S.time x) p.val) =
    -(-NormedSpace.normalize (EmbeddedTime.gradient S.embedding
      (CollaredZero.retraction S m) S.time p.val))
  rw [EmbeddedTime.gradient_neg S.embedding (CollaredZero.retraction S.reverse m)
    S.time S.time_smooth p.val,
    EmbeddedTime.gradient_retraction_independent S.embedding (CollaredZero.retraction S m)
      S.time (CollaredZero.retraction S.reverse m) S.time_smooth p.val]
  simp only [NormedSpace.normalize, norm_neg, smul_neg, neg_neg]

theorem reverse_zeroColumns (m : S.Space) (p : S.Zero) :
    letI := S.zeroAtlas; letI := S.reverse.zeroAtlas;
    EmbeddedTime.zeroColumns (n := 6) S.reverse.embedding (CollaredZero.retraction S.reverse m)
      S.reverse.zeroTimeMap S.reverse.normalFrame (S.reverseZeroDiffeomorph p) =
    (EmbeddedTime.zeroColumns (n := 6) S.embedding (CollaredZero.retraction S m)
      S.zeroTimeMap S.normalFrame p).comp
      (OrthogonalFrameAppend.lastReflection
        (S.embedding.ambientDimension - 7)).toContinuousLinearMap := by
  let := S.zeroAtlas
  let := S.reverse.zeroAtlas
  change OrthogonalFrameAppend.operator (S.normalFrame.orthonormal p.val).val
    (EmbeddedTime.outwardNormal (n := 6) S.reverse.embedding (CollaredZero.retraction S.reverse m)
      S.reverse.zeroTimeMap (S.reverseZeroDiffeomorph p)) = _
  rw [reverse_outwardNormal]
  exact OrthogonalFrameAppend.operator_neg (S.normalFrame.orthonormal p.val).val
    (EmbeddedTime.outwardNormal (n := 6) S.embedding (CollaredZero.retraction S m) S.zeroTimeMap p)

theorem reverse_sixFrame (m : S.Space) (p : S.Zero) :
    letI := S.zeroAtlas; letI := S.reverse.zeroAtlas;
    ∀ v : Vector (S.embedding.ambientDimension - 6),
      (CollaredZero.normalFrame S.reverse m).ambient (S.reverseZeroDiffeomorph p) v =
      (CollaredZero.normalFrame S m).ambient p (reversalSixColumnChange S m v) := by
  let := S.zeroAtlas
  let := S.reverse.zeroAtlas
  intro v
  let Q := EmbeddedTime.normalCoordinates (n := 6) S.embedding m
  let C := EmbeddedTime.zeroColumns (n := 6) S.embedding (CollaredZero.retraction S m)
    S.zeroTimeMap S.normalFrame p
  have hQ : Q (reversalSixColumnChange S m v) =
      OrthogonalFrameAppend.lastReflection (S.embedding.ambientDimension - 7) (Q v) := by
    rw [reversalSixColumnChange_apply]
    exact Q.apply_symm_apply _
  have hs := congrArg
    (fun L : Vector ((S.embedding.ambientDimension - 7) + 1) →L[ℝ]
      Vector S.embedding.ambientDimension ↦ L (Q v)) (reverse_zeroColumns S m p)
  have hi := congrArg C hQ
  change EmbeddedTime.zeroColumns (n := 6) S.reverse.embedding
      (CollaredZero.retraction S.reverse m) S.reverse.zeroTimeMap S.reverse.normalFrame
      (S.reverseZeroDiffeomorph p) (Q v) = C (Q (reversalSixColumnChange S m v))
  exact hs.trans hi.symm

end NoExoticSixSphere.CollaredSeam
