import Wikipedia.NoExoticSixSphere.LowCollaredStateClopenRestriction
import Wikipedia.NoExoticSixSphere.CollaredZeroComponentFrame

/-!
# Clopen restriction preserves the actual induced boundary six-frame

The restricted intrinsic gradient, normalized original normal columns,
and appended outward normal agree with their original counterparts.
The native restricted-zero diffeomorphism identifies every full induced
column, even for independent tubular choices. No boundary connectedness
is required.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CollaredZero.ClopenRestriction

open GLOrthonormalization Stiefel Wikipedia.HopfProblem.DegreeCollapse

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)
  (U : TopologicalSpace.Opens S.Space) (hU : IsClosed (U : Set S.Space))

local instance : ChartedSpace (Vector (6 + 1)) S.Space := S.atlas
local instance : IsManifold (𝓡 (6 + 1)) ∞ S.Space := S.smooth

theorem gradient (m : S.Space) (m' x : (S.restrictClopen U hU).Space) :
    EmbeddedTime.gradient (S.restrictClopen U hU).embedding
      (CollaredZero.retraction (S.restrictClopen U hU) m') (S.restrictClopen U hU).time x =
    EmbeddedTime.gradient S.embedding (CollaredZero.retraction S m) S.time x.val := by
  exact EmbeddedTime.gradient_natural S.embedding (S.restrictClopen U hU).embedding
    (CollaredZero.retraction S m) (CollaredZero.retraction (S.restrictClopen U hU) m')
    S.time (S.restrictClopen U hU).time S.time_smooth (S.restrictClopen U hU).time_smooth
    (fun q : U ↦ q.val) id x
    (isLocalDiffeomorphAt_openSubset_val (I := 𝓡 7) U x)
    ((Diffeomorph.refl (𝓡 7) U ∞).isLocalDiffeomorph x)
    (LinearIsometryEquiv.refl ℝ (Vector S.embedding.ambientDimension)).toLinearIsometry
    (fun _ ↦ rfl) (fun _ ↦ rfl)

theorem outwardNormal (m : S.Space) (m' : (S.restrictClopen U hU).Space)
    (p : (S.restrictClopen U hU).Zero) :
    letI := S.zeroAtlas; letI := (S.restrictClopen U hU).zeroAtlas;
    EmbeddedTime.outwardNormal (n := 6) (S.restrictClopen U hU).embedding
      (CollaredZero.retraction (S.restrictClopen U hU) m') (S.restrictClopen U hU).zeroTimeMap p =
    EmbeddedTime.outwardNormal (n := 6) S.embedding (CollaredZero.retraction S m)
      S.zeroTimeMap (S.restrictClopenZeroDiffeomorph U hU p).val := by
  let := S.zeroAtlas
  let := (S.restrictClopen U hU).zeroAtlas
  change -NormedSpace.normalize
      (EmbeddedTime.gradient (S.restrictClopen U hU).embedding
        (CollaredZero.retraction (S.restrictClopen U hU) m') (S.restrictClopen U hU).time p.val) =
    -NormedSpace.normalize (EmbeddedTime.gradient S.embedding (CollaredZero.retraction S m)
      S.time p.val.val)
  exact congrArg (fun z : Vector S.embedding.ambientDimension ↦ -NormedSpace.normalize z)
    (gradient S U hU m m' p.val)

theorem normalFrame_ambient (x : (S.restrictClopen U hU).Space) :
    (S.restrictClopen U hU).normalFrame.ambient x = S.normalFrame.ambient x.val := rfl

theorem orthonormal (p : (S.restrictClopen U hU).Zero) :
    letI := S.zeroAtlas; letI := (S.restrictClopen U hU).zeroAtlas;
    ((S.restrictClopen U hU).normalFrame.orthonormal p.val).val =
      (S.normalFrame.orthonormal (S.restrictClopenZeroDiffeomorph U hU p).val.val).val := by
  let := S.zeroAtlas
  let := (S.restrictClopen U hU).zeroAtlas
  exact Orthonormalization.operator_congr_value (S.restrictClopen U hU).normalFrame.ambient
    S.normalFrame.ambient p.val (S.restrictClopenZeroDiffeomorph U hU p).val.val
      (normalFrame_ambient S U hU p.val)

theorem zeroColumns (m : S.Space) (m' : (S.restrictClopen U hU).Space)
    (p : (S.restrictClopen U hU).Zero) :
    letI := S.zeroAtlas; letI := (S.restrictClopen U hU).zeroAtlas;
    EmbeddedTime.zeroColumns (n := 6) (S.restrictClopen U hU).embedding
      (CollaredZero.retraction (S.restrictClopen U hU) m') (S.restrictClopen U hU).zeroTimeMap
      (S.restrictClopen U hU).normalFrame p =
    EmbeddedTime.zeroColumns (n := 6) S.embedding (CollaredZero.retraction S m)
      S.zeroTimeMap S.normalFrame (S.restrictClopenZeroDiffeomorph U hU p).val := by
  let := S.zeroAtlas
  let := (S.restrictClopen U hU).zeroAtlas
  change OrthogonalFrameAppend.operator
      ((S.restrictClopen U hU).normalFrame.orthonormal p.val).val
      (EmbeddedTime.outwardNormal (n := 6) (S.restrictClopen U hU).embedding
        (CollaredZero.retraction (S.restrictClopen U hU) m')
          (S.restrictClopen U hU).zeroTimeMap p) =
    OrthogonalFrameAppend.operator
      (S.normalFrame.orthonormal (S.restrictClopenZeroDiffeomorph U hU p).val.val).val
      (EmbeddedTime.outwardNormal (n := 6) S.embedding (CollaredZero.retraction S m)
        S.zeroTimeMap (S.restrictClopenZeroDiffeomorph U hU p).val)
  rw [orthonormal S U hU p, outwardNormal S U hU m m' p]
  rfl

theorem sixFrame (m : S.Space) (m' : (S.restrictClopen U hU).Space)
    (p : (S.restrictClopen U hU).Zero) :
    letI := S.zeroAtlas; letI := (S.restrictClopen U hU).zeroAtlas;
    ∀ v : Vector (S.embedding.ambientDimension - 6),
      (CollaredZero.normalFrame (S.restrictClopen U hU) m').ambient p v =
      (CollaredZero.normalFrame S m).ambient (S.restrictClopenZeroDiffeomorph U hU p).val v := by
  let := S.zeroAtlas
  let := (S.restrictClopen U hU).zeroAtlas
  intro v
  have hQ : EmbeddedTime.normalCoordinates (n := 6) (S.restrictClopen U hU).embedding m' =
      EmbeddedTime.normalCoordinates (n := 6) S.embedding m := rfl
  have hc := zeroColumns S U hU m m' p
  have hv := congrArg
    (fun L : Vector ((S.embedding.ambientDimension - 7) + 1) →L[ℝ]
      Vector S.embedding.ambientDimension ↦
        L (EmbeddedTime.normalCoordinates (n := 6) S.embedding m v)) hc
  change EmbeddedTime.zeroColumns (n := 6) (S.restrictClopen U hU).embedding
      (CollaredZero.retraction (S.restrictClopen U hU) m') (S.restrictClopen U hU).zeroTimeMap
      (S.restrictClopen U hU).normalFrame p
      (EmbeddedTime.normalCoordinates (n := 6) (S.restrictClopen U hU).embedding m' v) =
    EmbeddedTime.zeroColumns (n := 6) S.embedding (CollaredZero.retraction S m)
      S.zeroTimeMap S.normalFrame (S.restrictClopenZeroDiffeomorph U hU p).val
      (EmbeddedTime.normalCoordinates (n := 6) S.embedding m v)
  rw [hQ]
  exact hv

end NoExoticSixSphere.CollaredZero.ClopenRestriction
