import Wikipedia.NoExoticSixSphere.CollaredZeroNormalFrame
import Wikipedia.NoExoticSixSphere.EmbeddedTimeNaturality
import Wikipedia.NoExoticSixSphere.CollaredSeamFrame

/-!
# Restricting to the actual boundary component preserves its induced six-frame

The inherited open-subset atlas and the restricted original embedding have
the same intrinsic time-gradient. The restricted seven-frame has the same
orthonormalized columns. Thus the full induced six-frame agrees under the
native component zero diffeomorphism, even with independent tubular choices.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere

open GLOrthonormalization Stiefel Wikipedia.HopfProblem.DegreeCollapse

theorem Stiefel.Orthonormalization.operator_congr_value {X Y : Type*} {N k : ℕ}
    (A : X → Vector k →L[ℝ] Vector N) (B : Y → Vector k →L[ℝ] Vector N)
    (x : X) (y : Y) (h : A x = B y) :
    Orthonormalization.operator A x = Orthonormalization.operator B y :=
  congrArg (fun L : Vector k →L[ℝ] Vector N ↦
    Orthonormalization.operator (fun _ : Unit ↦ L) ()) h

namespace CollaredSeam

variable {B : Type} [TopologicalSpace B] [PathConnectedSpace B]
  (S : LowCollaredSevenState B) (b : B)

local instance componentChartedSpace : ChartedSpace (Vector (6 + 1)) S.Space := S.atlas

local instance componentIsManifold : IsManifold (𝓡 (6 + 1)) ∞ S.Space := S.smooth

local instance componentLocallyPathConnected : LocallyPathConnectedSpace S.Space :=
  ChartedSpace.locallyPathConnectedSpace (Vector 7) S.Space

theorem component_gradient (m : S.Space) (m' x : (S.component b).Space) :
    EmbeddedTime.gradient (S.component b).embedding (CollaredZero.retraction (S.component b) m')
      (S.component b).time x =
    EmbeddedTime.gradient S.embedding (CollaredZero.retraction S m) S.time x.val := by
  exact EmbeddedTime.gradient_natural S.embedding (S.component b).embedding
    (CollaredZero.retraction S m) (CollaredZero.retraction (S.component b) m')
    S.time (S.component b).time S.time_smooth (S.component b).time_smooth
    (fun q : S.collar.boundaryComponent b ↦ q.val) id x
    (isLocalDiffeomorphAt_openSubset_val (I := 𝓡 7) (S.collar.boundaryComponent b) x)
    ((Diffeomorph.refl (𝓡 7) (S.collar.boundaryComponent b) ∞).isLocalDiffeomorph x)
    (LinearIsometryEquiv.refl ℝ (Vector S.embedding.ambientDimension)).toLinearIsometry
    (fun _ ↦ rfl) (fun _ ↦ rfl)

theorem component_outwardNormal (m : S.Space) (m' : (S.component b).Space)
    (p : (S.component b).Zero) : letI := S.zeroAtlas; letI := (S.component b).zeroAtlas;
    EmbeddedTime.outwardNormal (n := 6) (S.component b).embedding
      (CollaredZero.retraction (S.component b) m') (S.component b).zeroTimeMap p =
    EmbeddedTime.outwardNormal (n := 6) S.embedding (CollaredZero.retraction S m)
      S.zeroTimeMap (S.componentZeroDiffeomorph b p) := by
  let := S.zeroAtlas
  let := (S.component b).zeroAtlas
  change -NormedSpace.normalize
      (EmbeddedTime.gradient (S.component b).embedding (CollaredZero.retraction (S.component b) m')
        (S.component b).time p.val) =
    -NormedSpace.normalize (EmbeddedTime.gradient S.embedding (CollaredZero.retraction S m)
      S.time p.val.val)
  exact congrArg (fun z : Vector S.embedding.ambientDimension ↦ -NormedSpace.normalize z)
    (component_gradient S b m m' p.val)

theorem component_orthonormal (p : (S.component b).Zero) :
    letI := S.zeroAtlas; letI := (S.component b).zeroAtlas;
    ((S.component b).normalFrame.orthonormal p.val).val =
      (S.normalFrame.orthonormal (S.componentZeroDiffeomorph b p).val).val := by
  let := S.zeroAtlas
  let := (S.component b).zeroAtlas
  exact Orthonormalization.operator_congr_value (S.component b).normalFrame.ambient
    S.normalFrame.ambient p.val (S.componentZeroDiffeomorph b p).val (component_frame S b p)

theorem component_zeroColumns (m : S.Space) (m' : (S.component b).Space)
    (p : (S.component b).Zero) : letI := S.zeroAtlas; letI := (S.component b).zeroAtlas;
    EmbeddedTime.zeroColumns (n := 6) (S.component b).embedding
      (CollaredZero.retraction (S.component b) m') (S.component b).zeroTimeMap
      (S.component b).normalFrame p =
    EmbeddedTime.zeroColumns (n := 6) S.embedding (CollaredZero.retraction S m)
      S.zeroTimeMap S.normalFrame (S.componentZeroDiffeomorph b p) := by
  let := S.zeroAtlas
  let := (S.component b).zeroAtlas
  change OrthogonalFrameAppend.operator ((S.component b).normalFrame.orthonormal p.val).val
      (EmbeddedTime.outwardNormal (n := 6) (S.component b).embedding
        (CollaredZero.retraction (S.component b) m') (S.component b).zeroTimeMap p) =
    OrthogonalFrameAppend.operator
      (S.normalFrame.orthonormal (S.componentZeroDiffeomorph b p).val).val
      (EmbeddedTime.outwardNormal (n := 6) S.embedding (CollaredZero.retraction S m)
        S.zeroTimeMap (S.componentZeroDiffeomorph b p))
  rw [component_orthonormal S b p, component_outwardNormal S b m m' p]
  rfl

theorem component_sixFrame (m : S.Space) (m' : (S.component b).Space)
    (p : (S.component b).Zero) : letI := S.zeroAtlas; letI := (S.component b).zeroAtlas;
    ∀ v : Vector (S.embedding.ambientDimension - 6),
      (CollaredZero.normalFrame (S.component b) m').ambient p v =
      (CollaredZero.normalFrame S m).ambient (S.componentZeroDiffeomorph b p) v := by
  let := S.zeroAtlas
  let := (S.component b).zeroAtlas
  intro v
  have hQ : EmbeddedTime.normalCoordinates (n := 6) (S.component b).embedding m' =
      EmbeddedTime.normalCoordinates (n := 6) S.embedding m := rfl
  have hc := component_zeroColumns S b m m' p
  have hv := congrArg
    (fun L : Vector ((S.embedding.ambientDimension - 7) + 1) →L[ℝ]
      Vector S.embedding.ambientDimension ↦
        L (EmbeddedTime.normalCoordinates (n := 6) S.embedding m v)) hc
  change EmbeddedTime.zeroColumns (n := 6) (S.component b).embedding
      (CollaredZero.retraction (S.component b) m') (S.component b).zeroTimeMap
      (S.component b).normalFrame p
      (EmbeddedTime.normalCoordinates (n := 6) (S.component b).embedding m' v) =
    EmbeddedTime.zeroColumns (n := 6) S.embedding (CollaredZero.retraction S m)
      S.zeroTimeMap S.normalFrame (S.componentZeroDiffeomorph b p)
      (EmbeddedTime.normalCoordinates (n := 6) S.embedding m v)
  rw [hQ]
  exact hv

end CollaredSeam
end NoExoticSixSphere
