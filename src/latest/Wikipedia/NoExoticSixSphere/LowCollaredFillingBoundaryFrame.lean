import Wikipedia.NoExoticSixSphere.FramedEmbeddingReparametrization
import Wikipedia.NoExoticSixSphere.CollaredZeroComponentFrame
import Wikipedia.NoExoticSixSphere.LowCollaredFilling

/-!
# The full actual filling-boundary frame with a possibly disconnected seam

The literal boundary of the positive half retains its native transported
regular-fiber atlas. Its embedding is the restriction of the filling's
actual inclusion. Its full normal frame consists of the filling's
orthonormal normal columns and the negative unit time-gradient, with the
actual codimension coordinates. This last column is tangent to the half,
normal to the boundary, and has strictly negative time derivative.
None of these constructions or identities assumes connectedness or
simple connectivity of the seam, ambient state, or positive half.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.LowCollaredFillingBoundary

open GLOrthonormalization Stiefel Wikipedia.HopfProblem.DegreeCollapse

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)

local instance stateChartedSpace : ChartedSpace (Vector (6 + 1)) S.Space := S.atlas

local instance stateIsManifold : IsManifold (𝓡 (6 + 1)) ∞ S.Space := S.smooth

def retraction (m : S.Space) : S.embedding.TubularRetraction := by
  let : Nonempty S.Space := ⟨m⟩
  exact Classical.choice (S.embedding.nonempty_tubularRetraction S.normalFrame)

def embedding : letI := S.halfBoundaryAtlas; EuclideanEmbedding 6 S.HalfBoundary := by
  let := S.halfBoundaryAtlas
  let := S.zeroAtlas
  let eZ : EuclideanEmbedding 6 S.Zero := EmbeddedTime.zeroEmbedding (n := 6)
    S.embedding S.zeroTimeMap S.time_smooth S.time_regular
  exact eZ.reparametrize S.halfBoundaryDiffeomorph

theorem embedding_eq_filling_inclusion (p : S.HalfBoundary) :
    letI := S.halfBoundaryAtlas; letI := S.zeroAtlas;
    (embedding S).toFun p = S.framedFilling.inclusion p.val := rfl

def outwardNormal (m : S.Space) (p : S.HalfBoundary) : Vector S.embedding.ambientDimension :=
  EmbeddedTime.outwardNormal (n := 6) S.embedding (retraction S m) S.zeroTimeMap
    (S.halfBoundaryHomeomorph p)

theorem outwardNormal_norm (m : S.Space) (p : S.HalfBoundary) :
    ‖outwardNormal S m p‖ = 1 :=
  EmbeddedTime.outwardNormal_norm (n := 6) S.embedding (retraction S m) S.zeroTimeMap
    S.time_smooth S.time_regular (S.halfBoundaryHomeomorph p)

theorem outwardNormal_mem_half_tangent (m : S.Space) (p : S.HalfBoundary) :
    outwardNormal S m p ∈ (S.halfAmbientDerivative p.val).range := by
  rw [S.range_halfAmbientDerivative]
  exact EmbeddedTime.outwardNormal_mem_tangent (n := 6) S.embedding (retraction S m)
    S.zeroTimeMap (S.halfBoundaryHomeomorph p)

theorem outwardNormal_mem_boundary_normal (m : S.Space) (p : S.HalfBoundary) :
    letI := S.halfBoundaryAtlas; outwardNormal S m p ∈ (embedding S).normalFiber p := by
  let := S.halfBoundaryAtlas
  let := S.zeroAtlas
  let eZ : EuclideanEmbedding 6 S.Zero := EmbeddedTime.zeroEmbedding (n := 6)
    S.embedding S.zeroTimeMap S.time_smooth S.time_regular
  change outwardNormal S m p ∈ ((eZ.reparametrize S.halfBoundaryDiffeomorph).tangentImage p)ᗮ
  rw [eZ.reparametrize_tangentImage]
  change outwardNormal S m p ∈ (EmbeddedTime.zeroDerivative (n := 6) S.embedding
    S.zeroTimeMap S.time_smooth S.time_regular (S.halfBoundaryHomeomorph p)).rangeᗮ
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro _ ⟨v, rfl⟩
  exact (real_inner_comm _ _).trans (EmbeddedTime.outwardNormal_orthogonal_zero (n := 6)
    S.embedding (retraction S m) S.zeroTimeMap S.time_smooth S.time_regular
      (S.halfBoundaryHomeomorph p) v)

theorem outwardNormal_time_derivative_neg (m : S.Space) (p : S.HalfBoundary) :
    fderiv ℝ (EmbeddedTime.extension S.embedding (retraction S m) S.zeroTimeMap)
      (S.embedding.toFun p.val.val) (outwardNormal S m p) < 0 :=
  EmbeddedTime.extension_outward_neg (n := 6) S.embedding (retraction S m) S.zeroTimeMap
    S.time_smooth S.time_regular (S.halfBoundaryHomeomorph p)

theorem contMDiff_outwardNormal (m : S.Space) : letI := S.halfBoundaryAtlas;
    ContMDiff (𝓡 6) (𝓡 S.embedding.ambientDimension) ∞ (outwardNormal S m) := by
  let := S.halfBoundaryAtlas
  let := S.zeroAtlas
  have hn : ContMDiff (𝓡 6) (𝓡 S.embedding.ambientDimension) ∞
      (fun p : S.Zero ↦ EmbeddedTime.outwardNormal (n := 6) S.embedding (retraction S m)
        S.zeroTimeMap p) := EmbeddedTime.contMDiff_outwardNormal (n := 6) S.embedding
      (retraction S m) S.zeroTimeMap S.time_smooth S.time_regular
  exact hn.comp S.halfBoundaryDiffeomorph.contMDiff

def normalFrame (m : S.Space) : letI := S.halfBoundaryAtlas;
    SmoothRangeFrame (𝓡 6) (embedding S).normalProjection (embedding S).NormalModel := by
  let := S.halfBoundaryAtlas
  let := S.zeroAtlas
  let eZ : EuclideanEmbedding 6 S.Zero := EmbeddedTime.zeroEmbedding (n := 6)
    S.embedding S.zeroTimeMap S.time_smooth S.time_regular
  let aZ : SmoothRangeFrame (𝓡 6) eZ.normalProjection eZ.NormalModel :=
    EmbeddedTime.zeroNormalFrame (n := 6) S.embedding (retraction S m) S.zeroTimeMap
      S.time_smooth S.time_regular S.normalFrame m
  exact eZ.reparametrizeFrame S.halfBoundaryDiffeomorph aZ

def columns (m : S.Space) (p : S.HalfBoundary) :
    Vector ((S.embedding.ambientDimension - 7) + 1) →L[ℝ]
      Vector S.embedding.ambientDimension := by
  let := S.zeroAtlas
  let := S.halfChartedSpace
  let := S.framedFilling.topology
  let := S.framedFilling.atlas
  exact OrthogonalFrameAppend.operator (S.framedFilling.frame.orthonormal p.val).val
    (outwardNormal S m p)

theorem filling_orthonormal_boundary (p : S.HalfBoundary) :
    letI := S.zeroAtlas; letI := S.halfChartedSpace;
    letI := S.framedFilling.topology; letI := S.framedFilling.atlas;
    (S.framedFilling.frame.orthonormal p.val).val = (S.normalFrame.orthonormal p.val.val).val := by
  let := S.zeroAtlas
  let := S.halfChartedSpace
  let := S.framedFilling.topology
  let := S.framedFilling.atlas
  exact Orthonormalization.operator_congr_value S.framedFilling.frame.ambient
    S.normalFrame.ambient p.val p.val.val rfl

theorem columns_eq_zeroColumns (m : S.Space) (p : S.HalfBoundary) :
    columns S m p = EmbeddedTime.zeroColumns (n := 6) S.embedding (retraction S m)
      S.zeroTimeMap S.normalFrame (S.halfBoundaryHomeomorph p) := by
  let := S.zeroAtlas
  let := S.halfChartedSpace
  let := S.framedFilling.topology
  let := S.framedFilling.atlas
  change OrthogonalFrameAppend.operator (S.framedFilling.frame.orthonormal p.val).val
      (outwardNormal S m p) =
    OrthogonalFrameAppend.operator (S.normalFrame.orthonormal p.val.val).val
      (outwardNormal S m p)
  rw [filling_orthonormal_boundary]
  rfl

theorem normalFrame_ambient (m : S.Space) (p : S.HalfBoundary) :
    letI := S.halfBoundaryAtlas; ∀ v : Vector (S.embedding.ambientDimension - 6),
    (normalFrame S m).ambient p v = columns S m p
      (EmbeddedTime.normalCoordinates (n := 6) S.embedding m v) := by
  let := S.halfBoundaryAtlas
  intro v
  rw [columns_eq_zeroColumns]
  rfl

theorem normalFrame_norm (m : S.Space) (p : S.HalfBoundary) :
    letI := S.halfBoundaryAtlas; ∀ v, ‖(normalFrame S m).ambient p v‖ = ‖v‖ := by
  let := S.halfBoundaryAtlas
  exact EmbeddedTime.zeroNormalFrame_norm (n := 6) S.embedding (retraction S m)
    S.zeroTimeMap S.time_smooth S.time_regular S.normalFrame m (S.halfBoundaryHomeomorph p)

end NoExoticSixSphere.LowCollaredFillingBoundary
