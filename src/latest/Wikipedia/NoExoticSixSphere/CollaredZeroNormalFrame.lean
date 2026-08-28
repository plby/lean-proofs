import Wikipedia.NoExoticSixSphere.RegularTimeZeroNormalFrame
import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenBoundary

/-!
# The actual induced six-frame on a collared seven-state's native zero atlas

The state supplies its compact seven-manifold, original embedding, normal
frame and regular time. A tubular retraction is constructed from those
data. The native zero embedding is framed by the original normal columns
and the negative unit intrinsic time-gradient, in its actual normal model.
No boundary frame or smooth structure is supplied as an additional input.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CollaredZero

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)

local instance : ChartedSpace (Vector (6 + 1)) S.Space := S.atlas

local instance : IsManifold (𝓡 (6 + 1)) ∞ S.Space := S.smooth

def embedding : letI := S.zeroAtlas; EuclideanEmbedding 6 S.Zero :=
  EmbeddedTime.zeroEmbedding (n := 6) S.embedding S.zeroTimeMap S.time_smooth S.time_regular

def retraction (m : S.Space) : S.embedding.TubularRetraction := by
  let : Nonempty S.Space := ⟨m⟩
  exact Classical.choice (S.embedding.nonempty_tubularRetraction S.normalFrame)

def normalFrame (m : S.Space) : letI := S.zeroAtlas;
    SmoothRangeFrame (𝓡 6) (embedding S).normalProjection (embedding S).NormalModel :=
  EmbeddedTime.zeroNormalFrame (n := 6) S.embedding (retraction S m) S.zeroTimeMap S.time_smooth
    S.time_regular S.normalFrame m

theorem normalFrame_ambient (m : S.Space) (p : S.Zero) : letI := S.zeroAtlas;
    ∀ v, (normalFrame S m).ambient p v =
      EmbeddedTime.zeroColumns (n := 6) S.embedding (retraction S m) S.zeroTimeMap S.normalFrame p
        (EmbeddedTime.normalCoordinates (n := 6) S.embedding m v) := by
  let := S.zeroAtlas
  exact EmbeddedTime.zeroNormalFrame_ambient (n := 6) S.embedding (retraction S m) S.zeroTimeMap
    S.time_smooth S.time_regular S.normalFrame m p

theorem normalFrame_norm (m : S.Space) (p : S.Zero) : letI := S.zeroAtlas;
    ∀ v, ‖(normalFrame S m).ambient p v‖ = ‖v‖ := by
  let := S.zeroAtlas
  exact EmbeddedTime.zeroNormalFrame_norm (n := 6) S.embedding (retraction S m) S.zeroTimeMap
    S.time_smooth S.time_regular S.normalFrame m p

theorem normalFrame_point_independent (m m' : S.Space) : letI := S.zeroAtlas;
    normalFrame S m' = normalFrame S m := by
  let := S.zeroAtlas
  apply SmoothRangeFrame.eq_of_ambient_eq
  intro p
  apply ContinuousLinearMap.ext
  intro v
  rw [normalFrame_ambient, normalFrame_ambient,
    EmbeddedTime.normalCoordinates_point_independent S.embedding m m']
  exact congrArg
    (fun L : Vector ((S.embedding.ambientDimension - 7) + 1) →L[ℝ]
      Vector S.embedding.ambientDimension ↦ L (EmbeddedTime.normalCoordinates S.embedding m v))
    (EmbeddedTime.zeroColumns_retraction_independent (n := 6) S.embedding (retraction S m)
      S.zeroTimeMap S.time_smooth S.normalFrame (retraction S m') p)

end NoExoticSixSphere.CollaredZero
