import Wikipedia.NoExoticSixSphere.RegularTimeZeroColumns
import Wikipedia.NoExoticSixSphere.OrthonormalRangeFrame
import Wikipedia.HopfProblem.DegreeCollapseSevenInducedEndNormalFraming

/-!
# The induced normal frame in the actual zero-fiber embedding's normal model

The original columns and the negative unit time-gradient are reindexed
into the actual Euclidean normal model of the native zero-fiber embedding.
The resulting smooth range frame is orthonormal, has the full normal range,
and is independent of the tubular retraction used to define the gradient.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector (n + 1)) M]
  [IsManifold (𝓡 (n + 1)) ∞ M] (e : EuclideanEmbedding (n + 1) M)
  (r : e.TubularRetraction) (t : C(M, ℝ))
  (ht : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) t x))
  (a : SmoothRangeFrame (𝓡 (n + 1)) e.normalProjection e.NormalModel)

theorem zeroNormalDimension (m : M) :
    e.ambientDimension - n = (e.ambientDimension - (n + 1)) + 1 := by
  have hN := e.dimension_le_ambient m
  omega

def normalCoordinates (m : M) : Vector (e.ambientDimension - n) ≃ₗᵢ[ℝ]
    Vector ((e.ambientDimension - (n + 1)) + 1) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (zeroNormalDimension e m))

theorem normalCoordinates_point_independent (m m' : M) :
    normalCoordinates e m' = normalCoordinates e m := rfl

def zeroNormalFrame (m : M) : letI := zeroAtlas t ht hreg;
    SmoothRangeFrame (𝓡 n) (zeroEmbedding e t ht hreg).normalProjection
      (zeroEmbedding e t ht hreg).NormalModel := by
  let := zeroAtlas t ht hreg
  let F (p : {x : M // t x = 0}) :=
    (zeroColumns e r t a p).comp
      (normalCoordinates e m).toContinuousLinearEquiv.toContinuousLinearMap
  apply NormalColumns.normalFraming (zeroEmbedding e t ht hreg) F
  · intro p v
    exact (zeroColumns_norm e r t ht hreg a p (normalCoordinates e m v)).trans
      ((normalCoordinates e m).norm_map v)
  · exact (contMDiff_zeroColumns e r t ht hreg a).clm_comp contMDiff_const
  · intro p
    change (F p).range = ((zeroEmbedding e t ht hreg).normalProjection p).range
    have hF : (F p).range = (zeroColumns e r t a p).range :=
      LinearMap.range_comp_of_range_eq_top _
        (LinearMap.range_eq_top.mpr (normalCoordinates e m).surjective)
    exact hF.trans ((zeroColumns_range e r t ht hreg a p).trans
      ((zeroEmbedding e t ht hreg).range_normalProjection p).symm)

theorem zeroNormalFrame_ambient (m : M) (p : {x : M // t x = 0}) :
    letI := zeroAtlas t ht hreg;
    ∀ v, (zeroNormalFrame e r t ht hreg a m).ambient p v =
      zeroColumns e r t a p (normalCoordinates e m v) := by
  let := zeroAtlas t ht hreg
  intro v
  rfl

theorem zeroNormalFrame_norm (m : M) (p : {x : M // t x = 0}) :
    letI := zeroAtlas t ht hreg;
    ∀ v, ‖(zeroNormalFrame e r t ht hreg a m).ambient p v‖ = ‖v‖ := by
  let := zeroAtlas t ht hreg
  intro v
  rw [zeroNormalFrame_ambient]
  exact (zeroColumns_norm e r t ht hreg a p (normalCoordinates e m v)).trans
    ((normalCoordinates e m).norm_map v)

theorem zeroNormalFrame_retraction_independent (r' : e.TubularRetraction) (m : M) :
    letI := zeroAtlas t ht hreg;
    zeroNormalFrame e r' t ht hreg a m = zeroNormalFrame e r t ht hreg a m := by
  let := zeroAtlas t ht hreg
  apply SmoothRangeFrame.eq_of_ambient_eq
  intro p
  apply ContinuousLinearMap.ext
  intro v
  rw [zeroNormalFrame_ambient, zeroNormalFrame_ambient]
  simp only [zeroColumns, outwardNormal, gradient_retraction_independent e r t r' ht p.val]
  rfl

end NoExoticSixSphere.EmbeddedTime
