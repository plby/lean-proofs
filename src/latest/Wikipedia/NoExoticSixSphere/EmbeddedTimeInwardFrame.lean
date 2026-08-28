import Wikipedia.NoExoticSixSphere.EmbeddedTimeCovector
import Wikipedia.NoExoticSixSphere.RegularTimeZeroNormalFrame
import Wikipedia.NoExoticSixSphere.OrthogonalFrameAppendReflection

/-!
# The actual boundary frame in negative-time graph coordinates

For a disk entering the nonnegative-time half, negative time has positive
outward radial derivative. Its covector pairs negatively with the inward
normal. The actual OUTWARD boundary frame is retained by an explicit
last-column reflection in its fixed normal-model coordinates. No boundary
framing is silently replaced by its opposite.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization Stiefel

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector (n + 1)) M]
  [IsManifold (𝓡 (n + 1)) ∞ M] (e : EuclideanEmbedding (n + 1) M)
  (r : e.TubularRetraction) (t : C(M, ℝ))
  (ht : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) t x))

def inwardNormal (p : {x : M // t x = 0}) : Vector e.ambientDimension :=
  -outwardNormal e r t p

def inwardTimeCovector (p : {x : M // t x = 0}) : Vector e.ambientDimension →L[ℝ] ℝ :=
  -timeCovector e r t p.val

theorem contMDiff_inwardNormal : letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 n) (𝓡 e.ambientDimension) ∞ (inwardNormal e r t) := by
  let := zeroAtlas t ht hreg
  exact (contMDiff_outwardNormal e r t ht hreg).neg

theorem contMDiff_inwardTimeCovector : letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 n) 𝓘(ℝ, Vector e.ambientDimension →L[ℝ] ℝ) ∞
      (inwardTimeCovector e r t) := by
  let := zeroAtlas t ht hreg
  exact ((contMDiff_timeCovector e r t ht).comp (contMDiff_zeroInclusion t ht hreg)).neg

theorem inwardTimeCovector_frame
    (a : SmoothRangeFrame (𝓡 (n + 1)) e.normalProjection e.NormalModel)
    (p : {x : M // t x = 0}) (v : e.NormalModel) :
    inwardTimeCovector e r t p (a.ambient p.val v) = 0 := by
  change -timeCovector e r t p.val (a.ambient p.val v) = 0
  rw [timeCovector_frame, neg_zero]

include ht hreg in
theorem inwardTimeCovector_inward_neg (p : {x : M // t x = 0}) :
    inwardTimeCovector e r t p (inwardNormal e r t p) < 0 := by
  change -timeCovector e r t p.val (-outwardNormal e r t p) < 0
  rw [map_neg, neg_neg]
  exact timeCovector_outward_neg e r t ht hreg p

def inwardNormalCoordinates (m : M) :
    Vector (e.ambientDimension - n) ≃L[ℝ] Vector ((e.ambientDimension - (n + 1)) + 1) :=
  (normalCoordinates (n := n) e m).toContinuousLinearEquiv.trans
    (OrthogonalFrameAppend.lastReflection (e.ambientDimension - (n + 1))).toContinuousLinearEquiv

theorem zeroNormalFrame_inward_columns
    (a : SmoothRangeFrame (𝓡 (n + 1)) e.normalProjection e.NormalModel)
    (m : M) (p : {x : M // t x = 0}) : letI := zeroAtlas t ht hreg;
    (zeroNormalFrame e r t ht hreg a m).ambient p =
      (OrthogonalFrameAppend.operator (a.orthonormal p.val).val (inwardNormal e r t p)).comp
        (inwardNormalCoordinates e m).toContinuousLinearMap := by
  let := zeroAtlas t ht hreg
  apply ContinuousLinearMap.ext
  intro v
  rw [zeroNormalFrame_ambient]
  change OrthogonalFrameAppend.operator (a.orthonormal p.val).val (outwardNormal e r t p)
      (normalCoordinates (n := n) e m v) =
    OrthogonalFrameAppend.operator (a.orthonormal p.val).val (-outwardNormal e r t p)
      (OrthogonalFrameAppend.lastReflection (e.ambientDimension - (n + 1))
        (normalCoordinates (n := n) e m v))
  have h := congrArg
    (fun L : Vector ((e.ambientDimension - (n + 1)) + 1) →L[ℝ]
      Vector e.ambientDimension ↦ L (normalCoordinates (n := n) e m v))
    (OrthogonalFrameAppend.operator_neg (a.orthonormal p.val).val (-outwardNormal e r t p))
  change OrthogonalFrameAppend.operator (a.orthonormal p.val).val (-(-outwardNormal e r t p))
      (normalCoordinates (n := n) e m v) =
    OrthogonalFrameAppend.operator (a.orthonormal p.val).val (-outwardNormal e r t p)
      (OrthogonalFrameAppend.lastReflection (e.ambientDimension - (n + 1))
        (normalCoordinates (n := n) e m v)) at h
  rw [neg_neg] at h
  exact h

end NoExoticSixSphere.EmbeddedTime
