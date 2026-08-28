import Wikipedia.NoExoticSixSphere.EmbeddedTimeNaturality
import Wikipedia.NoExoticSixSphere.RegularTimeZeroColumns
import Wikipedia.NoExoticSixSphere.LowSurgerySeamFrame
import Wikipedia.NoExoticSixSphere.EuclideanBlockProjection

/-!
# The actual time-gradient and outward six-boundary column at the surgery seam

The retained open neighborhood has exactly the old embedding with zero
coordinates appended and exactly the old time. Native differentiation
therefore identifies the intrinsic gradients. The outward unit column on
the native six-dimensional zero fiber has the same signed identification,
independently of both tubular retractions.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.LowSurgerySeam

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
open FramedAttachingProduct RoundedTrace NativeSurgery

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : Sphere d → M} (A : FramedAttachingProduct e a f)
  (hR : A.radius = 2) (T : TimeData A) (r : e.TubularRetraction)

theorem gradient_retainedBand : letI := boundaryChartedSpace A;
    ∀ (r' : (otherBoundaryEuclideanEmbedding A).TubularRetraction) (p : retainedTimeBand A T),
      EmbeddedTime.gradient (otherBoundaryEuclideanEmbedding A) r' (timeFunction A hR T)
        (retainedTimeMap A T p) =
      appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))
        (EmbeddedTime.gradient e r T.time p.val) := by
  let := boundaryChartedSpace A
  let := boundary_isManifold A
  intro r' p
  let J : Vector e.ambientDimension →ₗᵢ[ℝ]
      Vector (e.ambientDimension + (1 + (1 + (d + 1)))) :=
    ⟨(appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))).toLinearMap,
      norm_appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))⟩
  exact EmbeddedTime.gradient_natural e (otherBoundaryEuclideanEmbedding A) r r'
    T.time (timeFunction A hR T) T.smooth (contMDiff_timeFunction A hR T)
    (fun q : retainedTimeBand A T ↦ q.val) (retainedTimeMap A T) p
    (isLocalDiffeomorphAt_openSubset_val (I := 𝓡 7) (retainedTimeBand A T) p)
    (isLocalDiffeomorphAt_retainedTimeMap A T p) J
    (embedding_retainedBand A T) (timeFunction_retainedTimeMap A hR T)

theorem outwardNormal_zero : letI := boundaryChartedSpace A;
    letI := originalZeroAtlas A T; letI := resultZeroAtlas A hR T;
    ∀ (r' : (otherBoundaryEuclideanEmbedding A).TubularRetraction) (p : OriginalZero A T),
      EmbeddedTime.outwardNormal (n := 6) (otherBoundaryEuclideanEmbedding A) r'
        (resultTimeMap A hR T) (zeroDiffeomorph A hR T p) =
      appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))
        (EmbeddedTime.outwardNormal (n := 6) e r (originalTimeMap A T) p) := by
  let := boundaryChartedSpace A
  let := originalZeroAtlas A T
  let := resultZeroAtlas A hR T
  intro r' p
  change -NormedSpace.normalize
      (EmbeddedTime.gradient (otherBoundaryEuclideanEmbedding A) r' (timeFunction A hR T)
        (retainedTimeMap A T (originalZeroToBand A T p))) =
    appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))
      (-NormedSpace.normalize (EmbeddedTime.gradient e r T.time p.val))
  rw [gradient_retainedBand A hR T r]
  change -NormedSpace.normalize
      (appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))
        (EmbeddedTime.gradient e r T.time p.val)) =
    appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))
      (-NormedSpace.normalize (EmbeddedTime.gradient e r T.time p.val))
  simp only [NormedSpace.normalize, norm_appendZeroMap, map_neg, map_smul]

end NoExoticSixSphere.LowSurgerySeam
