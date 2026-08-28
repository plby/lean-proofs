import Wikipedia.NoExoticSixSphere.RoundedTraceTransverseSplitting
import Wikipedia.NoExoticSixSphere.ManifoldFrameTubeDerivative

/-!
# The actual vertical frame-displacement map

Its zero-section differential is the checked tangent/transverse isomorphism.
It preserves time on a whole base neighborhood of the native boundary, for
every fiber vector. Injectivity on a uniform tube is a separate obligation.
-/

noncomputable section

open Function Set Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def verticalTube (q : ambientSet A × TimeGraphFrameSpace (e := e)) : TimeGraphSpace (e := e) :=
  timeGraph A q.1 + verticalFrame A q.1 q.2

theorem verticalTube_core (p : ambientSet A) : verticalTube A (p, 0) = timeGraph A p := by
  rw [verticalTube, map_zero, add_zero]

theorem contMDiff_verticalTube : letI := traceChartedSpace A;
    ContMDiff ((ProductHalfSpace.model (Vector 6)).prod 𝓘(ℝ, TimeGraphFrameSpace (e := e)))
      𝓘(ℝ, TimeGraphSpace (e := e)) ∞ (verticalTube A) := by
  let := traceChartedSpace A
  exact ((contMDiff_timeGraph A).comp contMDiff_fst).add
    (((contMDiff_verticalFrame A).comp contMDiff_fst).clm_apply contMDiff_snd)

theorem continuous_verticalTube : Continuous (verticalTube A) := by
  let := traceChartedSpace A
  exact (contMDiff_verticalTube A).continuous

def verticalTubeDifferential (q : ambientSet A × TimeGraphFrameSpace (e := e)) :
    ((ℝ × Vector 6) × TimeGraphFrameSpace (e := e)) →L[ℝ] TimeGraphSpace (e := e) :=
  letI := traceChartedSpace A
  mvfderiv ((ProductHalfSpace.model (Vector 6)).prod 𝓘(ℝ, TimeGraphFrameSpace (e := e)))
    (verticalTube A) q

theorem verticalTubeDifferential_core (p : ambientSet A) :
    verticalTubeDifferential A (p, 0) = transverseSum A p := by
  let := traceChartedSpace A
  exact mvfderiv_frameTube_core p ((contMDiff_timeGraph A).mdifferentiableAt (by simp))
    ((contMDiff_verticalFrame A).mdifferentiableAt (by simp))

theorem bijective_verticalTubeDifferential_core (p : ambientSet A) :
    Bijective (verticalTubeDifferential A (p, 0)) := by
  rw [verticalTubeDifferential_core]
  exact ⟨injective_transverseSum A p, surjective_transverseSum A p⟩

theorem verticalTube_time (p : ambientSet A) (v : TimeGraphFrameSpace (e := e)) :
    timeGraphTimeFunctional (e := e) (verticalTube A (p, v)) =
      bordismTime A p + timeGraphTimeFunctional (e := e) (verticalFrame A p v) := by
  rw [verticalTube, map_add]
  rfl

theorem verticalTube_time_boundary (p : Boundary A) (v : TimeGraphFrameSpace (e := e)) :
    timeGraphTimeFunctional (e := e) (verticalTube A (p.val, v)) = bordismTime A p.val := by
  rw [verticalTube_time, verticalFrame_time_zero_boundary, add_zero]

theorem verticalTube_eventually_time_eq :
    ∀ᶠ p in 𝓝ˢ (range (Subtype.val : Boundary A → ambientSet A)), ∀ v,
      timeGraphTimeFunctional (e := e) (verticalTube A (p, v)) = bordismTime A p := by
  filter_upwards [verticalFrame_eventually_time_zero A] with p hp v
  rw [verticalTube_time, hp v, add_zero]

theorem exists_verticalTube_time_neighborhood :
    ∃ U : Set (ambientSet A), IsOpen U ∧ range (Subtype.val : Boundary A → ambientSet A) ⊆ U ∧
      ∀ p ∈ U, ∀ v, timeGraphTimeFunctional (e := e) (verticalTube A (p, v)) = bordismTime A p :=
  eventually_nhdsSet_iff_exists.mp (verticalTube_eventually_time_eq A)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
