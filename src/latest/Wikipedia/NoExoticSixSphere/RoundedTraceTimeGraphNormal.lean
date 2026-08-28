import Wikipedia.NoExoticSixSphere.RoundedTraceTimeGraph
import Wikipedia.NoExoticSixSphere.ImmersionNormalProjection

/-!
# A smooth new normal column for the time graph

Projecting the positive time axis into the graph normal space never gives
zero: a pure time vector cannot be tangent to the graph of an immersion.
Normalization therefore gives a global smooth unit normal column.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def timeGraphNormalProjection (p : ambientSet A) :
    TimeGraphSpace (e := e) →L[ℝ] TimeGraphSpace (e := e) :=
  (timeGraphDifferential A p).rangeᗮ.starProjection

theorem contMDiff_timeGraphNormalProjection : letI := traceChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 6))
      𝓘(ℝ, TimeGraphSpace (e := e) →L[ℝ] TimeGraphSpace (e := e)) ∞
      (timeGraphNormalProjection A) := by
  let := traceChartedSpace A
  let := trace_isManifold A
  exact ImmersionNormalProjection.contMDiff_normalProjection
    (ProductHalfSpace.model (Vector 6)) (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Vector 6))
    (contMDiff_timeGraph A) (injective_timeGraphDifferential A)

def timeGraphTimeUnit : TimeGraphSpace (e := e) :=
  (timeGraphCoordinates (e := e)).symm (1, 0)

theorem timeGraphTimeUnit_not_tangent (p : ambientSet A) :
    timeGraphTimeUnit (e := e) ∉ (timeGraphDifferential A p).range := by
  rintro ⟨v, hv⟩
  have he := congrArg (timeGraphCoordinates (e := e)) hv
  have hc := congrArg
    (fun D : (ℝ × Vector 6) →L[ℝ] (ℝ × Vector (e.ambientDimension + 6)) ↦ D v)
    (timeGraphDifferential_coordinates A p)
  have hpair : (bordismTimeDifferential A p v, traceAmbientDerivative A p v) = (1, 0) :=
    hc.symm.trans he
  have hz : v = 0 := (injective_traceAmbientDerivative A p)
    ((congrArg Prod.snd hpair).trans (map_zero _).symm)
  have hfirst := congrArg Prod.fst hpair
  exact zero_ne_one (by simpa only [hz, map_zero, Prod.fst] using hfirst)

theorem timeGraph_projectedTime_ne_zero (p : ambientSet A) :
    timeGraphNormalProjection A p (timeGraphTimeUnit (e := e)) ≠ 0 := by
  intro hz
  have hm : timeGraphTimeUnit (e := e) ∈ (timeGraphDifferential A p).rangeᗮ.starProjection.ker :=
    hz
  rw [Submodule.ker_starProjection, Submodule.orthogonal_orthogonal] at hm
  exact timeGraphTimeUnit_not_tangent A p hm

def timeGraphNewNormal (p : ambientSet A) : TimeGraphSpace (e := e) :=
  NormedSpace.normalize (timeGraphNormalProjection A p (timeGraphTimeUnit (e := e)))

theorem contMDiff_timeGraphNewNormal : letI := traceChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 6)) 𝓘(ℝ, TimeGraphSpace (e := e)) ∞
      (timeGraphNewNormal A) := by
  let := traceChartedSpace A
  exact contMDiff_normalize ((contMDiff_timeGraphNormalProjection A).clm_apply contMDiff_const)
    (timeGraph_projectedTime_ne_zero A)

theorem norm_timeGraphNewNormal (p : ambientSet A) : ‖timeGraphNewNormal A p‖ = 1 :=
  NormedSpace.norm_normalize (timeGraph_projectedTime_ne_zero A p)

theorem timeGraphNewNormal_mem (p : ambientSet A) :
    timeGraphNewNormal A p ∈ (timeGraphDifferential A p).rangeᗮ :=
  (timeGraphDifferential A p).rangeᗮ.smul_mem _
    ((timeGraphDifferential A p).rangeᗮ.starProjection_apply_mem _)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
