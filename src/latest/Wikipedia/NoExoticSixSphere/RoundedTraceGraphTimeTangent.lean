import Wikipedia.NoExoticSixSphere.RoundedTraceGraphBoundaryFrameHomotopy

/-!
# A smooth tangent direction for time near the slab ends

The tangential projection of the time axis has time component equal to its
squared norm. It is nonzero wherever time is regular, in particular along
the entire native boundary. No noncriticality in the interior is assumed.
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

def timeGraphTimeFunctional : TimeGraphSpace (e := e) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (Vector (e.ambientDimension + 6))).comp
    (timeGraphCoordinates (e := e)).toContinuousLinearMap

theorem timeGraphTimeFunctional_eq_inner (v : TimeGraphSpace (e := e)) :
    timeGraphTimeFunctional (e := e) v = inner ℝ (timeGraphTimeUnit (e := e)) v := by
  change v.fst = inner ℝ (WithLp.toLp 2 ((1 : ℝ), (0 : Vector _))) v
  simp only [WithLp.prod_inner_apply, Real.inner_apply, inner_zero_left, one_mul, add_zero]
  rfl

theorem timeGraphTimeFunctional_differential (p : ambientSet A) (v : ℝ × Vector 6) :
    timeGraphTimeFunctional (e := e) (timeGraphDifferential A p v) =
      bordismTimeDifferential A p v := by
  rw [timeGraphDifferential_apply]
  rfl

def graphTimeTangent (p : ambientSet A) : TimeGraphSpace (e := e) :=
  timeGraphTimeUnit (e := e) - timeGraphNormalProjection A p (timeGraphTimeUnit (e := e))

theorem graphTimeTangent_eq_projection (p : ambientSet A) :
    graphTimeTangent A p = (timeGraphDifferential A p).range.starProjection
      (timeGraphTimeUnit (e := e)) := by
  rw [graphTimeTangent, timeGraphNormalProjection, Submodule.starProjection_orthogonal_val,
    sub_sub_cancel]

theorem graphTimeTangent_mem (p : ambientSet A) :
    graphTimeTangent A p ∈ (timeGraphDifferential A p).range := by
  rw [graphTimeTangent_eq_projection]
  exact (timeGraphDifferential A p).range.starProjection_apply_mem _

theorem contMDiff_graphTimeTangent : letI := traceChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 6)) 𝓘(ℝ, TimeGraphSpace (e := e)) ∞
      (graphTimeTangent A) := by
  let := traceChartedSpace A
  exact contMDiff_const.sub ((contMDiff_timeGraphNormalProjection A).clm_apply contMDiff_const)

def graphTimeSpeed (p : ambientSet A) : ℝ :=
  timeGraphTimeFunctional (e := e) (graphTimeTangent A p)

theorem contMDiff_graphTimeSpeed : letI := traceChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 6)) 𝓘(ℝ, ℝ) ∞ (graphTimeSpeed A) := by
  let := traceChartedSpace A
  exact (timeGraphTimeFunctional (e := e)).contDiff.contMDiff.comp (contMDiff_graphTimeTangent A)

theorem continuous_graphTimeSpeed : Continuous (graphTimeSpeed A) := by
  let := traceChartedSpace A
  exact (contMDiff_graphTimeSpeed A).continuous

theorem graphTimeSpeed_eq_norm_sq (p : ambientSet A) :
    graphTimeSpeed A p = ‖graphTimeTangent A p‖ ^ 2 := by
  let K := (timeGraphDifferential A p).range
  let u := timeGraphTimeUnit (e := e)
  have he := K.inner_right_of_mem_orthogonal (K.starProjection_apply_mem u)
    (K.sub_starProjection_mem_orthogonal u)
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at he
  change inner ℝ (K.starProjection u) u - ‖K.starProjection u‖ ^ 2 = 0 at he
  rw [graphTimeSpeed, timeGraphTimeFunctional_eq_inner, graphTimeTangent_eq_projection,
    real_inner_comm]
  exact sub_eq_zero.mp he

theorem graphTimeSpeed_nonneg (p : ambientSet A) : 0 ≤ graphTimeSpeed A p := by
  rw [graphTimeSpeed_eq_norm_sq]
  exact sq_nonneg _

theorem graphTimeTangent_ne_zero (p : ambientSet A)
    (hreg : Surjective (bordismTimeDifferential A p)) : graphTimeTangent A p ≠ 0 := by
  intro hz
  rw [graphTimeTangent_eq_projection] at hz
  have hn : timeGraphTimeUnit (e := e) ∈
      (timeGraphDifferential A p).range.starProjection.ker := hz
  rw [Submodule.ker_starProjection] at hn
  obtain ⟨v, hv⟩ := hreg 1
  have he := (timeGraphDifferential A p).range.inner_right_of_mem_orthogonal ⟨v, rfl⟩ hn
  change inner ℝ (timeGraphDifferential A p v) (timeGraphTimeUnit (e := e)) = 0 at he
  rw [real_inner_comm, ← timeGraphTimeFunctional_eq_inner,
    timeGraphTimeFunctional_differential, hv] at he
  exact one_ne_zero he

theorem graphTimeSpeed_pos_boundary (p : Boundary A) : 0 < graphTimeSpeed A p.val := by
  rw [graphTimeSpeed_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr
    (graphTimeTangent_ne_zero A p.val (bordismTimeDifferential_surjective A p)))

def timeRegularNeighborhood : Set (ambientSet A) := {p | 0 < graphTimeSpeed A p}

theorem isOpen_timeRegularNeighborhood : IsOpen (timeRegularNeighborhood A) :=
  isOpen_lt continuous_const (continuous_graphTimeSpeed A)

theorem boundary_mem_timeRegularNeighborhood (p : Boundary A) :
    p.val ∈ timeRegularNeighborhood A := graphTimeSpeed_pos_boundary A p

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
