import Wikipedia.NoExoticSixSphere.RoundedTraceVerticalCutoff

/-!
# A global smooth tangent correction with unit time component near the ends

Division by the time speed is performed only where it is positive. At all
other points the cutoff is identically zero nearby, so the total formula is
smooth. Its values are always in the actual graph tangent image.
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

def cutoffTimeTangent (p : ambientSet A) : TimeGraphSpace (e := e) :=
  letI := traceChartedSpace A
  (verticalFrameCutoff A p / graphTimeSpeed A p) • graphTimeTangent A p

theorem contMDiff_cutoffTimeTangent : letI := traceChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 6)) 𝓘(ℝ, TimeGraphSpace (e := e)) ∞
      (cutoffTimeTangent A) := by
  let := traceChartedSpace A
  intro p
  by_cases hp : p ∈ timeRegularNeighborhood A
  · exact ((verticalFrameCutoff A).contMDiff.contMDiffAt.div₀
      (contMDiff_graphTimeSpeed A).contMDiffAt (ne_of_gt hp)).smul
        (contMDiff_graphTimeTangent A).contMDiffAt
  · have hzero := (verticalFrameCutoff_eventually_zero A).filter_mono (nhds_le_nhdsSet hp)
    have he : cutoffTimeTangent A =ᶠ[𝓝 p] (fun _ ↦ 0) := by
      filter_upwards [hzero] with q hq
      simp only [cutoffTimeTangent, hq, zero_div, zero_smul]
    exact he.contMDiffAt_iff.mpr contMDiffAt_const

theorem cutoffTimeTangent_mem (p : ambientSet A) :
    cutoffTimeTangent A p ∈ (timeGraphDifferential A p).range :=
  Submodule.smul_mem _ _ (graphTimeTangent_mem A p)

theorem normalProjection_cutoffTimeTangent (p : ambientSet A) :
    timeGraphNormalProjection A p (cutoffTimeTangent A p) = 0 :=
  Submodule.starProjection_orthogonal_apply_eq_zero (cutoffTimeTangent_mem A p)

theorem timeFunctional_cutoffTimeTangent (p : ambientSet A) : letI := traceChartedSpace A;
    timeGraphTimeFunctional (e := e) (cutoffTimeTangent A p) = verticalFrameCutoff A p := by
  let := traceChartedSpace A
  by_cases hp : p ∈ timeRegularNeighborhood A
  · change timeGraphTimeFunctional (e := e)
      ((verticalFrameCutoff A p / graphTimeSpeed A p) • graphTimeTangent A p) = _
    rw [map_smul]
    change (verticalFrameCutoff A p / graphTimeSpeed A p) * graphTimeSpeed A p = _
    exact div_mul_cancel₀ _ (ne_of_gt hp)
  · rw [cutoffTimeTangent, verticalFrameCutoff_zero A hp, zero_div, zero_smul, map_zero]

theorem timeFunctional_cutoffTimeTangent_boundary (p : Boundary A) :
    timeGraphTimeFunctional (e := e) (cutoffTimeTangent A p.val) = 1 := by
  let := traceChartedSpace A
  rw [timeFunctional_cutoffTimeTangent, verticalFrameCutoff_one_boundary]

theorem timeFunctional_cutoffTimeTangent_eventually_one :
    ∀ᶠ p in 𝓝ˢ (range (Subtype.val : Boundary A → ambientSet A)),
      timeGraphTimeFunctional (e := e) (cutoffTimeTangent A p) = 1 := by
  let := traceChartedSpace A
  filter_upwards [verticalFrameCutoff_eventually_one A] with p hp
  rw [timeFunctional_cutoffTimeTangent, hp]

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
