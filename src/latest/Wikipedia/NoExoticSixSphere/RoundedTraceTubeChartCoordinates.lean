import Wikipedia.NoExoticSixSphere.RoundedTraceVerticalTubeRegularity
import Wikipedia.NoExoticSixSphere.ManifoldChartInterior

/-!
# Half-space coordinates for the actual tube source

Only a fixed product reassociation is applied to the native extended charts.
The resulting first coordinate is nonnegative; zero is exactly the trace
boundary and positivity is exactly its interior, in any valid source chart.
-/

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def tubeModelCoordinates : ((ℝ × Vector 6) × TimeGraphFrameSpace (e := e)) ≃L[ℝ]
    (ℝ × (Vector 6 × TimeGraphFrameSpace (e := e))) :=
  ContinuousLinearEquiv.prodAssoc ℝ ℝ (Vector 6) (TimeGraphFrameSpace (e := e))

def tubeChart (q : ambientSet A × TimeGraphFrameSpace (e := e)) :
    ambientSet A × TimeGraphFrameSpace (e := e) →
      ℝ × (Vector 6 × TimeGraphFrameSpace (e := e)) :=
  letI := traceChartedSpace A
  tubeModelCoordinates (e := e) ∘ extChartAt ((ProductHalfSpace.model (Vector 6)).prod
    𝓘(ℝ, TimeGraphFrameSpace (e := e))) q

theorem tubeModelCoordinates_range :
    tubeModelCoordinates (e := e) '' range ((ProductHalfSpace.model (Vector 6)).prod
      𝓘(ℝ, TimeGraphFrameSpace (e := e))) = {z | 0 ≤ z.1} := by
  rw [ModelWithCorners.range_prod, ProductHalfSpace.model_range, ModelWithCorners.range_eq_univ]
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw.1
  · intro hz
    exact ⟨((z.1, z.2.1), z.2.2), ⟨hz, mem_univ _⟩, rfl⟩

theorem tubeModel_interior :
    interior (range ((ProductHalfSpace.model (Vector 6)).prod
      𝓘(ℝ, TimeGraphFrameSpace (e := e)))) = {z | 0 < z.1.1} := by
  rw [ModelWithCorners.range_prod, interior_prod_eq, ProductHalfSpace.model_interior,
    ModelWithCorners.range_eq_univ, interior_univ]
  ext z
  simp only [mem_prod, mem_setOf_eq, mem_univ, and_true]

theorem map_tubeChart_nhds (q : ambientSet A × TimeGraphFrameSpace (e := e)) :
    Filter.map (tubeChart A q) (𝓝 q) = 𝓝[{z | 0 ≤ z.1}] (tubeChart A q q) := by
  let := traceChartedSpace A
  change Filter.map (tubeModelCoordinates (e := e) ∘ extChartAt
    ((ProductHalfSpace.model (Vector 6)).prod 𝓘(ℝ, TimeGraphFrameSpace (e := e))) q) (𝓝 q) = _
  rw [← Filter.map_map, map_extChartAt_nhds]
  have hm := (tubeModelCoordinates (e := e)).toHomeomorph.isEmbedding.map_nhdsWithin_eq
    (range ((ProductHalfSpace.model (Vector 6)).prod 𝓘(ℝ, TimeGraphFrameSpace (e := e))))
    (extChartAt ((ProductHalfSpace.model (Vector 6)).prod
      𝓘(ℝ, TimeGraphFrameSpace (e := e))) q q)
  change Filter.map (tubeModelCoordinates (e := e)) _ =
    𝓝[tubeModelCoordinates (e := e) '' range ((ProductHalfSpace.model (Vector 6)).prod
      𝓘(ℝ, TimeGraphFrameSpace (e := e)))] (tubeChart A q q) at hm
  rw [tubeModelCoordinates_range] at hm
  exact hm

theorem tubeChart_first_nonneg (q y : ambientSet A × TimeGraphFrameSpace (e := e))
    (hy : letI := traceChartedSpace A;
      y ∈ (extChartAt ((ProductHalfSpace.model (Vector 6)).prod
        𝓘(ℝ, TimeGraphFrameSpace (e := e))) q).source) : 0 ≤ (tubeChart A q y).1 := by
  let := traceChartedSpace A
  have h := extChartAt_target_subset_range q ((extChartAt _ q).map_source hy)
  rw [ModelWithCorners.range_prod, ProductHalfSpace.model_range,
    ModelWithCorners.range_eq_univ] at h
  exact h.1

theorem tubeChart_first_pos_iff (q y : ambientSet A × TimeGraphFrameSpace (e := e))
    (hy : letI := traceChartedSpace A;
      y ∈ (extChartAt ((ProductHalfSpace.model (Vector 6)).prod
        𝓘(ℝ, TimeGraphFrameSpace (e := e))) q).source) :
    0 < (tubeChart A q y).1 ↔ y.1 ∉ traceBoundarySet A := by
  let := traceChartedSpace A
  let := trace_isManifold A
  let I := (ProductHalfSpace.model (Vector 6)).prod 𝓘(ℝ, TimeGraphFrameSpace (e := e))
  have hchart : I.IsInteriorPoint y ↔ 0 < (tubeChart A q y).1 := by
    rw [isInteriorPoint_iff_extChartAt_mem_interior_range q y hy, tubeModel_interior]
    rfl
  rw [← hchart]
  have hprod : I.IsInteriorPoint y ↔ (ProductHalfSpace.model (Vector 6)).IsInteriorPoint y.1 := by
    change y ∈ I.interior (ambientSet A × TimeGraphFrameSpace (e := e)) ↔ _
    rw [ModelWithCorners.interior_prod]
    change (_ ∧ _) ↔ _
    exact and_iff_left (BoundarylessManifold.isInteriorPoint (I := 𝓘(ℝ, _)))
  rw [hprod, ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint,
    trace_isBoundaryPoint_iff]

theorem tubeChart_first_zero_iff (q y : ambientSet A × TimeGraphFrameSpace (e := e))
    (hy : letI := traceChartedSpace A;
      y ∈ (extChartAt ((ProductHalfSpace.model (Vector 6)).prod
        𝓘(ℝ, TimeGraphFrameSpace (e := e))) q).source) :
    (tubeChart A q y).1 = 0 ↔ y.1 ∈ traceBoundarySet A := by
  have hn := tubeChart_first_nonneg A q y hy
  have hp := tubeChart_first_pos_iff A q y hy
  constructor
  · intro hz
    by_contra hb
    have hpos := hp.mpr hb
    linarith
  · intro hb
    exact le_antisymm (not_lt.mp (fun h ↦ hp.mp h hb)) hn

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
