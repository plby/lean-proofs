import Wikipedia.NoExoticSixSphere.RoundedTraceEndCutoff
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# A smooth time function on the actual rounded bordism

Combining the end cutoff `χ` and the nonnegative boundary equation `φ` as
`(χ + φ) / (1 + 2 * φ)` gives time zero and one exactly at the two ends.
Every native interior point has time strictly between zero and one.
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

def bordismTime (p : ambientSet A) : ℝ :=
  letI := traceChartedSpace A
  (endCutoff A p + boundaryDefiningFunction A p) / (1 + 2 * boundaryDefiningFunction A p)

theorem bordismTime_denominator_pos (p : ambientSet A) :
    0 < 1 + 2 * boundaryDefiningFunction A p := by
  have hp := boundaryDefiningFunction_nonneg A p
  linarith

theorem contMDiff_bordismTime : letI := traceChartedSpace A;
    ContMDiff (ProductHalfSpace.model (Vector 6)) 𝓘(ℝ, ℝ) ∞ (bordismTime A) := by
  let := traceChartedSpace A
  have hφ := contMDiff_boundaryDefiningFunction A
  exact ((endCutoff A).contMDiff.add hφ).div₀
    (contMDiff_const.add (contMDiff_const.mul hφ))
    (fun p ↦ (bordismTime_denominator_pos A p).ne')

theorem bordismTime_mem_Icc (p : ambientSet A) : bordismTime A p ∈ Icc 0 1 := by
  let := traceChartedSpace A
  have hφ := boundaryDefiningFunction_nonneg A p
  have hχ := endCutoff_mem_Icc A p
  have hd := bordismTime_denominator_pos A p
  constructor
  · exact div_nonneg (add_nonneg hχ.1 hφ) hd.le
  · change (endCutoff A p + boundaryDefiningFunction A p) /
      (1 + 2 * boundaryDefiningFunction A p) ≤ 1
    rw [div_le_one hd]
    linarith [hχ.2]

theorem bordismTime_interior (p : ambientSet A) : letI := traceChartedSpace A;
    ¬(ProductHalfSpace.model (Vector 6)).IsBoundaryPoint p →
      bordismTime A p ∈ Ioo 0 1 := by
  let := traceChartedSpace A
  intro hp
  have hφ := (boundaryDefiningFunction_pos_iff A p).mpr hp
  have hχ := endCutoff_mem_Icc A p
  have hd := bordismTime_denominator_pos A p
  constructor
  · exact div_pos (add_pos_of_nonneg_of_pos hχ.1 hφ) hd
  · change (endCutoff A p + boundaryDefiningFunction A p) /
      (1 + 2 * boundaryDefiningFunction A p) < 1
    rw [div_lt_one hd]
    linarith [hχ.2]

theorem bordismTime_otherEnd {p : ambientSet A} (hp : p ∈ otherEnd A) :
    bordismTime A p = 0 := by
  let := traceChartedSpace A
  have hφ := (boundaryDefiningFunction_zero_iff A p).mpr ((mem_otherEnd_iff A p).mp hp).1
  simp only [bordismTime, endCutoff_zero A hp, hφ, add_zero, mul_zero, zero_div]

theorem bordismTime_topEnd {p : ambientSet A} (hp : p ∈ topEnd A) :
    bordismTime A p = 1 := by
  let := traceChartedSpace A
  have hφ := (boundaryDefiningFunction_zero_iff A p).mpr ((mem_topEnd_iff A p).mp hp).1
  simp only [bordismTime, endCutoff_one A hp, hφ, add_zero, mul_zero, div_one]

theorem bordismTime_zero_iff (p : ambientSet A) :
    bordismTime A p = 0 ↔ p ∈ otherEnd A := by
  let := traceChartedSpace A
  constructor
  · intro hz
    have hb : (ProductHalfSpace.model (Vector 6)).IsBoundaryPoint p := by
      by_contra hp
      exact (ne_of_gt (bordismTime_interior A p hp).1) hz
    rcases (boundary_iff_mem_ends A p).mp hb with hp | hp
    · exact hp
    · have he := bordismTime_topEnd A hp
      linarith
  · exact bordismTime_otherEnd A

theorem bordismTime_one_iff (p : ambientSet A) :
    bordismTime A p = 1 ↔ p ∈ topEnd A := by
  let := traceChartedSpace A
  constructor
  · intro ho
    have hb : (ProductHalfSpace.model (Vector 6)).IsBoundaryPoint p := by
      by_contra hp
      exact (ne_of_lt (bordismTime_interior A p hp).2) ho
    rcases (boundary_iff_mem_ends A p).mp hb with hp | hp
    · have he := bordismTime_otherEnd A hp
      linarith
    · exact hp
  · exact bordismTime_topEnd A

theorem bordismTime_mem_Ioo_iff (p : ambientSet A) : letI := traceChartedSpace A;
    bordismTime A p ∈ Ioo 0 1 ↔
      ¬(ProductHalfSpace.model (Vector 6)).IsBoundaryPoint p := by
  let := traceChartedSpace A
  constructor
  · intro ht hb
    rcases (boundary_iff_mem_ends A p).mp hb with hp | hp
    · exact (ne_of_gt ht.1) (bordismTime_otherEnd A hp)
    · exact (ne_of_lt ht.2) (bordismTime_topEnd A hp)
  · exact bordismTime_interior A p

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
