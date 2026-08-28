import Wikipedia.NoExoticSixSphere.RoundedTraceTubeChartCoordinates
import Wikipedia.NoExoticSixSphere.RoundedTraceTubeEndCoordinates

/-!
# Actual half-space side conditions at the tube boundary

Time preservation holds on a whole base neighborhood of the native boundary,
for every fiber vector. Excluding the opposite end then gives the exact zero
and positive signs required by the relative-open-mapping argument.
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

def tubeEndTime (top : Bool) (p : ambientSet A) : ℝ :=
  if top then 1 - bordismTime A p else bordismTime A p

theorem continuous_tubeEndTime (top : Bool) : Continuous (tubeEndTime A top) := by
  let := traceChartedSpace A
  have hc := (contMDiff_bordismTime A).continuous
  cases top
  · exact hc
  · exact continuous_const.sub hc

theorem tubeEndTime_boundary (top : Bool) (p : ambientSet A)
    (hp : p ∈ traceBoundarySet A) : tubeEndTime A top p = 0 ∨ tubeEndTime A top p = 1 := by
  let := traceChartedSpace A
  have hb := (trace_isBoundaryPoint_iff A p).mpr hp
  rcases (boundary_iff_mem_ends A p).mp hb with ho | ht
  · have he := bordismTime_otherEnd A ho
    cases top <;> simp only [tubeEndTime, Bool.false_eq_true, if_false, if_true, he] <;> norm_num
  · have he := bordismTime_topEnd A ht
    cases top <;> simp only [tubeEndTime, Bool.false_eq_true, if_false, if_true, he] <;> norm_num

theorem exists_zero_tubeEndTime (p : ambientSet A) (hp : p ∈ traceBoundarySet A) :
    ∃ top : Bool, tubeEndTime A top p = 0 := by
  rcases tubeEndTime_boundary A false p hp with h | h
  · exact ⟨false, h⟩
  · refine ⟨true, ?_⟩
    change 1 - bordismTime A p = 0
    change bordismTime A p = 1 at h
    rw [h, sub_self]

theorem tubeEndTime_interior (top : Bool) (p : ambientSet A)
    (hp : p ∉ traceBoundarySet A) : tubeEndTime A top p ∈ Ioo 0 1 := by
  let := traceChartedSpace A
  have hb : ¬(ProductHalfSpace.model (Vector 6)).IsBoundaryPoint p :=
    fun h ↦ hp ((trace_isBoundaryPoint_iff A p).mp h)
  have ht := bordismTime_interior A p hb
  cases top
  · exact ht
  · change 0 < 1 - bordismTime A p ∧ 1 - bordismTime A p < 1
    constructor <;> linarith [ht.1, ht.2]

theorem eventually_verticalTube_end_time
    (q : ambientSet A × TimeGraphFrameSpace (e := e)) (hq : q.1 ∈ traceBoundarySet A) :
    ∀ᶠ y in 𝓝 q, ∀ top : Bool,
      (tubeEndCoordinates (e := e) top (verticalTube A y)).1 = tubeEndTime A top y.1 := by
  let := traceChartedSpace A
  obtain ⟨U, hU, hBU, htime⟩ := exists_verticalTube_time_neighborhood A
  have hb : (ProductHalfSpace.model (Vector 6)).IsBoundaryPoint q.1 :=
    (trace_isBoundaryPoint_iff A q.1).mpr hq
  have hqU : q.1 ∈ U := hBU ⟨⟨q.1, hb⟩, rfl⟩
  have hnear : ∀ᶠ y in 𝓝 q, y.1 ∈ U := continuous_fst.continuousAt (hU.mem_nhds hqU)
  filter_upwards [hnear] with y hy top
  rw [tubeEndCoordinates_first, htime y.1 hy y.2]
  rfl

theorem eventually_tubeChart_boundary_signs
    (q : ambientSet A × TimeGraphFrameSpace (e := e)) (hq : q.1 ∈ traceBoundarySet A)
    (top : Bool) (htop : tubeEndTime A top q.1 = 0) :
    ∀ᶠ y in 𝓝 q,
      ((tubeChart A q y).1 = 0 → (tubeEndCoordinates (e := e) top (verticalTube A y)).1 = 0) ∧
      (0 < (tubeChart A q y).1 → 0 < (tubeEndCoordinates (e := e) top (verticalTube A y)).1) := by
  let := traceChartedSpace A
  have hc := (continuous_tubeEndTime A top).comp
    (continuous_fst : Continuous (Prod.fst : ambientSet A × TimeGraphFrameSpace (e := e) → _))
  have hnear : ∀ᶠ y in 𝓝 q, tubeEndTime A top y.1 < 1 :=
    hc.continuousAt (isOpen_Iio.mem_nhds (by change tubeEndTime A top q.1 < 1; rw [htop]; norm_num))
  have hchart : (extChartAt ((ProductHalfSpace.model (Vector 6)).prod
      𝓘(ℝ, TimeGraphFrameSpace (e := e))) q).source ∈ 𝓝 q := extChartAt_source_mem_nhds q
  filter_upwards [eventually_verticalTube_end_time A q hq, hnear, hchart] with y hy hylt hychart
  rw [hy top]
  constructor
  · intro hz
    rcases tubeEndTime_boundary A top y.1 ((tubeChart_first_zero_iff A q y hychart).mp hz)
      with hzero | hone
    · exact hzero
    · exact (ne_of_lt hylt hone).elim
  · intro hp
    exact (tubeEndTime_interior A top y.1 ((tubeChart_first_pos_iff A q y hychart).mp hp)).1

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
