import Wikipedia.HopfProblem.DegreeCollapseMorseBeltPassage
import Wikipedia.HopfProblem.DegreeCollapseAdaptedSurgeryBasins
import Wikipedia.HopfProblem.DegreeCollapseClockNormalizedBasins

/-!
# Exact upper-to-lower passage under the actual native surgery flow

The explicit model segment lies in the whole closed adapted block. Native
integral-curve uniqueness identifies it with the original complete flow,
including its endpoint. Hence the upper and lower coordinate points have
exactly the same forward endpoint basins.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] {f : M → ℝ}

open Classical in
theorem AdaptedSurgeryWindows.flow_belt_passage
    (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    S.flow (BeltPassage.time s) ((S.data q).chart.splitChart.symm
      (BeltPassage.upper (S.data q).radius s u.val v.val)) =
      (S.data q).chart.splitChart.symm
        (BeltPassage.lower (S.data q).radius s u.val v.val) := by
  let d := S.data q
  let z := BeltPassage.upper d.radius s u.val v.val
  have htime := BeltPassage.time_nonneg hs
  have hstay (t : ℝ) (ht : t ∈ uIcc 0 (BeltPassage.time s)) :
      MorseHandle.descentFlow t z ∈ closedBall (0 : d.chart.NegativeCoordinates) (2 * d.radius) ×ˢ
        closedBall (0 : d.chart.PositiveCoordinates) (2 * d.radius) := by
    rw [uIcc_of_le htime] at ht
    exact BeltPassage.descentFlow_mem_block d.radius_pos hs hs₁
      (mem_sphere_zero_iff_norm.mp u.property) (mem_sphere_zero_iff_norm.mp v.property) ht
  have hz : z ∈ d.chart.splitChart.target := by
    have hh := d.block (hstay 0 left_mem_uIcc)
    simpa only [MorseHandle.descentFlow.map_zero_apply] using hh
  have hcoords : d.chart.splitChart (d.chart.splitChart.symm z) = z :=
    d.chart.splitChart.right_inv' hz
  have hflow := d.chart.flow_eq_descentModel_of_mem_uIcc (S.smooth.of_le (by simp))
    S.flow S.integral (x := d.chart.splitChart.symm z) (d.chart.splitChart.map_target' hz)
    (t := BeltPassage.time s)
    (fun t ht => by rw [hcoords]; exact d.block (hstay t ht))
    (fun t ht => by rw [hcoords]; exact S.model_germ q _ (hstay t ht))
  change S.flow (BeltPassage.time s) (d.chart.splitChart.symm z) =
    d.chart.splitChart.symm (MorseHandle.descentFlow (BeltPassage.time s)
      (d.chart.splitChart (d.chart.splitChart.symm z))) at hflow
  rw [hcoords, BeltPassage.descentFlow_time d.radius hs u.val v.val] at hflow
  exact hflow

open Classical in
theorem AdaptedSurgeryWindows.belt_passage_forward_limit_iff
    (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (p : M) :
    Tendsto (fun t => S.flow t ((S.data q).chart.splitChart.symm
      (BeltPassage.upper (S.data q).radius s u.val v.val))) atTop (𝓝 p) ↔
    Tendsto (fun t => S.flow t ((S.data q).chart.splitChart.symm
      (BeltPassage.lower (S.data q).radius s u.val v.val))) atTop (𝓝 p) := by
  rw [← S.flow_belt_passage q hs hs₁ u v]
  exact (flow_time_atTop_limit_iff S.flow (BeltPassage.time s) _ p).symm

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
