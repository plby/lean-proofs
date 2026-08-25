import StackExchange.Puzzling139335.WeightedMass.Basic
import StackExchange.Puzzling139335.JordanRegion
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Local weighted mass

The weighted mass of a piece inside a metric ball.  The bounds below use the
actual interior and frontier of the piece, so no null-boundary assumption is
needed.  A Jordan region has positive local mass at each of its points because
it is the closure of its interior.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Puzzling139335

noncomputable section

/-- The weighted mass of a piece in an open ball. -/
def localMass (P : Set Plane) (v : Plane) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Metric.ball v r, weightedDensity P x ∂volume

/-- Local weighted mass is bounded above by the area of its ball. -/
theorem localMass_le_ball_volume (P : Set Plane) (v : Plane) (r : ℝ) :
    localMass P v r ≤ volume (Metric.ball v r) := by
  calc
    localMass P v r ≤ ∫⁻ x in Metric.ball v r, (1 : ℝ≥0∞) ∂volume :=
      lintegral_mono (weightedDensity_le_one P)
    _ = volume (Metric.ball v r) := setLIntegral_one _

/-- Every local weighted mass is finite, including at nonpositive radii. -/
theorem localMass_lt_top (P : Set Plane) (v : Plane) (r : ℝ) :
    localMass P v r < ∞ :=
  (localMass_le_ball_volume P v r).trans_lt measure_ball_lt_top

/-- All area in the interior contributes with weight one. -/
theorem volume_ball_inter_interior_le_localMass (P : Set Plane) (v : Plane) (r : ℝ) :
    volume (Metric.ball v r ∩ interior P) ≤ localMass P v r := by
  calc
    volume (Metric.ball v r ∩ interior P) =
        ∫⁻ x in Metric.ball v r ∩ interior P, weightedDensity P x ∂volume := by
      rw [← setLIntegral_one (Metric.ball v r ∩ interior P)]
      apply setLIntegral_congr_fun
        (Metric.isOpen_ball.inter isOpen_interior).measurableSet
      intro x hx
      exact (weightedDensity_of_mem_interior hx.2).symm
    _ ≤ localMass P v r := lintegral_mono_set inter_subset_left

/-- Each positive-radius ball centered on a Jordan region has positive local mass. -/
theorem localMass_pos {P : Set Plane} (hP : IsJordanRegion P)
    {v : Plane} (hv : v ∈ P) {r : ℝ} (hr : 0 < r) :
    0 < localMass P v r := by
  have hvcl : v ∈ closure (interior P) := by
    rwa [hP.closure_interior]
  obtain ⟨x, hx, hdist⟩ := Metric.mem_closure_iff.mp hvcl r hr
  have hne : (Metric.ball v r ∩ interior P).Nonempty :=
    ⟨x, by simpa only [Metric.mem_ball, dist_comm] using hdist, hx⟩
  have hpos : 0 < volume (Metric.ball v r ∩ interior P) :=
    (Metric.isOpen_ball.inter isOpen_interior).measure_pos volume hne
  exact hpos.trans_le (volume_ball_inter_interior_le_localMass P v r)

/-- A ball missing a closed piece has no contribution from its frontier either. -/
theorem localMass_eq_zero_of_disjoint {P : Set Plane} (hP : IsClosed P)
    {v : Plane} {r : ℝ} (hdis : Disjoint (Metric.ball v r) P) :
    localMass P v r = 0 := by
  calc
    localMass P v r = ∫⁻ _x in Metric.ball v r, (0 : ℝ≥0∞) ∂volume := by
      apply setLIntegral_congr_fun Metric.isOpen_ball.measurableSet
      intro x hx
      exact weightedDensity_of_not_mem hP (fun hp => Set.disjoint_left.mp hdis hx hp)
    _ = 0 := by simp

/-- A pointwise version of the disjoint-ball criterion. -/
theorem localMass_eq_zero_of_not_mem {P : Set Plane} (hP : IsClosed P)
    {v : Plane} {r : ℝ} (h : ∀ x ∈ Metric.ball v r, x ∉ P) :
    localMass P v r = 0 :=
  localMass_eq_zero_of_disjoint hP (Set.disjoint_left.mpr h)

end

end Puzzling139335
