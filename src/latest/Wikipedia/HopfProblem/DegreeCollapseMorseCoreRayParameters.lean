import Wikipedia.HopfProblem.DegreeCollapseNativeMorseCoreFlow

/-!
# Exact unit-core parameters for a nonzero small Morse coordinate

Normalization supplies the original unit-sphere point, and the logarithm
of the radius ratio supplies the correctly signed Morse-flow time.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem exists_negative_core_ray_parameter {r : ℝ} (hr : 0 < r) {z : A}
    (hz : z ≠ 0) (hzr : ‖z‖ < r) :
    ∃ (u : PuncturedHandle.UnitSphere A) (t : ℝ),
      t < 0 ∧ Real.exp t • (r • (u : A)) = z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let u : PuncturedHandle.UnitSphere A :=
    ⟨‖z‖⁻¹ • z, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hz)⟩
  have hratio : 0 < ‖z‖ / r := div_pos hn hr
  have hratio1 : ‖z‖ / r < 1 := (div_lt_one hr).mpr hzr
  have hcoef : Real.exp (Real.log (‖z‖ / r)) * r * ‖z‖⁻¹ = 1 := by
    rw [Real.exp_log hratio]
    field_simp
  refine ⟨u, Real.log (‖z‖ / r), Real.log_neg hratio hratio1, ?_⟩
  change Real.exp (Real.log (‖z‖ / r)) • (r • (‖z‖⁻¹ • z)) = z
  rw [smul_smul, smul_smul, hcoef, one_smul]

theorem exists_positive_core_ray_parameter {r : ℝ} (hr : 0 < r) {z : A}
    (hz : z ≠ 0) (hzr : ‖z‖ < r) :
    ∃ (u : PuncturedHandle.UnitSphere A) (t : ℝ),
      0 < t ∧ Real.exp (-t) • (r • (u : A)) = z := by
  obtain ⟨u, t, ht, heq⟩ := exists_negative_core_ray_parameter hr hz hzr
  exact ⟨u, -t, neg_pos.mpr ht, by simpa only [neg_neg] using heq⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
