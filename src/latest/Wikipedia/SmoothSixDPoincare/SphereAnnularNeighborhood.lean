import Wikipedia.SmoothSixDPoincare.RadialExtension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening

/-!
# A uniform closed annulus inside an open neighborhood of the unit sphere

Compactness gives a positive closed thickening. The exact distance to the
normalized radial direction puts a full positive-width annulus inside it.
-/

noncomputable section

open Set Function Metric Topology

namespace Wikipedia.SmoothSixDPoincare.AnnularExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dist_direction {x : E} (hx : x ≠ 0) :
    dist x (RadialExtension.direction x hx : E) = |‖x‖ - 1| := by
  let v := RadialExtension.direction x hx
  have hvec : ‖x‖ • (v : E) = x := smul_inv_smul₀ (norm_ne_zero_iff.mpr hx) x
  have hn : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  change dist x (v : E) = _
  calc
    _ = ‖(‖x‖ - 1) • (v : E)‖ := by rw [dist_eq_norm, sub_smul, one_smul, hvec]
    _ = |‖x‖ - 1| := by rw [norm_smul, Real.norm_eq_abs, hn, mul_one]

/-- The annulus straddles radius one and has a strictly positive inner radius. -/
theorem exists_closed_annulus_subset [FiniteDimensional ℝ E] {W : Set E}
    (hW : IsOpen W) (hSW : sphere (0 : E) 1 ⊆ W) :
    ∃ a b : ℝ, 0 < a ∧ a < 1 ∧ 1 < b ∧ {x : E | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} ⊆ W := by
  obtain ⟨δ, hδ, hδW⟩ := (isCompact_sphere (0 : E) 1).exists_cthickening_subset_open hW hSW
  let ε := min (δ / 2) (1 / 2)
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hεsmall : ε ≤ 1 / 2 := min_le_right _ _
  have hεδ : ε ≤ δ := (min_le_left _ _).trans (by linarith)
  refine ⟨1 - ε, 1 + ε, by linarith, by linarith, by linarith, ?_⟩
  intro x hx
  have hx0 : x ≠ 0 := by
    intro heq
    have hxlo := hx.1
    rw [heq, norm_zero] at hxlo
    linarith
  have hdist : dist x (RadialExtension.direction x hx0 : E) ≤ δ := by
    rw [dist_direction]
    apply le_trans (abs_le.mpr ?_) hεδ
    constructor <;> linarith [hx.1, hx.2]
  exact hδW (mem_cthickening_of_dist_le x (RadialExtension.direction x hx0) δ
    (sphere (0 : E) 1) (RadialExtension.direction x hx0).property hdist)

end Wikipedia.SmoothSixDPoincare.AnnularExtension
