import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.ContinuousMap.Basic

/-!
# A literal radial clamp onto the closed unit disk

The map is continuous everywhere, fixes the whole closed disk, and sends
every exterior point to the original unit sphere.
-/

noncomputable section

open Metric

namespace NoExoticSixSphere.UnitDiskClamp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def map (x : E) : E := (max 1 ‖x‖)⁻¹ • x

omit [NormedSpace ℝ E] in
theorem denominator_pos (x : E) : 0 < max 1 ‖x‖ :=
  zero_lt_one.trans_le (le_max_left _ _)

theorem continuous_map : Continuous (map (E := E)) :=
  ((continuous_const.max continuous_norm).inv₀
    (fun x ↦ (denominator_pos x).ne')).smul continuous_id

theorem map_of_norm_le (x : E) (hx : ‖x‖ ≤ 1) : map x = x := by
  rw [map, max_eq_left hx, inv_one, one_smul]

theorem norm_map_le (x : E) : ‖map x‖ ≤ 1 := by
  rw [map, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos (denominator_pos x), ← div_eq_inv_mul]
  exact (div_le_one (denominator_pos x)).mpr (le_max_right _ _)

theorem map_mem_closedBall (x : E) : map x ∈ closedBall 0 1 :=
  mem_closedBall_zero_iff.mpr (norm_map_le x)

theorem norm_map_of_one_le (x : E) (hx : 1 ≤ ‖x‖) : ‖map x‖ = 1 := by
  rw [map, max_eq_right hx, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (zero_lt_one.trans_le hx).ne'

def continuousMap : C(E, E) := ⟨map, continuous_map⟩

end NoExoticSixSphere.UnitDiskClamp
