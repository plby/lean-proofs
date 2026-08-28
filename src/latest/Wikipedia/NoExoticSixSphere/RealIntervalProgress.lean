import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.ProjIcc

/-!
# Clamped progress on a real time interval

The progress is continuous on the entire real line, zero before the interval,
one after it, and equal to the usual affine coordinate inside it.
-/

open Set unitInterval

namespace NoExoticSixSphere.RealIntervalProgress

noncomputable def progress (l u t : ℝ) : ℝ :=
  projIcc (0 : ℝ) 1 zero_le_one ((t - l) / (u - l))

theorem continuous_progress (l u : ℝ) : Continuous (progress l u) :=
  continuous_subtype_val.comp
    (continuous_projIcc.comp ((continuous_id.sub continuous_const).div_const _))

theorem progress_before {l u t : ℝ} (hlu : l ≤ u) (ht : t ≤ l) : progress l u t = 0 := by
  have h := projIcc_of_le_left (a := (0 : ℝ)) (b := 1) zero_le_one
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_nonneg.mpr hlu))
  exact congrArg Subtype.val h

theorem progress_after {l u t : ℝ} (hlu : l < u) (ht : u ≤ t) : progress l u t = 1 := by
  have hr : 1 ≤ (t - l) / (u - l) := by
    apply (le_div_iff₀ (sub_pos.mpr hlu)).mpr
    simpa only [one_mul] using sub_le_sub_right ht l
  exact congrArg Subtype.val (projIcc_of_right_le zero_le_one hr)

theorem progress_of_mem {l u t : ℝ} (hlu : l < u) (ht : t ∈ Icc l u) :
    progress l u t = (t - l) / (u - l) := by
  have h0 : 0 ≤ (t - l) / (u - l) := div_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr hlu.le)
  have h1 : (t - l) / (u - l) ≤ 1 := by
    apply (div_le_iff₀ (sub_pos.mpr hlu)).mpr
    simpa only [one_mul] using sub_le_sub_right ht.2 l
  change max 0 (min 1 _) = _
  rw [min_eq_right h1, max_eq_right h0]

end NoExoticSixSphere.RealIntervalProgress
