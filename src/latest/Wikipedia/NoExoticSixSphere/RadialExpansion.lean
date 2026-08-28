import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Continuous outward radial expansion in a punctured ball

The radius interpolates from the initial norm to a prescribed outer radius.
Every stage is a nonnegative scalar multiple of the initial vector, the scalar
lies between one and its final value, and boundary vectors remain fixed.
-/

open Set unitInterval

namespace NoExoticSixSphere.RadialExpansion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def scale (r : ℝ) (p : I × E) : ℝ :=
  1 + (p.1 : ℝ) * (r / ‖p.2‖ - 1)

noncomputable def expand (r : ℝ) (p : I × E) : E := scale r p • p.2

omit [NormedSpace ℝ E] in
theorem scale_bounds (r : ℝ) {x : E} (hx : x ≠ 0) (hxr : ‖x‖ ≤ r) (s : I) :
    1 ≤ scale r (s, x) ∧ scale r (s, x) ≤ r / ‖x‖ := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hr : 1 ≤ r / ‖x‖ := (le_div_iff₀ hn).mpr (by simpa using hxr)
  have hp := mul_nonneg s.2.1 (sub_nonneg.mpr hr)
  have hq := mul_le_mul_of_nonneg_right s.2.2 (sub_nonneg.mpr hr)
  dsimp only [scale]
  constructor <;> linarith

theorem norm_expand (r : ℝ) {x : E} (hx : x ≠ 0) (hxr : ‖x‖ ≤ r) (s : I) :
    ‖expand r (s, x)‖ = (1 - (s : ℝ)) * ‖x‖ + (s : ℝ) * r := by
  have hs : 0 ≤ scale r (s, x) := le_trans zero_le_one (scale_bounds r hx hxr s).1
  rw [expand, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  change (1 + (s : ℝ) * (r / ‖x‖ - 1)) * ‖x‖ = _
  calc
    _ = (1 - (s : ℝ)) * ‖x‖ + (s : ℝ) * ((r / ‖x‖) * ‖x‖) := by ring
    _ = _ := by rw [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)]

theorem norm_expand_bounds (r : ℝ) {x : E} (hx : x ≠ 0) (hxr : ‖x‖ ≤ r) (s : I) :
    ‖x‖ ≤ ‖expand r (s, x)‖ ∧ ‖expand r (s, x)‖ ≤ r := by
  rw [norm_expand r hx hxr s]
  have h1 := mul_nonneg s.2.1 (sub_nonneg.mpr hxr)
  have h2 := mul_nonneg (sub_nonneg.mpr s.2.2) (sub_nonneg.mpr hxr)
  constructor <;> nlinarith

theorem expand_zero (r : ℝ) (x : E) : expand r (0, x) = x := by simp [expand, scale]

theorem norm_expand_one (r : ℝ) {x : E} (hx : x ≠ 0) (hxr : ‖x‖ ≤ r) :
    ‖expand r (1, x)‖ = r := by simpa using norm_expand r hx hxr 1

theorem expand_fixed (r : ℝ) (hr : 0 < r) {x : E} (hxr : ‖x‖ = r) (s : I) :
    expand r (s, x) = x := by simp [expand, scale, hxr, ne_of_gt hr]

theorem continuousAt_expand (r : ℝ) {p : I × E} (hp : p.2 ≠ 0) :
    ContinuousAt (expand r) p := by
  have hs : ContinuousAt (scale r) p :=
    continuousAt_const.add ((continuous_subtype_val.continuousAt.comp continuousAt_fst).mul
      ((continuousAt_const.div continuousAt_snd.norm (norm_ne_zero_iff.mpr hp)).sub
        continuousAt_const))
  exact hs.smul continuousAt_snd

end NoExoticSixSphere.RadialExpansion
