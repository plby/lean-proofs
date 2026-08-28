import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Tactic.Linarith

/-!
# A continuous radial shrinking map, including its zero section

Subtract a nonnegative amount from the radius and stop at zero. The norm
bound proves joint continuity at every zero vector, without dividing by a
nonzero radius there. This map will collapse the transverse factor of a
handle while fixing its attaching face.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.SmoothSixDPoincare.RadialCoreShrink

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def shrink (a : ℝ) (y : E) : E :=
  (max (‖y‖ - max a 0) 0 / ‖y‖) • y

@[simp] theorem shrink_zero (a : ℝ) : shrink a (0 : E) = 0 := by
  simp [shrink]

theorem norm_shrink (a : ℝ) (y : E) :
    ‖shrink a y‖ = max (‖y‖ - max a 0) 0 := by
  by_cases hy : y = 0
  · subst y
    rw [shrink_zero, norm_zero]
    exact (max_eq_right (by linarith [le_max_right a 0])).symm
  rw [shrink, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (le_max_right _ _) (norm_nonneg y)),
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hy)]

theorem norm_shrink_le (a : ℝ) (y : E) : ‖shrink a y‖ ≤ ‖y‖ := by
  rw [norm_shrink]
  exact max_le (sub_le_self _ (le_max_right a 0)) (norm_nonneg y)

@[simp] theorem shrink_zero_parameter (y : E) : shrink 0 y = y := by
  by_cases hy : y = 0
  · subst y
    exact shrink_zero 0
  rw [shrink, max_self, sub_zero, max_eq_left (norm_nonneg y),
    div_self (norm_ne_zero_iff.mpr hy), one_smul]

theorem shrink_eq_zero {a : ℝ} {y : E} (hy : ‖y‖ ≤ a) : shrink a y = 0 := by
  rw [shrink, max_eq_right (sub_nonpos.mpr (hy.trans (le_max_left a 0))),
    zero_div, zero_smul]

/-- Radius subtraction is jointly continuous, also when the vector vanishes. -/
theorem continuous_shrink : Continuous (fun z : ℝ × E => shrink z.1 z.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨a, y⟩
  by_cases hy : y = 0
  · subst y
    change Tendsto (fun z : ℝ × E => shrink z.1 z.2) (𝓝 (a, 0)) (𝓝 (shrink a 0))
    rw [shrink_zero]
    apply squeeze_zero_norm (fun z => norm_shrink_le z.1 z.2)
    simpa only [ContinuousAt, norm_zero] using
      (continuous_snd.norm.continuousAt :
        ContinuousAt (fun z : ℝ × E => ‖z.2‖) (a, 0))
  exact (((continuous_snd.norm.sub (continuous_fst.max continuous_const)).max
    continuous_const).continuousAt.div continuous_snd.norm.continuousAt
      (norm_ne_zero_iff.mpr hy)).smul continuous_snd.continuousAt

end Wikipedia.SmoothSixDPoincare.RadialCoreShrink
