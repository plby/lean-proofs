import Wikipedia.HopfProblem.DegreeCollapseCubicModelOrbit
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The exact cubic longitudinal time chart

The complete longitudinal orbit and its explicit inverse time coordinate
are smooth on their actual domains. They form a genuine partial
diffeomorphism from the real time line onto the open interval between the
two cubic critical points.
-/

noncomputable section

open Set Function
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

/-- Smoothness of the actual inverse hyperbolic tangent on its open real domain. -/
theorem contDiffAt_artanh {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ContDiffAt ℝ ∞ Real.artanh x := by
  have hp : 0 < (1 + x) / (1 - x) := div_pos (by linarith [hx.1]) (by linarith [hx.2])
  have hr : ContDiffAt ℝ ∞ (fun y : ℝ => (1 + y) / (1 - y)) x :=
    (contDiffAt_const.add contDiffAt_id).div (contDiffAt_const.sub contDiffAt_id)
      (by linarith [hx.2])
  exact (hr.sqrt hp.ne').log (Real.sqrt_pos.mpr hp).ne'

theorem contDiff_cubicAxisParameter (a : ℝ) : ContDiff ℝ ∞ (cubicAxisParameter a) := by
  have ht : ContDiff ℝ ∞ Real.tanh := by
    have hh : ContDiff ℝ ∞ (fun t => Real.sinh t / Real.cosh t) :=
      Real.contDiff_sinh.div Real.contDiff_cosh (fun t => (Real.cosh_pos t).ne')
    have he : (fun t => Real.sinh t / Real.cosh t) = Real.tanh :=
      funext (fun t => (Real.tanh_eq_sinh_div_cosh t).symm)
    rw [he] at hh
    exact hh
  change ContDiff ℝ ∞ (fun t => a * Real.tanh (a * t))
  exact contDiff_const.mul (ht.comp (contDiff_const.mul contDiff_id))

def cubicAxisClock (a s : ℝ) : ℝ := Real.artanh (s / a) / a

theorem cubicAxisClock_parameter {a : ℝ} (ha : 0 < a) (t : ℝ) :
    cubicAxisClock a (cubicAxisParameter a t) = t := by
  simp only [cubicAxisClock, cubicAxisParameter, mul_div_cancel_left₀ _ ha.ne', Real.artanh_tanh]

theorem cubicAxisParameter_clock {a s : ℝ} (ha : 0 < a) (hs : s ∈ Ioo (-a) a) :
    cubicAxisParameter a (cubicAxisClock a s) = s := by
  have hs' : s / a ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · exact (lt_div_iff₀ ha).mpr (by simpa only [neg_one_mul] using hs.1)
    · exact (div_lt_iff₀ ha).mpr (by simpa only [one_mul] using hs.2)
  simp only [cubicAxisClock, cubicAxisParameter, mul_div_cancel₀ _ ha.ne', Real.tanh_artanh hs']

theorem contDiffOn_cubicAxisClock {a : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ ∞ (cubicAxisClock a) (Ioo (-a) a) := by
  intro s hs
  have hs' : s / a ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · exact (lt_div_iff₀ ha).mpr (by simpa only [neg_one_mul] using hs.1)
    · exact (div_lt_iff₀ ha).mpr (by simpa only [one_mul] using hs.2)
  exact (((contDiffAt_artanh hs').comp s (contDiffAt_id.div_const a)).div_const a).contDiffWithinAt

/-- The actual longitudinal orbit is a smooth time chart between the two critical endpoints. -/
def cubicAxisTimeChart {a : ℝ} (ha : 0 < a) :
    PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ where
  toFun := cubicAxisParameter a
  invFun := cubicAxisClock a
  source := univ
  target := Ioo (-a) a
  map_source' t _ := cubicAxisParameter_mem ha t
  map_target' _ _ := mem_univ _
  left_inv' t _ := cubicAxisClock_parameter ha t
  right_inv' _ hs := cubicAxisParameter_clock ha hs
  open_source := isOpen_univ
  open_target := isOpen_Ioo
  contMDiffOn_toFun := (contDiff_cubicAxisParameter a).contMDiff.contMDiffOn
  contMDiffOn_invFun := (contDiffOn_cubicAxisClock ha).contMDiffOn

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
