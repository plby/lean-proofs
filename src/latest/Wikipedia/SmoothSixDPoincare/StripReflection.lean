import Wikipedia.SmoothSixDPoincare.StripSliceDerivative
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Reversing the horizontal parameter of an endpoint corner

Horizontal reflection moves the corner at zero to the strip endpoint at one.
It preserves the actual vertical derivative, and changes the vertical-axis
contact equation from first coordinate zero to first coordinate one.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.StripCoordinates

def reverse (p : ℝ × ℝ) : ℝ × ℝ := (1 - p.1, p.2)

theorem contDiff_reverse : ContDiff ℝ ∞ reverse :=
  (contDiff_const.sub contDiff_fst).prodMk contDiff_snd

theorem reverse_one_zero : reverse (1, 0) = (0, 0) := by simp only [reverse, sub_self]

theorem reverse_involutive : Involutive reverse := by
  rintro ⟨t, s⟩
  simp only [reverse, sub_sub_cancel]

theorem reverse_tendsto_one_zero : Tendsto reverse (𝓝 (1, 0)) (𝓝 (0, 0)) := by
  have h : Tendsto reverse (𝓝 (1, 0)) (𝓝 (reverse (1, 0))) :=
    contDiff_reverse.continuous.continuousAt.tendsto
  rwa [reverse_one_zero] at h

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- Horizontal reflection preserves the actual vertical derivative at the endpoint. -/
theorem vertical_derivative_reverse {H : (ℝ × ℝ) → B}
    (hH : DifferentiableAt ℝ H (0, 0)) :
    fderiv ℝ (H ∘ reverse) (1, 0) (0, 1) = fderiv ℝ H (0, 0) (0, 1) := by
  have houter : DifferentiableAt ℝ H (reverse (1, 0)) := by
    rw [reverse_one_zero]
    exact hH
  have hcomp : DifferentiableAt ℝ (H ∘ reverse) (1, 0) :=
    houter.comp (1, 0) (contDiff_reverse.contDiffAt.differentiableAt (by simp))
  have hleft := hasDerivAt_verticalSlice hcomp
  have hright := hasDerivAt_verticalSlice hH
  have heq : (fun s : ℝ => (H ∘ reverse) (1, s)) = fun s => H (0, s) := by
    funext s
    simp only [comp_apply, reverse, sub_self]
  rw [heq] at hleft
  exact hleft.unique hright

end Wikipedia.SmoothSixDPoincare.StripCoordinates
