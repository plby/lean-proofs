import ErdosProblems.Erdos336.CircleArcHalfPlane
import ErdosProblems.Erdos336.FourierHalfPlane

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Real

variable {N : ℕ} [NeZero N]

noncomputable def fourierDirectionCircle
    (A : Finset (ZMod N)) (k : ZMod N)
    (hF : cyclicFinsetFourier A k ≠ 0) : Circle :=
  ⟨starRingEnd ℂ (cyclicFinsetFourier A k) /
      ‖cyclicFinsetFourier A k‖, by
    change starRingEnd ℂ (cyclicFinsetFourier A k) /
      (‖cyclicFinsetFourier A k‖ : ℂ) ∈ Metric.sphere 0 1
    rw [Metric.mem_sphere, dist_zero_right, norm_div]
    simp [hF]⟩

@[simp] lemma coe_fourierDirectionCircle
    (A : Finset (ZMod N)) (k : ZMod N)
    (hF : cyclicFinsetFourier A k ≠ 0) :
    ((fourierDirectionCircle A k hF : Circle) : ℂ) =
      starRingEnd ℂ (cyclicFinsetFourier A k) /
        ‖cyclicFinsetFourier A k‖ := rfl

lemma positiveHalf_mem_rotated_centeredArc
    (A : Finset (ZMod N)) (k : ZMod N)
    (hF : cyclicFinsetFourier A k ≠ 0)
    {x : ZMod N} (hx : x ∈ fourierPositiveHalf A k) :
    fourierDirectionCircle A k hF * ZMod.toCircle (-(x * k)) ∈
      Circle.centeredArc (Real.pi / 2) := by
  rw [circle_mem_centeredArc_pi_div_two_iff_re_pos]
  simp only [fourierPositiveHalf, Finset.mem_filter] at hx
  have hpos := hx.2
  have hnorm : 0 < ‖cyclicFinsetFourier A k‖ :=
    (norm_pos_iff.mpr hF)
  change 0 < ((starRingEnd ℂ (cyclicFinsetFourier A k) /
      ‖cyclicFinsetFourier A k‖) *
      ZMod.stdAddChar (-(x * k))).re
  rw [div_mul_eq_mul_div]
  rw [Complex.div_ofReal_re]
  exact div_pos hpos hnorm

end Erdos336
