import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! # A normalized analytic logarithm on a nonvanishing disk -/

namespace Erdos421

open Metric

/-- Constructing the logarithm from a primitive of `f'/f` also proves its
derivative formula. The nonvanishing hypothesis is local to this general lemma. -/
theorem exists_normalized_log_on_ball {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hzero : ∀ z ∈ ball c R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, g c = 0 ∧
      (∀ z ∈ ball c R, HasDerivAt g (deriv f z / f z) z) ∧
      ∀ z ∈ ball c R, Complex.exp (g z) = f z / f c := by
  have hc : c ∈ ball c R := mem_ball_self hR
  have hlogderiv : DifferentiableOn ℂ (fun z ↦ deriv f z / f z) (ball c R) :=
    (hf.deriv isOpen_ball).div hf hzero
  obtain ⟨g, hgc, hg⟩ := hlogderiv.isExactOn_ball.with_val_at c 0
  refine ⟨g, hgc, hg, ?_⟩
  let F : ℂ → ℂ := fun z ↦ f z * Complex.exp (-g z)
  have hd : ∀ z ∈ ball c R, HasDerivAt F 0 z := by
    intro z hz
    have hfz := (hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have hgz := (hg z hz).neg.cexp
    have hprod := hfz.mul hgz
    have he : deriv f z * Complex.exp (-g z) +
        f z * (Complex.exp (-g z) * -(deriv f z / f z)) = 0 := by
      field_simp [hzero z hz]
      ring
    convert! hprod using 1
    simpa only [Pi.neg_apply] using he.symm
  intro z hz
  have hnorm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun w hw ↦ (hd w hw).hasDerivWithinAt)
    (fun _ _ ↦ (show ‖(0 : ℂ)‖ ≤ (0 : ℝ) by simp)) (convex_ball c R) hc hz
  have hFc : F z = F c := by
    apply sub_eq_zero.mp
    apply norm_le_zero_iff.mp
    simpa only [zero_mul] using hnorm
  have heq : f z * Complex.exp (-g z) = f c := by
    simpa only [F, hgc, neg_zero, Complex.exp_zero, mul_one] using hFc
  rw [Complex.exp_neg, ← div_eq_mul_inv] at heq
  have hm := (div_eq_iff (Complex.exp_ne_zero (g z))).mp heq
  apply (eq_div_iff (hzero c hc)).mpr
  simpa only [mul_comm] using hm.symm

end Erdos421
