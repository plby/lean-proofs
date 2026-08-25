import Util.Bernays.AnalyticSquareDerivative
import Mathlib.Analysis.Complex.Convex

/-!
# Uniform square-root bounds along a vertical boundary
-/

open Set Metric Filter Topology

namespace Bernays

theorem halfPlane_differentiableOn {F : ℂ → ℂ} {c : ℝ}
    (hF : ∀ z : ℂ, c < z.re → DifferentiableAt ℂ F z) :
    DifferentiableOn ℂ F {z : ℂ | c < z.re} :=
  fun z hz => (hF z hz).differentiableWithinAt

theorem halfPlane_deriv_continuousOn {F : ℂ → ℂ} {c : ℝ}
    (hF : ∀ z : ℂ, c < z.re → DifferentiableAt ℂ F z) :
    ContinuousOn (deriv F) {z : ℂ | c < z.re} :=
  ((halfPlane_differentiableOn hF).deriv (isOpen_lt continuous_const Complex.continuous_re)).continuousOn

theorem halfPlane_closedBall {δ t : ℝ} (hδ : 0 < δ) :
    closedBall ((1 + δ : ℝ) + t * Complex.I) (δ / 2) ⊆ {z : ℂ | 1 < z.re} := by
  intro z hz
  have hnorm := (mem_closedBall_iff_norm.mp hz)
  have h := (abs_le.mp ((Complex.abs_re_le_norm
    (z - ((1 + δ : ℝ) + t * Complex.I))).trans hnorm)).1
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at h
  change 1 < z.re
  linarith

theorem halfPlane_closedBall_rectangle {δ t T : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (ht : |t| ≤ T) :
    closedBall ((1 + δ : ℝ) + t * Complex.I) (δ / 2) ⊆
      (Icc (3 / 4 : ℝ) 3) ×ℂ (Icc (-T - 1) (T + 1)) := by
  intro z hz
  have hnorm := mem_closedBall_iff_norm.mp hz
  have hr := abs_le.mp ((Complex.abs_re_le_norm
    (z - ((1 + δ : ℝ) + t * Complex.I))).trans hnorm)
  have hi := abs_le.mp ((Complex.abs_im_le_norm
    (z - ((1 + δ : ℝ) + t * Complex.I))).trans hnorm)
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add] at hr hi
  have ht' := abs_le.mp ht
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem halfPlane_square_uniform_bounds {f F : ℂ → ℂ}
    (hf : ∀ z : ℂ, 1 < z.re → DifferentiableAt ℂ f z)
    (hF : ∀ z : ℂ, (1 / 2 : ℝ) < z.re → DifferentiableAt ℂ F z)
    (heq : ∀ z : ℂ, 1 < z.re → F z = f z ^ 2) (T : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ δ t : ℝ, 0 < δ → δ ≤ 1 → |t| ≤ T →
      ‖f ((1 + δ : ℝ) + t * Complex.I)‖ ≤ K ∧
      Real.sqrt δ * ‖deriv f ((1 + δ : ℝ) + t * Complex.I)‖ ≤ K := by
  let S := (Icc (3 / 4 : ℝ) 3) ×ℂ (Icc (-T - 1) (T + 1))
  have hSc : IsCompact S := isCompact_Icc.reProdIm isCompact_Icc
  have hSU : S ⊆ {z : ℂ | (1 / 2 : ℝ) < z.re} := fun z hz => by
    have hz' : 3 / 4 ≤ z.re := hz.1.1
    change 1 / 2 < z.re
    linarith
  obtain ⟨A, hA⟩ := hSc.exists_bound_of_continuousOn
    ((halfPlane_differentiableOn hF).continuousOn.mono hSU)
  obtain ⟨B, hB⟩ := hSc.exists_bound_of_continuousOn
    ((halfPlane_deriv_continuousOn hF).mono hSU)
  let L := max 1 B
  refine ⟨Real.sqrt (max 0 A) + 2 * (L + 1) + 1, by
    have := le_max_left (1 : ℝ) B
    have := Real.sqrt_nonneg (max 0 A)
    dsimp only [L]
    linarith, ?_⟩
  intro δ t hδ hδ₁ ht
  let z : ℂ := (1 + δ : ℝ) + t * Complex.I
  have hball := halfPlane_closedBall hδ (t := t)
  have hrect := halfPlane_closedBall_rectangle hδ hδ₁ ht
  have hz : z ∈ closedBall z (δ / 2) := mem_closedBall_self (by positivity)
  have hval : ‖f z‖ ≤ Real.sqrt (max 0 A) :=
    norm_le_sqrt_of_sq_eq (heq z (hball hz)).symm ((hA z (hrect hz)).trans (le_max_right _ _))
  have hdiff : DiffContOnCl ℂ f (ball z (δ / 2)) :=
    (halfPlane_differentiableOn hf).diffContOnCl_ball hball
  have hder := sqrt_mul_norm_deriv_le_of_deriv_bound (half_pos hδ) (le_max_left 1 B) hdiff
    (fun w hw => hF w (hSU (hrect hw))) (fun w hw => heq w (hball hw))
    (fun w hw => (hB w (hrect hw)).trans (le_max_right 1 B))
  have hsqrt : Real.sqrt δ ≤ 2 * Real.sqrt (δ / 2) := by
    have h₁ := Real.sq_sqrt hδ.le
    have h₂ := Real.sq_sqrt (show 0 ≤ δ / 2 by positivity)
    nlinarith [Real.sqrt_nonneg δ, Real.sqrt_nonneg (δ / 2)]
  have hmul := mul_le_mul_of_nonneg_right hsqrt (norm_nonneg (deriv f z))
  have hL : 1 ≤ L := le_max_left 1 B
  have hnonneg := Real.sqrt_nonneg (max 0 A)
  constructor <;> change _ ≤ Real.sqrt (max 0 A) + 2 * (L + 1) + 1
  · linarith
  · change Real.sqrt (δ / 2) * ‖deriv f z‖ ≤ L + 1 at hder
    change Real.sqrt δ * ‖deriv f z‖ ≤ _
    nlinarith

end Bernays
