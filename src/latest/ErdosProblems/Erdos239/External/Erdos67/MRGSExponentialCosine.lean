import Mathlib

/-!
# The elementary exponential--cosine inequality in the GS argument

This is the real-variable inequality used in the maximum-modulus step of
the Granville--Soundararajan proof.  Complex normalizations are recorded
separately below.
-/

namespace Erdos67

noncomputable section

/-- Increasing `exp (sqrt x)` from `a²` to `a²+t²` gains at least `t²`. -/
theorem exp_abs_add_sq_le_exp_sqrt_sq_add_sq (a t : ℝ) :
    Real.exp |a| + t ^ 2 ≤ Real.exp (Real.sqrt (a ^ 2 + t ^ 2)) := by
  by_cases ht : t = 0
  · subst t
    simp [Real.sqrt_sq_eq_abs]
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  let lo : ℝ := |a| ^ 2
  let hi : ℝ := |a| ^ 2 + t ^ 2
  let h : ℝ → ℝ := fun x ↦ Real.exp (Real.sqrt x)
  have hlohi : lo < hi := by
    dsimp only [lo, hi]
    linarith
  have hcont : ContinuousOn h (Set.Icc lo hi) :=
    (Real.continuous_exp.comp Real.continuous_sqrt).continuousOn
  have hdiff : DifferentiableOn ℝ h (interior (Set.Icc lo hi)) := by
    intro x hx
    have hxIoo : x ∈ Set.Ioo lo hi := by
      simpa [interior_Icc, hlohi] using hx
    have hxpos : 0 < x :=
      (show 0 ≤ lo by dsimp only [lo]; positivity).trans_lt hxIoo.1
    exact ((Real.hasDerivAt_exp (Real.sqrt x)).comp x
      (Real.hasDerivAt_sqrt hxpos.ne')).differentiableAt.differentiableWithinAt
  have hderiv : ∀ x ∈ interior (Set.Icc lo hi), (1 : ℝ) ≤ deriv h x := by
    intro x hx
    have hxIoo : x ∈ Set.Ioo lo hi := by
      simpa [interior_Icc, hlohi] using hx
    have hxpos : 0 < x :=
      (show 0 ≤ lo by dsimp only [lo]; positivity).trans_lt hxIoo.1
    have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
    have hquad := Real.quadratic_le_exp_of_nonneg hsqrtpos.le
    have htwo : 2 * Real.sqrt x ≤ Real.exp (Real.sqrt x) := by
      nlinarith [sq_nonneg (Real.sqrt x - 1)]
    have hratio : (1 : ℝ) ≤
        Real.exp (Real.sqrt x) / (2 * Real.sqrt x) :=
      (le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt x)).2 (by
        simpa using htwo)
    have hd := (Real.hasDerivAt_exp (Real.sqrt x)).comp x
      (Real.hasDerivAt_sqrt hxpos.ne')
    change (1 : ℝ) ≤ deriv (fun y : ℝ ↦ Real.exp (Real.sqrt y)) x
    rw [show deriv (fun y : ℝ ↦ Real.exp (Real.sqrt y)) x =
      Real.exp (Real.sqrt x) * (1 / (2 * Real.sqrt x)) by exact hd.deriv]
    simpa [div_eq_mul_inv] using hratio
  have hgrow := (convex_Icc lo hi).mul_sub_le_image_sub_of_le_deriv
    hcont hdiff hderiv (x := lo) (y := hi)
    (Set.left_mem_Icc.mpr hlohi.le) (Set.right_mem_Icc.mpr hlohi.le) hlohi.le
  have hsqrtlo : Real.sqrt lo = |a| := by
    dsimp only [lo]
    rw [Real.sqrt_sq_eq_abs, abs_abs]
  have hsqrthi : Real.sqrt hi = Real.sqrt (a ^ 2 + t ^ 2) := by
    dsimp only [hi]
    rw [sq_abs]
  dsimp only [h] at hgrow
  rw [hsqrtlo, hsqrthi] at hgrow
  dsimp only [lo, hi] at hgrow
  linarith

/-- Source inequality (A.12): the symmetric real exponential and cosine
combination is controlled by the radial exponential. -/
theorem exp_add_exp_neg_sub_two_cos_le_exp_sqrt_sq_add_sq (a t : ℝ) :
    Real.exp a + Real.exp (-a) - 2 * Real.cos t ≤
      Real.exp (Real.sqrt (a ^ 2 + t ^ 2)) := by
  have hmain := exp_abs_add_sq_le_exp_sqrt_sq_add_sq a t
  have hcos := Real.one_sub_sq_div_two_le_cos (x := t)
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha] at hmain
    have hneg : Real.exp (-a) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)
    nlinarith
  · have ha' : a ≤ 0 := le_of_not_ge ha
    rw [abs_of_nonpos ha'] at hmain
    have hpos : Real.exp a ≤ 1 := Real.exp_le_one_iff.mpr ha'
    nlinarith

/-- Exact Euler-factor normalization underlying (A.12). -/
theorem normSq_one_sub_exp_neg_add_mul_I (a t : ℝ) :
    Complex.normSq
        (1 - Complex.exp ((-a : ℂ) + Complex.I * (t : ℂ))) =
      Real.exp (-a) *
        (Real.exp a + Real.exp (-a) - 2 * Real.cos t) := by
  rw [Complex.normSq_sub]
  simp only [Complex.normSq_eq_norm_sq, Complex.norm_exp, one_mul]
  simp [Complex.exp_re, Real.exp_neg]
  field_simp [Real.exp_ne_zero]

/-- Complex Euler-factor form of (A.12), normalized exactly as used in the
maximum-modulus argument. -/
theorem normSq_one_sub_exp_neg_add_mul_I_le (a t : ℝ) (_ha : 0 ≤ a) :
    Complex.normSq
        (1 - Complex.exp ((-a : ℂ) + Complex.I * (t : ℂ))) ≤
      Real.exp (-a + Real.sqrt (a ^ 2 + t ^ 2)) := by
  have hreal := exp_add_exp_neg_sub_two_cos_le_exp_sqrt_sq_add_sq a t
  have hscale := mul_le_mul_of_nonneg_left hreal (Real.exp_pos (-a)).le
  rw [normSq_one_sub_exp_neg_add_mul_I]
  calc
    Real.exp (-a) *
        (Real.exp a + Real.exp (-a) - 2 * Real.cos t)
        ≤ Real.exp (-a) * Real.exp (Real.sqrt (a ^ 2 + t ^ 2)) := hscale
    _ = Real.exp (-a + Real.sqrt (a ^ 2 + t ^ 2)) := by
      rw [Real.exp_add]

/-- Norm form of the complex Euler-factor inequality. -/
theorem norm_one_sub_exp_neg_add_mul_I_le (a t : ℝ) (ha : 0 ≤ a) :
    ‖1 - Complex.exp ((-a : ℂ) + Complex.I * (t : ℂ))‖ ≤
      Real.exp ((-a + Real.sqrt (a ^ 2 + t ^ 2)) / 2) := by
  have hsq := normSq_one_sub_exp_neg_add_mul_I_le a t ha
  rw [Complex.normSq_eq_norm_sq] at hsq
  have hexp :
      Real.exp ((-a + Real.sqrt (a ^ 2 + t ^ 2)) / 2) ^ 2 =
        Real.exp (-a + Real.sqrt (a ^ 2 + t ^ 2)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [← hexp] at hsq
  nlinarith [norm_nonneg
    (1 - Complex.exp ((-a : ℂ) + Complex.I * (t : ℂ))),
    Real.exp_pos ((-a + Real.sqrt (a ^ 2 + t ^ 2)) / 2)]

end

end Erdos67
