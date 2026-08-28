import Mathlib.Analysis.Complex.HasPrimitives

/-!
# Removing a straight line from the holomorphy hypothesis

A continuous function on an open complex domain is holomorphic if it is
holomorphic away from the real axis.  The proof splits each Cauchy rectangle
at the real axis and then applies the rectangle form of Morera's theorem.
This is the analytic gluing step in Schwarz reflection; continuity along
the axis is a genuine hypothesis here, not an asserted boundary extension.
-/

noncomputable section

open Complex Filter Metric Set MeasureTheory
open scoped Topology Interval

namespace Wikipedia.HopfProblem.SchwarzReflection

/-- The oriented integral around an axis-parallel rectangle. -/
def rectangleIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) -
    (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
    I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

theorem rectangleIntegral_eq_wedges (f : ℂ → ℂ) (z w : ℂ) :
    rectangleIntegral f z w = wedgeIntegral z w f + wedgeIntegral w z f := by
  rw [wedgeIntegral_add_wedgeIntegral_eq]
  rfl

theorem horizontal_line_mem_rectangle {z w : ℂ} {x y : ℝ}
    (hx : x ∈ [[z.re, w.re]]) (hy : y ∈ [[z.im, w.im]]) :
    (x : ℂ) + y * I ∈ Rectangle z w := by
  simpa only [Rectangle, mem_reProdIm, add_re, ofReal_re, mul_re, ofReal_im,
    I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero, add_im, mul_im,
    mul_one, zero_add] using And.intro hx hy

theorem continuousOn_vertical_integrable {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f (Rectangle z w)) {x : ℝ}
    (hx : x ∈ [[z.re, w.re]]) {a b : ℝ}
    (hab : [[a, b]] ⊆ [[z.im, w.im]]) :
    IntervalIntegrable (fun y : ℝ => f (x + y * I)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply hf.comp (by fun_prop)
  intro y hy
  exact horizontal_line_mem_rectangle hx (hab hy)

/-- Cutting a rectangle at a horizontal line adds its two boundary
integrals; the common horizontal edge cancels exactly. -/
theorem rectangleIntegral_split {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f (Rectangle z w)) {a : ℝ}
    (ha : a ∈ [[z.im, w.im]]) :
    rectangleIntegral f z w =
      rectangleIntegral f z (w.re + a * I) +
        rectangleIntegral f (z.re + a * I) w := by
  have hz : [[z.im, a]] ⊆ [[z.im, w.im]] :=
    uIcc_subset_uIcc (left_mem_uIcc) ha
  have hw : [[a, w.im]] ⊆ [[z.im, w.im]] :=
    uIcc_subset_uIcc ha (right_mem_uIcc)
  have hright := intervalIntegral.integral_add_adjacent_intervals
    (continuousOn_vertical_integrable hf (right_mem_uIcc) hz)
    (continuousOn_vertical_integrable hf (right_mem_uIcc) hw)
  have hleft := intervalIntegral.integral_add_adjacent_intervals
    (continuousOn_vertical_integrable hf (left_mem_uIcc) hz)
    (continuousOn_vertical_integrable hf (left_mem_uIcc) hw)
  simp only [rectangleIntegral, add_re, ofReal_re, mul_re, ofReal_im,
    I_re, I_im, mul_zero, sub_zero, add_zero, add_im, mul_im,
    mul_one, zero_add]
  rw [← hright, ← hleft]
  ring

theorem rectangle_split_lower_subset {z w : ℂ} {a : ℝ}
    (ha : a ∈ [[z.im, w.im]]) :
    Rectangle z (w.re + a * I) ⊆ Rectangle z w := by
  have hsub : [[z.im, a]] ⊆ [[z.im, w.im]] :=
    uIcc_subset_uIcc left_mem_uIcc ha
  intro x hx
  simp only [Rectangle, mem_reProdIm, add_re, ofReal_re, mul_re, ofReal_im,
    I_re, I_im, mul_zero, sub_zero, add_zero, add_im, mul_im,
    mul_one, zero_add] at hx ⊢
  exact ⟨hx.1, hsub hx.2⟩

theorem rectangle_split_upper_subset {z w : ℂ} {a : ℝ}
    (ha : a ∈ [[z.im, w.im]]) :
    Rectangle (z.re + a * I) w ⊆ Rectangle z w := by
  have hsub : [[a, w.im]] ⊆ [[z.im, w.im]] :=
    uIcc_subset_uIcc ha right_mem_uIcc
  intro x hx
  simp only [Rectangle, mem_reProdIm, add_re, ofReal_re, mul_re, ofReal_im,
    I_re, I_im, mul_zero, sub_zero, add_zero, add_im, mul_im,
    mul_one, zero_add] at hx ⊢
  exact ⟨hx.1, hsub hx.2⟩

theorem rectangleIntegral_eq_zero_of_axis_not_interior {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f (Rectangle z w))
    (hd : ∀ x ∈ Rectangle z w, x.im ≠ 0 → DifferentiableAt ℂ f x)
    (haxis : (0 : ℝ) ∉ Ioo (min z.im w.im) (max z.im w.im)) :
    rectangleIntegral f z w = 0 := by
  apply integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    f z w ∅ countable_empty hf
  intro x hx
  have hx' := hx.1
  simp only [mem_reProdIm, mem_Ioo] at hx'
  apply hd x
  · exact ⟨⟨hx'.1.1.le, hx'.1.2.le⟩, ⟨hx'.2.1.le, hx'.2.2.le⟩⟩
  · intro hzero
    apply haxis
    simpa only [hzero, mem_Ioo] using hx'.2

theorem zero_not_mem_open_interval_to_zero (a : ℝ) :
    (0 : ℝ) ∉ Ioo (min a 0) (max a 0) := by
  rcases le_total a 0 with h | h
  · simp [min_eq_left h, max_eq_right h]
  · simp [min_eq_right h, max_eq_left h]

/-- The real axis is removable for a continuous function which is
holomorphic on each side.  No boundary derivative is assumed. -/
theorem differentiableOn_of_continuousOn_off_real {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : ContinuousOn f U)
    (hd : ∀ z ∈ U, z.im ≠ 0 → DifferentiableAt ℂ f z) :
    DifferentiableOn ℂ f U := by
  apply (isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
  refine ⟨?_, hf⟩
  intro z w hzw
  rw [← add_eq_zero_iff_eq_neg, ← rectangleIntegral_eq_wedges]
  have hc := hf.mono hzw
  have hd' : ∀ x ∈ Rectangle z w, x.im ≠ 0 → DifferentiableAt ℂ f x :=
    fun x hx => hd x (hzw hx)
  by_cases haxis : (0 : ℝ) ∈ Ioo (min z.im w.im) (max z.im w.im)
  · have haxis' : (0 : ℝ) ∈ [[z.im, w.im]] := ⟨haxis.1.le, haxis.2.le⟩
    rw [rectangleIntegral_split hc haxis']
    have hlow := rectangle_split_lower_subset (z := z) (w := w) haxis'
    have hhigh := rectangle_split_upper_subset (z := z) (w := w) haxis'
    have h₁ : rectangleIntegral f z (w.re + (0 : ℝ) * I) = 0 := by
      apply rectangleIntegral_eq_zero_of_axis_not_interior (hc.mono hlow)
        (fun x hx => hd' x (hlow hx))
      simpa using zero_not_mem_open_interval_to_zero z.im
    have h₂ : rectangleIntegral f (z.re + (0 : ℝ) * I) w = 0 := by
      apply rectangleIntegral_eq_zero_of_axis_not_interior (hc.mono hhigh)
        (fun x hx => hd' x (hhigh hx))
      simpa [min_comm, max_comm] using zero_not_mem_open_interval_to_zero w.im
    rw [h₁, h₂, add_zero]
  · exact rectangleIntegral_eq_zero_of_axis_not_interior hc hd' haxis

theorem analyticOnNhd_of_continuousOn_off_real {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : ContinuousOn f U)
    (hd : ∀ z ∈ U, z.im ≠ 0 → DifferentiableAt ℂ f z) :
    AnalyticOnNhd ℂ f U :=
  (differentiableOn_of_continuousOn_off_real hU hf hd).analyticOnNhd hU

end Wikipedia.HopfProblem.SchwarzReflection
