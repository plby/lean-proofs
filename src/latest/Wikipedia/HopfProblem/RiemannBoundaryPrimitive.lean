import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Primitives on rectangles with bounded derivative

The primitive is the actual horizontal-then-vertical wedge integral. Cauchy's
theorem on rectangles identifies its local increments with wedge integrals
centered at the point of differentiation. A bounded holomorphic function then
has a primitive that extends continuously to the entire plane.

The wedge-additivity argument adapts the proof in mathlib's
`Analysis.Complex.HasPrimitives`, by Ian Jauslin, Alex Kontorovich and Oliver Nash
(Apache 2.0).
-/

noncomputable section

open Complex MeasureTheory Metric Set Filter Topology
open scoped Interval NNReal

namespace Wikipedia.HopfProblem.RiemannBoundary

/-- An open axis-aligned rectangle in the complex plane. -/
def openRectangle (a b c d : ℝ) : Set ℂ :=
  {z | z.re ∈ Ioo a b ∧ z.im ∈ Ioo c d}

theorem isOpen_openRectangle (a b c d : ℝ) : IsOpen (openRectangle a b c d) :=
  isOpen_Ioo.reProdIm isOpen_Ioo

theorem convex_openRectangle (a b c d : ℝ) : Convex ℝ (openRectangle a b c d) :=
  ((convex_halfSpace_re_gt a).inter (convex_halfSpace_re_lt b)).inter
    ((convex_halfSpace_im_gt c).inter (convex_halfSpace_im_lt d))

variable {a b c d : ℝ}

theorem mixed_mem_openRectangle {z w : ℂ}
    (hz : z ∈ openRectangle a b c d) (hw : w ∈ openRectangle a b c d) :
    z.re + w.im * I ∈ openRectangle a b c d := by
  simpa only [openRectangle, mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re,
    ofReal_im, I_im, mul_zero, zero_mul, sub_zero, add_zero, add_im, mul_im,
    mul_one, zero_add] using And.intro hz.1 hw.2

theorem rectangle_subset_openRectangle {z w : ℂ}
    (hz : z ∈ openRectangle a b c d) (hw : w ∈ openRectangle a b c d) :
    Rectangle z w ⊆ openRectangle a b c d :=
  (convex_openRectangle a b c d).rectangle_subset hz hw
    (mixed_mem_openRectangle hz hw) (mixed_mem_openRectangle hw hz)

private theorem horizontal_segment_subset {x₁ x₂ y : ℝ}
    (h₁ : (x₁ : ℂ) + y * I ∈ openRectangle a b c d)
    (h₂ : (x₂ : ℂ) + y * I ∈ openRectangle a b c d) :
    (fun x : ℝ => (x : ℂ) + y * I) '' [[x₁, x₂]] ⊆ openRectangle a b c d := by
  convert rectangle_subset_openRectangle h₁ h₂ using 1
  simp [horizontalSegment_eq x₁ x₂ y, Rectangle]

private theorem vertical_segment_subset {x y₁ y₂ : ℝ}
    (h₁ : (x : ℂ) + y₁ * I ∈ openRectangle a b c d)
    (h₂ : (x : ℂ) + y₂ * I ∈ openRectangle a b c d) :
    (fun y : ℝ => (x : ℂ) + y * I) '' [[y₁, y₂]] ⊆ openRectangle a b c d := by
  convert rectangle_subset_openRectangle h₁ h₂ using 1
  simp [verticalSegment_eq x y₁ y₂, Rectangle]

variable {f : ℂ → ℂ}

/-- Additivity of actual wedge integrals in an open rectangle. -/
theorem wedgeIntegral_sub_wedgeIntegral_openRectangle
    (hc : ContinuousOn f (openRectangle a b c d))
    (hf : IsConservativeOn f (openRectangle a b c d))
    {p z w : ℂ} (hp : p ∈ openRectangle a b c d)
    (hz : z ∈ openRectangle a b c d) (hw : w ∈ openRectangle a b c d) :
    wedgeIntegral p w f - wedgeIntegral p z f = wedgeIntegral z w f := by
  have integrableHoriz (x₁ x₂ y : ℝ)
      (h₁ : (x₁ : ℂ) + y * I ∈ openRectangle a b c d)
      (h₂ : (x₂ : ℂ) + y * I ∈ openRectangle a b c d) :
      IntervalIntegrable (fun x : ℝ => f (x + y * I)) volume x₁ x₂ :=
    ((hc.mono (horizontal_segment_subset h₁ h₂)).comp (by fun_prop)
      (mapsTo_image _ _)).intervalIntegrable
  have integrableVert (x y₁ y₂ : ℝ)
      (h₁ : (x : ℂ) + y₁ * I ∈ openRectangle a b c d)
      (h₂ : (x : ℂ) + y₂ * I ∈ openRectangle a b c d) :
      IntervalIntegrable (fun y : ℝ => f (x + y * I)) volume y₁ y₂ :=
    ((hc.mono (vertical_segment_subset h₁ h₂)).comp (by fun_prop)
      (mapsTo_image _ _)).intervalIntegrable
  have hHoriz :
      (∫ x in p.re..w.re, f (x + p.im * I)) =
        (∫ x in p.re..z.re, f (x + p.im * I)) +
          (∫ x in z.re..w.re, f (x + p.im * I)) := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · apply integrableHoriz
      · simpa only [re_add_im] using hp
      · exact mixed_mem_openRectangle hz hp
    · apply integrableHoriz
      · exact mixed_mem_openRectangle hz hp
      · exact mixed_mem_openRectangle hw hp
  have hVert :
      I * (∫ y in p.im..w.im, f (w.re + y * I)) =
        I * (∫ y in p.im..z.im, f (w.re + y * I)) +
          I * (∫ y in z.im..w.im, f (w.re + y * I)) := by
    rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals]
    · apply integrableVert
      · exact mixed_mem_openRectangle hw hp
      · exact mixed_mem_openRectangle hw hz
    · apply integrableVert
      · exact mixed_mem_openRectangle hw hz
      · simpa only [re_add_im] using hw
  have hRect := hf (z.re + p.im * I) (w.re + z.im * I)
    (rectangle_subset_openRectangle (mixed_mem_openRectangle hz hp)
      (mixed_mem_openRectangle hw hz))
  have hBoundary :
      (∫ x in z.re..w.re, f (x + p.im * I)) -
        (∫ x in z.re..w.re, f (x + z.im * I)) +
        I * (∫ y in p.im..z.im, f (w.re + y * I)) -
        I * (∫ y in p.im..z.im, f (z.re + y * I)) = 0 := by
    simpa [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq]
      using hRect
  simp only [wedgeIntegral, smul_eq_mul]
  rw [hHoriz, hVert]
  linear_combination hBoundary

/-- The rectangular wedge integral differentiates to the original holomorphic
function at every interior point. -/
theorem hasDerivAt_wedgeIntegral_openRectangle
    (hf : DifferentiableOn ℂ f (openRectangle a b c d))
    {p z : ℂ} (hp : p ∈ openRectangle a b c d)
    (hz : z ∈ openRectangle a b c d) :
    HasDerivAt (fun w => wedgeIntegral p w f) (f z) z := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp (isOpen_openRectangle a b c d) z hz
  have hd : HasDerivAt (fun w => wedgeIntegral z w f) (f z) z :=
    (hf.isConservativeOn.mono hsub).hasDerivAt_wedgeIntegral
      (hf.continuousOn.mono hsub) (mem_ball_self hr)
  apply (hd.add_const (wedgeIntegral p z f)).congr_of_eventuallyEq
  filter_upwards [(isOpen_openRectangle a b c d).mem_nhds hz] with w hw
  exact sub_eq_iff_eq_add.mp
    (wedgeIntegral_sub_wedgeIntegral_openRectangle hf.continuousOn
      hf.isConservativeOn hp hz hw)

/-- Every holomorphic function on an open axis-aligned rectangle has an actual
primitive. Empty rectangles are allowed. -/
theorem isExactOn_openRectangle
    (hf : DifferentiableOn ℂ f (openRectangle a b c d)) :
    IsExactOn f (openRectangle a b c d) := by
  by_cases h : (openRectangle a b c d).Nonempty
  · obtain ⟨p, hp⟩ := h
    exact ⟨fun z => wedgeIntegral p z f,
      fun _ hz => hasDerivAt_wedgeIntegral_openRectangle hf hp hz⟩
  · refine ⟨fun _ => 0, fun z hz => ?_⟩
    exact (h ⟨z, hz⟩).elim

/-- Bounded derivative on a rectangle gives a global Lipschitz extension of a
primitive, with its complex derivative unchanged in the rectangle. -/
theorem exists_lipschitz_extension_primitive_openRectangle
    {F : ℂ → ℂ} {K : ℝ≥0}
    (hF : ∀ z ∈ openRectangle a b c d, HasDerivAt F (f z) z)
    (hb : ∀ z ∈ openRectangle a b c d, ‖f z‖₊ ≤ K) :
    ∃ G : ℂ → ℂ, LipschitzWith (lipschitzExtensionConstant ℂ * K) G ∧
      EqOn F G (openRectangle a b c d) ∧
      ∀ z ∈ openRectangle a b c d, HasDerivAt G (f z) z := by
  have hLip : LipschitzOnWith K F (openRectangle a b c d) :=
    (convex_openRectangle a b c d).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun z hz => (hF z hz).hasDerivWithinAt) hb
  obtain ⟨G, hG, heq⟩ := hLip.extend_finite_dimension
  refine ⟨G, hG, heq, fun z hz => ?_⟩
  apply (hF z hz).congr_of_eventuallyEq
  filter_upwards [(isOpen_openRectangle a b c d).mem_nhds hz] with w hw
  exact (heq hw).symm

/-- A bounded holomorphic function on an open rectangle has a primitive that is
continuous on the entire complex plane. -/
theorem exists_continuous_primitive_openRectangle
    {K : ℝ≥0} (hf : DifferentiableOn ℂ f (openRectangle a b c d))
    (hb : ∀ z ∈ openRectangle a b c d, ‖f z‖₊ ≤ K) :
    ∃ G : ℂ → ℂ, Continuous G ∧
      ∀ z ∈ openRectangle a b c d, HasDerivAt G (f z) z := by
  obtain ⟨F, hF⟩ := isExactOn_openRectangle hf
  obtain ⟨G, hG, _, hd⟩ := exists_lipschitz_extension_primitive_openRectangle hF hb
  exact ⟨G, hG.continuous, hd⟩

/-- Real norm-bound version; no separate sign assumption on the bound is needed. -/
theorem exists_continuous_primitive_openRectangle_of_norm_le
    {M : ℝ} (hf : DifferentiableOn ℂ f (openRectangle a b c d))
    (hb : ∀ z ∈ openRectangle a b c d, ‖f z‖ ≤ M) :
    ∃ G : ℂ → ℂ, Continuous G ∧
      ∀ z ∈ openRectangle a b c d, HasDerivAt G (f z) z := by
  apply exists_continuous_primitive_openRectangle (K := M.toNNReal) hf
  intro z hz
  exact_mod_cast (hb z hz).trans (Real.le_coe_toNNReal M)

/-- Bounded-image version of the continuous primitive theorem. -/
theorem exists_continuous_primitive_openRectangle_of_bounded
    (hf : DifferentiableOn ℂ f (openRectangle a b c d))
    (hb : Bornology.IsBounded (f '' openRectangle a b c d)) :
    ∃ G : ℂ → ℂ, Continuous G ∧
      ∀ z ∈ openRectangle a b c d, HasDerivAt G (f z) z := by
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  exact exists_continuous_primitive_openRectangle_of_norm_le hf
    (fun z hz => hM (f z) (mem_image_of_mem f hz))

end Wikipedia.HopfProblem.RiemannBoundary
