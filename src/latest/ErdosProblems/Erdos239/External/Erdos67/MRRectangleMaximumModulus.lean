import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Maximum modulus on a closed rectangle

This small wrapper packages the form of the maximum-modulus principle used
in the finite Halasz contour argument.  The analytic function is controlled
separately on the four sides of an open rectangle; the conclusion holds on
the corresponding closed rectangle.
-/

open Set Complex

namespace Erdos67

noncomputable section

/-- A complex-differentiable function bounded by `C` on all four sides of a
rectangle is bounded by `C` throughout its closure. -/
theorem norm_le_on_closedRectangle_of_four_sides
    {f : ℂ → ℂ} {a b c d C : ℝ}
    (hab : a < b) (hcd : c < d)
    (hf : DiffContOnCl ℂ f (Ioo a b ×ℂ Ioo c d))
    (hleft : ∀ y ∈ Icc c d, ‖f ((a : ℂ) + Complex.I * y)‖ ≤ C)
    (hright : ∀ y ∈ Icc c d, ‖f ((b : ℂ) + Complex.I * y)‖ ≤ C)
    (hbottom : ∀ x ∈ Icc a b, ‖f ((x : ℂ) + Complex.I * c)‖ ≤ C)
    (htop : ∀ x ∈ Icc a b, ‖f ((x : ℂ) + Complex.I * d)‖ ≤ C)
    {z : ℂ} (hzre : z.re ∈ Icc a b) (hzim : z.im ∈ Icc c d) :
    ‖f z‖ ≤ C := by
  apply norm_le_of_forall_mem_frontier_norm_le
    ((Metric.isBounded_Ioo a b).reProdIm (Metric.isBounded_Ioo c d)) hf
  · intro w hw
    rw [frontier_reProdIm, closure_Ioo hab.ne, frontier_Ioo hcd,
      closure_Ioo hcd.ne, frontier_Ioo hab] at hw
    rcases hw with hw | hw
    · rcases hw.2 with hwc | hwd
      · have hrepr : w = (w.re : ℂ) + Complex.I * c := by
          apply Complex.ext
          · simp
          · simpa using hwc
        rw [hrepr]
        exact hbottom w.re hw.1
      · have hrepr : w = (w.re : ℂ) + Complex.I * d := by
          apply Complex.ext
          · simp
          · simpa using hwd
        rw [hrepr]
        exact htop w.re hw.1
    · rcases hw.1 with hwa | hwb
      · have hrepr : w = (a : ℂ) + Complex.I * w.im := by
          apply Complex.ext
          · simpa using hwa
          · simp
        rw [hrepr]
        exact hleft w.im hw.2
      · have hrepr : w = (b : ℂ) + Complex.I * w.im := by
          apply Complex.ext
          · simpa using hwb
          · simp
        rw [hrepr]
        exact hright w.im hw.2
  · rw [closure_reProdIm, closure_Ioo hab.ne, closure_Ioo hcd.ne]
    exact ⟨hzre, hzim⟩

/-- The L-series of a one-bounded coefficient is differentiable on, and
continuous up to, every rectangle whose closed real projection lies strictly
to the right of `1`. -/
theorem LSeries_diffContOnCl_rectangle_of_oneBounded
    {u : ℕ → ℂ} (hu : ∀ n : ℕ, n ≠ 0 → ‖u n‖ ≤ 1)
    {a b c d : ℝ} (ha : 1 < a) (hab : a < b) (hcd : c < d) :
    DiffContOnCl ℂ (LSeries u) (Ioo a b ×ℂ Ioo c d) := by
  have hmid : 1 < (a + 1) / 2 := by linarith
  have hsum : LSeriesSummable u ((((a + 1) / 2 : ℝ) : ℂ)) :=
    LSeriesSummable_of_bounded_of_one_lt_re hu (by simpa using hmid)
  have habs : LSeries.abscissaOfAbsConv u < (a : ℝ) := by
    calc
      LSeries.abscissaOfAbsConv u ≤ ((((a + 1) / 2 : ℝ) : EReal)) := by
        simpa using hsum.abscissaOfAbsConv_le
      _ < (a : ℝ) := by
        exact_mod_cast (by linarith : (a + 1) / 2 < a)
  apply DifferentiableOn.diffContOnCl
  rw [closure_reProdIm, closure_Ioo hab.ne, closure_Ioo hcd.ne]
  intro z hz
  have hzr : (a : EReal) ≤ (z.re : EReal) := by
    exact_mod_cast hz.1.1
  exact (LSeries_hasDerivAt (habs.trans_le hzr)).differentiableAt.differentiableWithinAt

/-- Direct L-series specialization of the four-side rectangle principle. -/
theorem norm_LSeries_le_on_closedRectangle_of_four_sides
    {u : ℕ → ℂ} (hu : ∀ n : ℕ, n ≠ 0 → ‖u n‖ ≤ 1)
    {a b c d C : ℝ} (ha : 1 < a) (hab : a < b) (hcd : c < d)
    (hleft : ∀ y ∈ Icc c d,
      ‖LSeries u ((a : ℂ) + Complex.I * y)‖ ≤ C)
    (hright : ∀ y ∈ Icc c d,
      ‖LSeries u ((b : ℂ) + Complex.I * y)‖ ≤ C)
    (hbottom : ∀ x ∈ Icc a b,
      ‖LSeries u ((x : ℂ) + Complex.I * c)‖ ≤ C)
    (htop : ∀ x ∈ Icc a b,
      ‖LSeries u ((x : ℂ) + Complex.I * d)‖ ≤ C)
    {z : ℂ} (hzre : z.re ∈ Icc a b) (hzim : z.im ∈ Icc c d) :
    ‖LSeries u z‖ ≤ C := by
  exact norm_le_on_closedRectangle_of_four_sides hab hcd
    (LSeries_diffContOnCl_rectangle_of_oneBounded hu ha hab hcd)
    hleft hright hbottom htop hzre hzim

end

end Erdos67
