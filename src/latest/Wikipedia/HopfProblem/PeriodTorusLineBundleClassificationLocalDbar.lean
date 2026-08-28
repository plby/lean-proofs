import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLocalDbarBasic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Actual local primitives on every polydisc

No compact-support hypothesis is imposed on the closed form.  The two
cutoffs are constructed from smooth bump functions, and the primitive is
the sum of two convergent one-coordinate Cauchy–Green integrals.  Both
antiholomorphic derivative equations are proved on the prescribed bidisc.
-/

noncomputable section

open Complex Set Metric
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

def localizedResidual (χ₁ χ₂ : ℂ → ℂ) (f g : ℂ × ℂ → ℂ) (q : ℂ × ℂ) : ℂ :=
  χ₁ q.1 * firstResidual χ₂ f g q

/-- The actual two-integral local antiholomorphic primitive. -/
def localDbarPrimitive (χ₁ χ₂ : ℂ → ℂ) (f g : ℂ × ℂ → ℂ) (q : ℂ × ℂ) : ℂ :=
  firstCorrection χ₂ g q + cauchyFirst (localizedResidual χ₁ χ₂ f g) q

theorem contDiff_localizedResidual {χ₁ χ₂ : ℂ → ℂ} {f g : ℂ × ℂ → ℂ}
    (hχ₁ : ContDiff ℝ ∞ χ₁) (hχ₂ : ContDiff ℝ ∞ χ₂)
    (hcχ₂ : HasCompactSupport χ₂) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (localizedResidual χ₁ χ₂ f g) :=
  (hχ₁.comp contDiff_fst).mul (contDiff_firstResidual hχ₂ hcχ₂ hf hg)

theorem localizedResidual_eq_zero {χ₁ χ₂ : ℂ → ℂ} {f g : ℂ × ℂ → ℂ}
    (z w : ℂ) (hz : z ∉ tsupport χ₁) : localizedResidual χ₁ χ₂ f g (z, w) = 0 := by
  rw [localizedResidual, image_eq_zero_of_notMem_tsupport hz, zero_mul]

theorem contDiff_localDbarPrimitive {χ₁ χ₂ : ℂ → ℂ} {f g : ℂ × ℂ → ℂ}
    (hχ₁ : ContDiff ℝ ∞ χ₁) (hχ₂ : ContDiff ℝ ∞ χ₂)
    (hcχ₁ : HasCompactSupport χ₁) (hcχ₂ : HasCompactSupport χ₂)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (localDbarPrimitive χ₁ χ₂ f g) :=
  (contDiff_firstCorrection hχ₂ hcχ₂ hg).add
    (contDiff_cauchyFirst (contDiff_localizedResidual hχ₁ hχ₂ hcχ₂ hf hg) hcχ₁
      (fun z w hz => localizedResidual_eq_zero z w hz))

theorem dbarSecond_localizedResidual_eq_zero {χ₁ χ₂ : ℂ → ℂ} {f g : ℂ × ℂ → ℂ}
    (hχ₁ : ContDiff ℝ ∞ χ₁) (hχ₂ : ContDiff ℝ ∞ χ₂)
    (hcχ₂ : HasCompactSupport χ₂) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hclosed : IsDbarClosed f g) (q : ℂ × ℂ) (hq : χ₂ q.2 = 1) :
    dbarSecond (localizedResidual χ₁ χ₂ f g) q = 0 := by
  change dbarSecond (fun x => χ₁ x.1 * firstResidual χ₂ f g x) q = 0
  rw [dbarSecond_mul (f := fun x => χ₁ x.1)
      (((hχ₁.comp contDiff_fst).differentiable (by simp)) q)
      (((contDiff_firstResidual hχ₂ hcχ₂ hf hg).differentiable (by simp)) q),
    dbarSecond_fst, dbarSecond_firstResidual_eq_zero hχ₂ hcχ₂ hf hg hclosed q hq,
    mul_zero, mul_zero, add_zero]

theorem dbarFirst_localDbarPrimitive {χ₁ χ₂ : ℂ → ℂ} {f g : ℂ × ℂ → ℂ}
    (hχ₁ : ContDiff ℝ ∞ χ₁) (hχ₂ : ContDiff ℝ ∞ χ₂)
    (hcχ₁ : HasCompactSupport χ₁) (hcχ₂ : HasCompactSupport χ₂)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (q : ℂ × ℂ) (hq : χ₁ q.1 = 1) :
    dbarFirst (localDbarPrimitive χ₁ χ₂ f g) q = f q := by
  have hv := contDiff_localizedResidual hχ₁ hχ₂ hcχ₂ hf hg
  have hvk := fun z w hz =>
    localizedResidual_eq_zero (χ₁ := χ₁) (χ₂ := χ₂) (f := f) (g := g) z w hz
  change dbarFirst (fun x => firstCorrection χ₂ g x +
    cauchyFirst (localizedResidual χ₁ χ₂ f g) x) q = f q
  rw [dbarFirst_add (((contDiff_firstCorrection hχ₂ hcχ₂ hg).differentiable (by simp)) q)
      (((contDiff_cauchyFirst hv hcχ₁ hvk).differentiable (by simp)) q),
    dbarFirst_cauchyFirst (hv.of_le (by simp)) hcχ₁ hvk,
    localizedResidual, hq, one_mul, firstResidual]
  ring

theorem dbarSecond_localDbarPrimitive {χ₁ χ₂ : ℂ → ℂ} {f g : ℂ × ℂ → ℂ}
    (hχ₁ : ContDiff ℝ ∞ χ₁) (hχ₂ : ContDiff ℝ ∞ χ₂)
    (hcχ₁ : HasCompactSupport χ₁) (hcχ₂ : HasCompactSupport χ₂)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hclosed : IsDbarClosed f g) (q : ℂ × ℂ) (hq : χ₂ q.2 = 1) :
    dbarSecond (localDbarPrimitive χ₁ χ₂ f g) q = g q := by
  have hv := contDiff_localizedResidual hχ₁ hχ₂ hcχ₂ hf hg
  have hvk := fun z w hz =>
    localizedResidual_eq_zero (χ₁ := χ₁) (χ₂ := χ₂) (f := f) (g := g) z w hz
  have he : dbarSecond (cauchyFirst (localizedResidual χ₁ χ₂ f g)) q = 0 := by
    apply dbarSecond_cauchyFirst_eq_zero (U := {w | χ₂ w = 1})
      (hv.of_le (by simp)) hcχ₁ hvk
    · exact fun z w hw => dbarSecond_localizedResidual_eq_zero
        hχ₁ hχ₂ hcχ₂ hf hg hclosed (z, w) hw
    · exact hq
  change dbarSecond (fun x => firstCorrection χ₂ g x +
    cauchyFirst (localizedResidual χ₁ χ₂ f g) x) q = g q
  rw [dbarSecond_add (((contDiff_firstCorrection hχ₂ hcχ₂ hg).differentiable (by simp)) q)
      (((contDiff_cauchyFirst hv hcχ₁ hvk).differentiable (by simp)) q),
    he, add_zero, dbarSecond_firstCorrection hχ₂ hcχ₂ hg,
    secondLocalizedData, hq, one_mul]

/-- A genuine smooth compactly supported complex-valued cutoff that is one
on the requested closed disc. -/
theorem exists_complex_cutoff (R : ℝ) (hR : 0 < R) :
    ∃ χ : ℂ → ℂ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      ∀ z ∈ closedBall (0 : ℂ) R, χ z = 1 := by
  let b : ContDiffBump (0 : ℂ) :=
    { rIn := R
      rOut := R + 1
      rIn_pos := hR
      rIn_lt_rOut := lt_add_one R }
  refine ⟨fun z => (b z : ℂ), Complex.ofRealCLM.contDiff.comp b.contDiff,
    b.hasCompactSupport.comp_left Complex.ofReal_zero, ?_⟩
  intro z hz
  dsimp only
  rw [b.one_of_mem_closedBall hz, Complex.ofReal_one]

/-- Every actual smooth closed `(0,1)` form on `ℂ²` has a smooth primitive on
each prescribed closed bidisc.  Neither coefficient needs compact support. -/
theorem exists_smooth_primitive_on_closedBidisc {f g : ℂ × ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hclosed : IsDbarClosed f g)
    (R : ℝ) (hR : 0 < R) :
    ∃ u : ℂ × ℂ → ℂ, ContDiff ℝ ∞ u ∧ ∀ q ∈ closedBall (0 : ℂ) R ×ˢ closedBall 0 R,
      dbarFirst u q = f q ∧ dbarSecond u q = g q := by
  obtain ⟨χ, hχ, hcχ, hχone⟩ := exists_complex_cutoff R hR
  refine ⟨localDbarPrimitive χ χ f g,
    contDiff_localDbarPrimitive hχ hχ hcχ hcχ hf hg, ?_⟩
  intro q hq
  exact ⟨dbarFirst_localDbarPrimitive hχ hχ hcχ hcχ hf hg q (hχone q.1 hq.1),
    dbarSecond_localDbarPrimitive hχ hχ hcχ hcχ hf hg hclosed q (hχone q.2 hq.2)⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
