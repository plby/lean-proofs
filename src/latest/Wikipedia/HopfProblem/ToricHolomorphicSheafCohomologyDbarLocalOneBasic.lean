import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLocalDbar

/-!
# Cauchy–Green correction under a local closedness equation

The residual identity uses the closedness equation only at the point at
which it is differentiated. After multiplication by the first-coordinate
cutoff, closedness is needed only where that cutoff is nonzero. This is
the local version required for actual smooth germs.
-/

noncomputable section

open Complex Set Metric
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DbarLocalOne

open PeriodTorusLineBundleClassification

theorem dbarSecond_firstResidual_eq_zero_of_closedAt
    {χ : ℂ → ℂ} {f g : ℂ × ℂ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (q : ℂ × ℂ) (hclosed : dbarFirst g q = dbarSecond f q)
    (hq : χ q.2 = 1) :
    dbarSecond (firstResidual χ f g) q = 0 := by
  have hu := contDiff_firstCorrection hχ hcχ hg
  have he : dbarSecond (firstCorrection χ g) = secondLocalizedData χ g :=
    funext (dbarSecond_firstCorrection hχ hcχ hg)
  change dbarSecond (fun x => f x - dbarFirst (firstCorrection χ g) x) q = 0
  rw [dbarSecond_sub ((hf.differentiable (by simp)) q)
      (((contDiff_dbarFirst hu).differentiable (by simp)) q),
    ← dbarFirst_dbarSecond hu q, he]
  change dbarSecond f q - dbarFirst (fun x => χ x.2 * g x) q = 0
  rw [dbarFirst_mul (f := fun x => χ x.2)
      (((hχ.comp contDiff_snd).differentiable (by simp)) q)
      ((hg.differentiable (by simp)) q), dbarFirst_snd, hq,
    one_mul, mul_zero, add_zero, hclosed, sub_self]

theorem dbarSecond_localizedResidual_eq_zero_of_closedAt
    {χ₁ χ₂ : ℂ → ℂ} {f g : ℂ × ℂ → ℂ}
    (hχ₁ : ContDiff ℝ ∞ χ₁) (hχ₂ : ContDiff ℝ ∞ χ₂)
    (hcχ₂ : HasCompactSupport χ₂) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (q : ℂ × ℂ) (hclosed : χ₁ q.1 ≠ 0 → dbarFirst g q = dbarSecond f q)
    (hq : χ₂ q.2 = 1) :
    dbarSecond (localizedResidual χ₁ χ₂ f g) q = 0 := by
  change dbarSecond (fun x => χ₁ x.1 * firstResidual χ₂ f g x) q = 0
  rw [dbarSecond_mul (f := fun x => χ₁ x.1)
      (((hχ₁.comp contDiff_fst).differentiable (by simp)) q)
      (((contDiff_firstResidual hχ₂ hcχ₂ hf hg).differentiable (by simp)) q),
    dbarSecond_fst, mul_zero, add_zero]
  by_cases hzero : χ₁ q.1 = 0
  · rw [hzero, zero_mul]
  · rw [dbarSecond_firstResidual_eq_zero_of_closedAt hχ₂ hcχ₂ hf hg q
      (hclosed hzero) hq, mul_zero]

/-- The second equation is solved on a strip when the original closedness
equation holds there at every point where the first cutoff is nonzero. -/
theorem dbarSecond_localDbarPrimitive_of_closedOn
    {χ₁ χ₂ : ℂ → ℂ} {f g : ℂ × ℂ → ℂ} {V : Set ℂ}
    (hχ₁ : ContDiff ℝ ∞ χ₁) (hχ₂ : ContDiff ℝ ∞ χ₂)
    (hcχ₁ : HasCompactSupport χ₁) (hcχ₂ : HasCompactSupport χ₂)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hclosed : ∀ z w, χ₁ z ≠ 0 → w ∈ V →
      dbarFirst g (z, w) = dbarSecond f (z, w))
    (hχ₂one : ∀ w ∈ V, χ₂ w = 1) (q : ℂ × ℂ) (hq : q.2 ∈ V) :
    dbarSecond (localDbarPrimitive χ₁ χ₂ f g) q = g q := by
  have hv := contDiff_localizedResidual hχ₁ hχ₂ hcχ₂ hf hg
  have hvk := fun z w hz =>
    localizedResidual_eq_zero (χ₁ := χ₁) (χ₂ := χ₂) (f := f) (g := g) z w hz
  have he : dbarSecond (cauchyFirst (localizedResidual χ₁ χ₂ f g)) q = 0 := by
    apply dbarSecond_cauchyFirst_eq_zero (U := V) (hv.of_le (by simp)) hcχ₁ hvk
    · intro z w hw
      exact dbarSecond_localizedResidual_eq_zero_of_closedAt hχ₁ hχ₂ hcχ₂ hf hg
        (z, w) (fun hz => hclosed z w hz hw) (hχ₂one w hw)
    · exact hq
  change dbarSecond (fun x => firstCorrection χ₂ g x +
    cauchyFirst (localizedResidual χ₁ χ₂ f g) x) q = g q
  rw [dbarSecond_add (((contDiff_firstCorrection hχ₂ hcχ₂ hg).differentiable (by simp)) q)
      (((contDiff_cauchyFirst hv hcχ₁ hvk).differentiable (by simp)) q),
    he, add_zero, dbarSecond_firstCorrection hχ₂ hcχ₂ hg,
    secondLocalizedData, hχ₂one q.2 hq, one_mul]

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DbarLocalOne
