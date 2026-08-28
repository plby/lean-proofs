import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalyticOpen
import Wikipedia.HopfProblem.PeriodTori

/-!
# Analyticity on the actual covering vector space

The product-coordinate theorem is transported by the canonical complex
continuous linear equivalence to `ComplexPlane₂ = Fin 2 → ℂ`.  In
particular, differentiability on an open subset implies actual `C^ω`
regularity there, as needed for native holomorphic bundle constructions.
-/

noncomputable section

open Set
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalytic

/-- The canonical complex coordinate equivalence, with the original norms. -/
def complexPairEquiv : ComplexPlane₂ ≃L[ℂ] ℂ × ℂ :=
  ContinuousLinearEquiv.finTwoArrow ℂ ℂ

@[simp] theorem complexPairEquiv_apply (z : ComplexPlane₂) :
    complexPairEquiv z = (z 0, z 1) := rfl

@[simp] theorem complexPairEquiv_symm_apply (z : ℂ × ℂ) :
    complexPairEquiv.symm z = ![z.1, z.2] := rfl

/-- Transfer genuine analyticity from the product coordinates. -/
theorem analyticOnNhd_complexPlane₂_of_pair {f : ComplexPlane₂ → ℂ}
    {s : Set ComplexPlane₂}
    (hf : AnalyticOnNhd ℂ (f ∘ complexPairEquiv.symm) (complexPairEquiv.symm ⁻¹' s)) :
    AnalyticOnNhd ℂ f s := by
  intro z hz
  have hmem : complexPairEquiv z ∈ complexPairEquiv.symm ⁻¹' s := by
    simpa only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hz
  have ha := (hf (complexPairEquiv z) hmem).comp
    (complexPairEquiv.toContinuousLinearMap.analyticAt z)
  have heq : (f ∘ complexPairEquiv.symm) ∘ complexPairEquiv = f := by
    funext w
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rwa [heq] at ha

/-- Continuous coordinatewise holomorphic functions are jointly analytic
on an actual open subset of the covering space. -/
theorem analyticOnNhd_complexPlane₂_of_continuousOn_of_slices
    {f : ComplexPlane₂ → ℂ} {s : Set ComplexPlane₂}
    (hs : IsOpen s) (hf : ContinuousOn f s)
    (h₁ : ∀ w : ℂ, DifferentiableOn ℂ (fun v => f ![v, w]) ((fun v => ![v, w]) ⁻¹' s))
    (h₂ : ∀ v : ℂ, DifferentiableOn ℂ (fun w => f ![v, w]) ((fun w => ![v, w]) ⁻¹' s)) :
    AnalyticOnNhd ℂ f s := by
  apply analyticOnNhd_complexPlane₂_of_pair
  apply analyticOnNhd_of_continuousOn_of_slices (hs.preimage complexPairEquiv.symm.continuous)
    (hf.comp complexPairEquiv.symm.continuous.continuousOn (fun _ h => h))
  · intro w
    simpa only [Function.comp_apply, complexPairEquiv_symm_apply, Set.preimage_preimage]
      using h₁ w
  · intro v
    simpa only [Function.comp_apply, complexPairEquiv_symm_apply, Set.preimage_preimage]
      using h₂ v

/-- Complex differentiability implies analyticity on actual open subsets
of `ComplexPlane₂`, not merely on one-dimensional slices. -/
theorem analyticOnNhd_complexPlane₂_of_differentiableOn
    {f : ComplexPlane₂ → ℂ} {s : Set ComplexPlane₂}
    (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) : AnalyticOnNhd ℂ f s := by
  apply analyticOnNhd_complexPlane₂_of_pair
  apply analyticOnNhd_of_differentiableOn (hs.preimage complexPairEquiv.symm.continuous)
  exact hf.comp complexPairEquiv.symm.differentiable.differentiableOn (fun _ h => h)

theorem analyticOnNhd_complexPlane₂_iff_differentiableOn
    {f : ComplexPlane₂ → ℂ} {s : Set ComplexPlane₂} (hs : IsOpen s) :
    AnalyticOnNhd ℂ f s ↔ DifferentiableOn ℂ f s :=
  ⟨AnalyticOnNhd.differentiableOn, analyticOnNhd_complexPlane₂_of_differentiableOn hs⟩

theorem contDiffOn_prod_of_differentiableOn {f : ℂ × ℂ → ℂ} {s : Set (ℂ × ℂ)}
    (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) : ContDiffOn ℂ ω f s :=
  (analyticOnNhd_of_differentiableOn hs hf).contDiffOn_of_completeSpace

theorem contDiff_prod_of_differentiable {f : ℂ × ℂ → ℂ}
    (hf : Differentiable ℂ f) : ContDiff ℂ ω f :=
  (analyticOnNhd_of_differentiableOn isOpen_univ hf.differentiableOn).contDiff

theorem contDiffOn_complexPlane₂_of_differentiableOn
    {f : ComplexPlane₂ → ℂ} {s : Set ComplexPlane₂}
    (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) : ContDiffOn ℂ ω f s :=
  (analyticOnNhd_complexPlane₂_of_differentiableOn hs hf).contDiffOn_of_completeSpace

theorem contDiff_complexPlane₂_of_differentiable {f : ComplexPlane₂ → ℂ}
    (hf : Differentiable ℂ f) : ContDiff ℂ ω f :=
  (analyticOnNhd_complexPlane₂_of_differentiableOn isOpen_univ hf.differentiableOn).contDiff

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalytic
