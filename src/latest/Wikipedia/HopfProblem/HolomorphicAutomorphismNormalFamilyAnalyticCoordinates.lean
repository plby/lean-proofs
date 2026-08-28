import Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamilyAnalyticOpen
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalyticCoordinates

/-!
# Analytic regularity on the native threefold model

The original model `ℂ × ComplexPlane₂` is continuously complex-linearly
equivalent to the three product coordinates.  Transport through this actual
equivalence preserves the original norm, topology, and differentiability
notions.  The scalar result also gives `C^ω` regularity of native-model-valued
maps, coordinate by coordinate.
-/

noncomputable section

open Set
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily.AnalyticThreefold

/-- The native base and two fibre coordinates, with their original norms. -/
def nativeProductEquiv : (ℂ × ComplexPlane₂) ≃L[ℂ] ℂ × (ℂ × ℂ) :=
  (ContinuousLinearEquiv.refl ℂ ℂ).prodCongr
    PeriodTorusLineBundleClassificationPolydiscAnalytic.complexPairEquiv

@[simp] theorem nativeProductEquiv_apply (z : ℂ × ComplexPlane₂) :
    nativeProductEquiv z = (z.1, z.2 0, z.2 1) := rfl

@[simp] theorem nativeProductEquiv_symm_apply (z : ℂ × (ℂ × ℂ)) :
    nativeProductEquiv.symm z = (z.1, ![z.2.1, z.2.2]) := rfl

/-- Transfer scalar analyticity from the three product coordinates. -/
theorem analyticOnNhd_nativeScalar_of_product
    {f : (ℂ × ComplexPlane₂) → ℂ} {s : Set (ℂ × ComplexPlane₂)}
    (hf : AnalyticOnNhd ℂ (f ∘ nativeProductEquiv.symm)
      (nativeProductEquiv.symm ⁻¹' s)) : AnalyticOnNhd ℂ f s := by
  intro z hz
  have hmem : nativeProductEquiv z ∈ nativeProductEquiv.symm ⁻¹' s := by
    simpa only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hz
  have ha := (hf (nativeProductEquiv z) hmem).comp
    (nativeProductEquiv.toContinuousLinearMap.analyticAt z)
  have heq : (f ∘ nativeProductEquiv.symm) ∘ nativeProductEquiv = f := by
    funext w
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rwa [heq] at ha

/-- Complex differentiability gives actual joint analyticity of scalar maps
on open subsets of the original threefold model. -/
theorem analyticOnNhd_nativeScalar_of_differentiableOn
    {f : (ℂ × ComplexPlane₂) → ℂ} {s : Set (ℂ × ComplexPlane₂)}
    (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) : AnalyticOnNhd ℂ f s := by
  apply analyticOnNhd_nativeScalar_of_product
  apply analyticOnNhd_product_of_differentiableOn
    (hs.preimage nativeProductEquiv.symm.continuous)
  exact hf.comp nativeProductEquiv.symm.differentiable.differentiableOn (fun _ h => h)

theorem analyticOnNhd_nativeScalar_iff_differentiableOn
    {f : (ℂ × ComplexPlane₂) → ℂ} {s : Set (ℂ × ComplexPlane₂)} (hs : IsOpen s) :
    AnalyticOnNhd ℂ f s ↔ DifferentiableOn ℂ f s :=
  ⟨AnalyticOnNhd.differentiableOn, analyticOnNhd_nativeScalar_of_differentiableOn hs⟩

/-- The scalar upgrade uses the actual analytic regularity index `ω`. -/
theorem contDiffOn_nativeScalar_of_differentiableOn
    {f : (ℂ × ComplexPlane₂) → ℂ} {s : Set (ℂ × ComplexPlane₂)}
    (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) : ContDiffOn ℂ ω f s :=
  (analyticOnNhd_nativeScalar_of_differentiableOn hs hf).contDiffOn_of_completeSpace

theorem contDiff_nativeScalar_of_differentiable
    {f : (ℂ × ComplexPlane₂) → ℂ} (hf : Differentiable ℂ f) : ContDiff ℂ ω f :=
  (analyticOnNhd_nativeScalar_of_differentiableOn isOpen_univ hf.differentiableOn).contDiff

/-- The native-model-valued upgrade is obtained from the actual base coordinate
and the two actual fibre coordinates.  No coordinate regularity is assumed. -/
theorem contDiffOn_nativeModel_of_differentiableOn
    {f : (ℂ × ComplexPlane₂) → (ℂ × ComplexPlane₂)} {s : Set (ℂ × ComplexPlane₂)}
    (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) : ContDiffOn ℂ ω f s := by
  have h₁ : ContDiffOn ℂ ω (fun z => (f z).1) s :=
    contDiffOn_nativeScalar_of_differentiableOn hs hf.fst
  have h₂ : ContDiffOn ℂ ω (fun z => (f z).2) s := by
    apply contDiffOn_pi.2
    intro i
    exact contDiffOn_nativeScalar_of_differentiableOn hs (differentiableOn_pi.1 hf.snd i)
  exact h₁.prodMk h₂

theorem contDiff_nativeModel_of_differentiable
    {f : (ℂ × ComplexPlane₂) → (ℂ × ComplexPlane₂)}
    (hf : Differentiable ℂ f) : ContDiff ℂ ω f :=
  contDiffOn_univ.mp
    (contDiffOn_nativeModel_of_differentiableOn isOpen_univ hf.differentiableOn)

end Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily.AnalyticThreefold
