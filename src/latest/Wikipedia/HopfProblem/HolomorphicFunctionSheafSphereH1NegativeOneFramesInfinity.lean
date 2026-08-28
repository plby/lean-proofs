import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneFramesCoordinates
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneFramesAnalytic
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneSheafBasic
import Mathlib.LinearAlgebra.Span.Basic

/-!
# The actual ideal-sheaf frame on every reciprocal-chart subopen set

The frame is the reciprocal coordinate itself.  Multiplication by this
actual holomorphic section identifies the function ring on every subopen
set with the actual ideal of sections vanishing at infinity.  Surjectivity
uses analytic divided differences on the original coordinate domain;
injectivity uses local holomorphic cancellation, including at infinity.
The identifications commute with literal restriction maps.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

open RiemannSphere

/-- The actual reciprocal coordinate is an ideal section on every
subopen set of its chart. -/
def infinityFrame (U : Opens RiemannSphere) (hU : U ≤ infinityChart) :
    NegativeOneSection U :=
  ⟨ofInfinityCoefficient U hU id (fun _ _ => analyticAt_id), fun _ => rfl⟩

@[simp] theorem infinityFrame_coe (U : Opens RiemannSphere) (hU : U ≤ infinityChart)
    (z : ℂ) (hz : (z : RiemannSphere) ∈ U) :
    (infinityFrame U hU).val ⟨(z : RiemannSphere), hz⟩ = z⁻¹ := rfl

@[simp] theorem infinityFrame_infty (U : Opens RiemannSphere) (hU : U ≤ infinityChart)
    (hInf : (∞ : RiemannSphere) ∈ U) :
    (infinityFrame U hU).val ⟨(∞ : RiemannSphere), hInf⟩ = 0 := rfl

@[simp] theorem infinityFrame_parametrization (U : Opens RiemannSphere)
    (hU : U ≤ infinityChart) (u : ℂ) (hu : infinityParametrization u ∈ U) :
    (infinityFrame U hU).val ⟨infinityParametrization u, hu⟩ = u :=
  ofInfinityCoefficient_parametrization U hU id (fun _ _ => analyticAt_id) u hu

/-- Multiplication by the actual frame, linear over the actual section ring. -/
def infinityFrameMap (U : Opens RiemannSphere) (hU : U ≤ infinityChart) :
    HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U →ₗ[
      HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U] NegativeOneSection U :=
  LinearMap.toSpanSingleton _ _ (infinityFrame U hU)

@[simp] theorem infinityFrameMap_apply (U : Opens RiemannSphere) (hU : U ≤ infinityChart)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) (p : U) :
    (infinityFrameMap U hU f).val p = f p * (infinityFrame U hU).val p := rfl

/-- The coefficient of an actual ideal section vanishes at zero, even
when infinity is outside its domain, where the chosen extension is zero. -/
theorem ideal_infinityCoefficient_zero (U : Opens RiemannSphere) (f : NegativeOneSection U) :
    infinityCoefficient U f.val 0 = 0 := by
  classical
  by_cases hInf : (∞ : RiemannSphere) ∈ U
  · exact (infinityCoefficient_zero U f.val hInf).trans (f.property hInf)
  · change sectionExtend U f.val (infinityParametrization 0) = 0
    rw [infinityParametrization_zero]
    simp only [sectionExtend, dif_neg hInf]

/-- Actual division by the frame on the original subopen set. -/
def infinityDivide (U : Opens RiemannSphere) (hU : U ≤ infinityChart)
    (f : NegativeOneSection U) : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U :=
  ofInfinityCoefficient U hU (dslope (infinityCoefficient U f.val) 0)
    (analyticOnNhd_dslope_open (infinityOpen U).isOpen (infinityCoefficient_analytic U f.val))

@[simp] theorem infinityDivide_parametrization (U : Opens RiemannSphere)
    (hU : U ≤ infinityChart) (f : NegativeOneSection U)
    (u : ℂ) (hu : infinityParametrization u ∈ U) :
    infinityDivide U hU f ⟨infinityParametrization u, hu⟩ =
      dslope (infinityCoefficient U f.val) 0 u :=
  ofInfinityCoefficient_parametrization U hU _ _ u hu

/-- Coordinate coefficients detect equality of actual sections on every
subopen set of the reciprocal chart. -/
theorem section_eq_of_infinityCoefficient_eq (U : Opens RiemannSphere)
    (hU : U ≤ infinityChart)
    (f g : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U)
    (he : ∀ u ∈ infinityOpen U, infinityCoefficient U f u = infinityCoefficient U g u) :
    f = g := by
  apply ContMDiffMap.ext
  intro p
  obtain ⟨u, hu⟩ := exists_infinityCoordinate p (hU p.property)
  have huU : infinityParametrization u ∈ U := hu.symm ▸ p.property
  have hp : (⟨infinityParametrization u, huU⟩ : U) = p := Subtype.ext hu
  have h := (infinityCoefficient_apply U f u huU).symm.trans
    ((he u huU).trans (infinityCoefficient_apply U g u huU))
  simpa only [hp] using h

/-- Analytic divided difference is an actual inverse to multiplication
by the frame, at all points including infinity. -/
theorem infinityFrameMap_divide (U : Opens RiemannSphere) (hU : U ≤ infinityChart)
    (f : NegativeOneSection U) : infinityFrameMap U hU (infinityDivide U hU f) = f := by
  apply Subtype.ext
  apply ContMDiffMap.ext
  intro p
  obtain ⟨u, hu⟩ := exists_infinityCoordinate p (hU p.property)
  have huU : infinityParametrization u ∈ U := hu.symm ▸ p.property
  have hp : (⟨infinityParametrization u, huU⟩ : U) = p := Subtype.ext hu
  rw [← hp, infinityFrameMap_apply, infinityDivide_parametrization,
    infinityFrame_parametrization]
  calc
    dslope (infinityCoefficient U f.val) 0 u * u =
        u * dslope (infinityCoefficient U f.val) 0 u := mul_comm _ _
    _ = infinityCoefficient U f.val u :=
      HolomorphicCousin.zero_mul_dslope (ideal_infinityCoefficient_zero U f) u
    _ = f.val ⟨infinityParametrization u, huU⟩ := infinityCoefficient_apply U f.val u huU

theorem infinityFrameMap_injective (U : Opens RiemannSphere) (hU : U ≤ infinityChart) :
    Function.Injective (infinityFrameMap U hU) := by
  intro f g he
  have hm : ∀ u ∈ infinityOpen U,
      u * infinityCoefficient U f u = u * infinityCoefficient U g u := by
    intro u hu
    have h := congrArg (fun s : NegativeOneSection U =>
      s.val ⟨infinityParametrization u, hu⟩) he
    change f ⟨infinityParametrization u, hu⟩ *
        (infinityFrame U hU).val ⟨infinityParametrization u, hu⟩ =
      g ⟨infinityParametrization u, hu⟩ *
        (infinityFrame U hU).val ⟨infinityParametrization u, hu⟩ at h
    have hframe := infinityFrame_parametrization U hU u hu
    rw [hframe] at h
    rw [infinityCoefficient_apply U f u hu, infinityCoefficient_apply U g u hu]
    simpa only [mul_comm] using h
  exact section_eq_of_infinityCoefficient_eq U hU f g
    (coordinate_mul_injective_on (infinityOpen U).isOpen
      (infinityCoefficient_analytic U f) (infinityCoefficient_analytic U g) hm)

theorem infinityFrameMap_surjective (U : Opens RiemannSphere) (hU : U ≤ infinityChart) :
    Function.Surjective (infinityFrameMap U hU) :=
  fun f => ⟨infinityDivide U hU f, infinityFrameMap_divide U hU f⟩

/-- On every subopen set, the actual ideal sheaf is free of rank one
over its actual ring of holomorphic functions, with reciprocal-coordinate frame. -/
def infinityTrivialization (U : Opens RiemannSphere) (hU : U ≤ infinityChart) :
    HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U ≃ₗ[
      HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U] NegativeOneSection U :=
  LinearEquiv.ofBijective (infinityFrameMap U hU)
    ⟨infinityFrameMap_injective U hU, infinityFrameMap_surjective U hU⟩

@[simp] theorem infinityTrivialization_apply (U : Opens RiemannSphere)
    (hU : U ≤ infinityChart) (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U)
    (p : U) :
    (infinityTrivialization U hU f).val p = f p * (infinityFrame U hU).val p := rfl

theorem infinityTrivialization_symm_eq_divide (U : Opens RiemannSphere)
    (hU : U ≤ infinityChart) (f : NegativeOneSection U) :
    (infinityTrivialization U hU).symm f = infinityDivide U hU f := by
  apply (infinityTrivialization U hU).injective
  exact ((infinityTrivialization U hU).apply_symm_apply f).trans
    (infinityFrameMap_divide U hU f).symm

@[simp] theorem infinityTrivialization_symm_parametrization (U : Opens RiemannSphere)
    (hU : U ≤ infinityChart) (f : NegativeOneSection U)
    (u : ℂ) (hu : infinityParametrization u ∈ U) :
    (infinityTrivialization U hU).symm f ⟨infinityParametrization u, hu⟩ =
      dslope (infinityCoefficient U f.val) 0 u := by
  rw [infinityTrivialization_symm_eq_divide, infinityDivide_parametrization]

/-- The frames themselves are compatible with literal restriction. -/
theorem infinityFrame_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (hV : V ≤ infinityChart) :
    negativeOneRestriction h (infinityFrame V hV) = infinityFrame U (h.trans hV) := by
  apply Subtype.ext
  apply ContMDiffMap.ext
  intro p
  rfl

/-- Naturality on all subopens: the actual module identifications
commute with the ideal sheaf's literal restriction maps. -/
theorem infinityTrivialization_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (hV : V ≤ infinityChart) (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere V) :
    negativeOneRestriction h (infinityTrivialization V hV f) =
      infinityTrivialization U (h.trans hV) (ContMDiffMap.restrictRingHom 𝓘(ℂ) 𝓘(ℂ) ℂ h f) := by
  apply Subtype.ext
  apply ContMDiffMap.ext
  intro p
  rfl

/-- The inverse coefficient maps are natural as well, by the proved
pointwise inverse to frame multiplication. -/
theorem infinityTrivialization_symm_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (hV : V ≤ infinityChart) (f : NegativeOneSection V) :
    ContMDiffMap.restrictRingHom 𝓘(ℂ) 𝓘(ℂ) ℂ h ((infinityTrivialization V hV).symm f) =
      (infinityTrivialization U (h.trans hV)).symm (negativeOneRestriction h f) := by
  apply (infinityTrivialization U (h.trans hV)).injective
  calc
    infinityTrivialization U (h.trans hV)
        (ContMDiffMap.restrictRingHom 𝓘(ℂ) 𝓘(ℂ) ℂ h
          ((infinityTrivialization V hV).symm f)) =
      negativeOneRestriction h
        (infinityTrivialization V hV ((infinityTrivialization V hV).symm f)) :=
          (infinityTrivialization_restrict h hV _).symm
    _ = negativeOneRestriction h f :=
      congrArg (negativeOneRestriction h) ((infinityTrivialization V hV).apply_symm_apply f)
    _ = infinityTrivialization U (h.trans hV)
        ((infinityTrivialization U (h.trans hV)).symm (negativeOneRestriction h f)) :=
      ((infinityTrivialization U (h.trans hV)).apply_symm_apply _).symm

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames
