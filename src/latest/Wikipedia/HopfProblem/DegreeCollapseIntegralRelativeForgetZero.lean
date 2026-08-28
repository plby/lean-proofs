import Wikipedia.HopfProblem.DegreeCollapseIntegralRelativeForgetNaturality

/-!
# The original forgotten relative class vanishes on the original subspace

The original subspace inclusion followed by the quotient projection is
zero on chains. Its original dual square gives zero cohomology pullback.
Every continuous map whose image lies in that subspace factors through
the actual subtype inclusion, so the same vanishing holds for that map.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCap

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree NoExoticSixSphere

variable {X : Type} [TopologicalSpace X] (U : Set X)

theorem toAbsoluteMap_subtype_zero :
    toAbsoluteMap U ≫ singularPullback (subtypeInclusion U) = 0 := by
  rw [toAbsoluteMap, singularPullback, ← dualMap_comp]
  change dualMap (RelativeSingularHomology.inclusion U ≫
    RelativeSingularHomology.projection U) = 0
  rw [RelativeSingularHomology.inclusion_projection, dualMap_zero]

theorem cohomologyForget_subtype_zero (p : ℕ) (a : Cohomology U p) :
    singularCohomologyPullback (subtypeInclusion U) p
      ((HomologicalComplex.homologyMap (toAbsoluteMap U) p).hom a) = 0 := by
  have he := congrArg (fun g : cochainComplex U ⟶ singularCochainComplex U ↦
    (HomologicalComplex.homologyMap g p).hom a) (toAbsoluteMap_subtype_zero U)
  simpa only [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_zero,
    ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply, LinearMap.zero_apply,
    singularCohomologyPullback] using he

theorem cohomologyForget_pullback_zero {Y : Type} [TopologicalSpace Y]
    (f : C(Y, X)) (hf : ∀ y, f y ∈ U) (p : ℕ) (a : Cohomology U p) :
    singularCohomologyPullback f p
      ((HomologicalComplex.homologyMap (toAbsoluteMap U) p).hom a) = 0 := by
  let g : C(Y, U) := ⟨fun y ↦ ⟨f y, hf y⟩, f.continuous.subtype_mk _⟩
  have hg : (subtypeInclusion U).comp g = f := rfl
  rw [← hg, singularCohomologyPullback_comp]
  change singularCohomologyPullback g p
    (singularCohomologyPullback (subtypeInclusion U) p
      ((HomologicalComplex.homologyMap (toAbsoluteMap U) p).hom a)) = 0
  rw [cohomologyForget_subtype_zero, map_zero]

end Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCap
