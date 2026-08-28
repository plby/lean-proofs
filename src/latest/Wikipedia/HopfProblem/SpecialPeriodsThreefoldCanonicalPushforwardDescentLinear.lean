import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardDescent
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardGenericLinear
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsSheafNative

/-!
# Linearity and restriction of genuine canonical descent

The holomorphic extension of the actual generic coefficient preserves
addition and the actual holomorphic base-function action. Uniqueness on
the dense generic open also proves compatibility with every literal
restriction. Thus descent takes values in the true ideal sheaf as an
O-linear map on each original base open.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Descent

open HolomorphicFunctionSheaf.SphereH1

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

theorem coefficient_add (U : Opens RiemannSphere) (s t : PreimageSection U) :
    coefficient U (s + t) = coefficient U s + coefficient U t := by
  symm
  apply coefficient_unique
  intro p hp
  change coefficient U s p + coefficient U t p = _
  rw [coefficient_eq_generic U s p hp, coefficient_eq_generic U t p hp,
    Generic.baseCoefficient_add]
  rfl

theorem coefficient_complex_smul (U : Opens RiemannSphere) (c : ℂ)
    (s : PreimageSection U) : coefficient U (c • s) = c • coefficient U s := by
  symm
  apply coefficient_unique
  intro p hp
  change c * coefficient U s p = _
  rw [coefficient_eq_generic U s p hp, Generic.baseCoefficient_complex_smul]
  rfl

/-- The action on the original canonical section is actual pullback
of the original holomorphic base function. -/
theorem coefficient_base_smul (U : Opens RiemannSphere)
    (f : Threefold.BaseSection U) (s : PreimageSection U) :
    coefficient U (f • s) = f * coefficient U s := by
  symm
  apply coefficient_unique
  intro p hp
  change f p * coefficient U s p = _
  rw [coefficient_eq_generic U s p hp, base_smul_eq_pullback,
    Generic.baseCoefficient_base_smul]
  rfl

theorem idealSection_add (U : Opens RiemannSphere) (s t : PreimageSection U) :
    idealSection U (s + t) = idealSection U s + idealSection U t :=
  Subtype.ext (coefficient_add U s t)

theorem idealSection_complex_smul (U : Opens RiemannSphere) (c : ℂ)
    (s : PreimageSection U) : idealSection U (c • s) = c • idealSection U s :=
  Subtype.ext (coefficient_complex_smul U c s)

theorem idealSection_base_smul (U : Opens RiemannSphere)
    (f : Threefold.BaseSection U) (s : PreimageSection U) :
    idealSection U (f • s) = f • idealSection U s :=
  Subtype.ext (coefficient_base_smul U f s)

/-- The actual O(U)-linear native canonical descent into the actual ideal. -/
def idealLinearMap (U : Opens RiemannSphere) :
    PreimageSection U →ₗ[Threefold.BaseSection U] NegativeOneSection U where
  toFun := idealSection U
  map_add' := idealSection_add U
  map_smul' := idealSection_base_smul U

@[simp] theorem idealLinearMap_apply (U : Opens RiemannSphere) (s : PreimageSection U) :
    idealLinearMap U s = idealSection U s := rfl

/-- The same map is complex-linear for the original constant scalar actions. -/
def idealComplexLinearMap (U : Opens RiemannSphere) :
    PreimageSection U →ₗ[ℂ] NegativeOneSection U where
  toFun := idealSection U
  map_add' := idealSection_add U
  map_smul' := idealSection_complex_smul U

/-- Holomorphic extension commutes with every literal restriction. -/
theorem coefficient_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : PreimageSection V) :
    coefficient U (restrictPreimageSection h s) =
      HolomorphicFunctionSheaf.restrictionAlgHom 𝓘(ℂ) RiemannSphere h (coefficient V s) := by
  apply CanonicalPushforwardExtension.section_eq_of_dense 𝓘(ℂ) RiemannSphere
    Generic.genericBase_dense U
  intro p hp
  change coefficient U (restrictPreimageSection h s) p =
    coefficient V s ⟨p.val, h p.property⟩
  rw [coefficient_eq_generic U (restrictPreimageSection h s) p hp,
    coefficient_eq_generic V s ⟨p.val, h p.property⟩ hp, Generic.baseCoefficient_restrict]
  rfl

/-- Naturality in the true ideal sheaf, not only in scalar coefficients. -/
theorem idealSection_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : PreimageSection V) :
    idealSection U (restrictPreimageSection h s) = negativeOneRestriction h (idealSection V s) :=
  Subtype.ext (coefficient_restrict h s)

theorem idealLinearMap_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : PreimageSection V) :
    idealLinearMap U (restrictPreimageSection h s) =
      negativeOneRestriction h (idealLinearMap V s) := idealSection_restrict h s

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Descent
