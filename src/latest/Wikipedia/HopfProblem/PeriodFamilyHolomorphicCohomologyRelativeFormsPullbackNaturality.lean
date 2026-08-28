import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsPullbackOperators

/-!
# Independence from the ambient extension of the original upstairs function

Every ambient representative agreeing with the literal original upstairs
function on the original open base has the same full antiholomorphic
derivative there. Thus the computed formula is a statement about that
original function, not about a choice of extension outside its domain.
-/

noncomputable section

open TopologicalSpace Filter
open scoped Topology

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Pullback

open HolomorphicDolbeaultThree FourierParameter
open PeriodTorusLineBundleClassification

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- Agreement with the actual upstairs function gives agreement on a
genuine full neighborhood in the original covering model. -/
theorem originalFunction_eventuallyEq (f : SmoothFamily U (Fin 4))
    {F : Model → ℂ}
    (hF : ∀ (b : U) (z : ComplexPlane₂), F ((b : ℂ), z) = upstairs P f (b, z))
    (b : U) (z : ComplexPlane₂) :
    F =ᶠ[𝓝 ((b : ℂ), z)] familyPullback P f := by
  filter_upwards [(Smooth.baseProductDomain_isOpen U ComplexPlane₂).mem_nhds
    (show ((b : ℂ), z) ∈ Smooth.baseProductDomain U ComplexPlane₂ from b.property)] with q hq
  exact (hF ⟨q.1, hq⟩ q.2).trans
    (familyPullback_eq_upstairs P f ⟨q.1, hq⟩ q.2).symm

/-- The actual full differential is independent of the ambient extension. -/
theorem originalFunction_dbar_eq (f : SmoothFamily U (Fin 4))
    {F : Model → ℂ}
    (hF : ∀ (b : U) (z : ComplexPlane₂), F ((b : ℂ), z) = upstairs P f (b, z))
    (b : U) (z : ComplexPlane₂) :
    dbar F ((b : ℂ), z) = dbar (familyPullback P f) ((b : ℂ), z) :=
  dbar_congr (originalFunction_eventuallyEq P f hF b z)

/-- Any representative of the literal original upstairs function has
exactly the three genuine smooth-family operators as its frame coefficients. -/
theorem originalFunction_dbar_operators (f : SmoothFamily U (Fin 4))
    {F : Model → ℂ}
    (hF : ∀ (b : U) (z : ComplexPlane₂), F ((b : ℂ), z) = upstairs P f (b, z))
    (b : U) (z : ComplexPlane₂) :
    let t := torusQuotient ((P.periodEquiv b).symm z)
    dbar F ((b : ℂ), z) =
      RelativeOperators.d0 f (b, t) • baseCovector.val +
        RelativeOperators.d1 P f (b, t) • dbar (coordinate P 0) ((b : ℂ), z) +
        RelativeOperators.d2 P f (b, t) • dbar (coordinate P 1) ((b : ℂ), z) := by
  rw [originalFunction_dbar_eq P f hF b z]
  exact familyPullback_dbar_operators P f b z

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Pullback
