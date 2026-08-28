import Wikipedia.HopfProblem.DegreeCollapseRelativeIntegralCapCohomology
import Wikipedia.HopfProblem.DegreeCollapseIntegralTorsionCocycles

/-!
# Original relative integral cocycles from strict subspace vanishing

Factor through the actual relative-chain quotient, retaining the value
on every original ambient representative. Surjectivity of that quotient
checks the original cocycle equation and exact recovery under the original
absolute pullback. No relative class or comparison is supplied as an input.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralRelativeCocycleLift

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree
open NoExoticSixSphere.RelativeSingularHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (p : ℕ)

theorem quotientKernel_le_cochainKernel (c : SingularCohomologyCup.Cochain X p)
    (hc : c.comp (inducedChain (subtypeInclusion U) p) = 0) :
    LinearMap.ker (quotientMap U p) ≤ LinearMap.ker c := by
  intro x hx
  have hr : x ∈ LinearMap.range (inducedChain (subtypeInclusion U) p) := by
    rw [subtypeInclusion_chain_range]
    exact (quotientMap_eq_zero_iff U p x).mp hx
  obtain ⟨y, rfl⟩ := hr
  exact LinearMap.congr_fun hc y

def relativeCochain (c : SingularCohomologyCup.Cochain X p)
    (hc : c.comp (inducedChain (subtypeInclusion U) p) = 0) : RelativeIntegralCap.Cochain U p :=
  IntegralTorsionEvaluation.descendLinear (quotientMap U p) (quotientMap_surjective U p)
    c (quotientKernel_le_cochainKernel U p c hc)

theorem relativeCochain_quotientMap (c : SingularCohomologyCup.Cochain X p)
    (hc : c.comp (inducedChain (subtypeInclusion U) p) = 0) (b : Chains X p) :
    relativeCochain U p c hc (quotientMap U p b) = c b :=
  IntegralTorsionEvaluation.descendLinear_apply (quotientMap U p) (quotientMap_surjective U p)
    c (quotientKernel_le_cochainKernel U p c hc) b

theorem relativeCochain_toAbsolute (c : SingularCohomologyCup.Cochain X p)
    (hc : c.comp (inducedChain (subtypeInclusion U) p) = 0) :
    RelativeIntegralCap.toAbsolute U p (relativeCochain U p c hc) = c := by
  ext b
  exact relativeCochain_quotientMap U p c hc b

def relativeCocycle (c : Cocycle (singularCochainComplex X) p)
    (hc : c.val.comp (inducedChain (subtypeInclusion U) p) = 0) :
    RelativeIntegralCap.Cocycle U p :=
  mkCocycle (RelativeIntegralCap.cochainComplex U) p (relativeCochain U p c.val hc) (by
    ext b
    obtain ⟨a, rfl⟩ := quotientMap_surjective U (p + 1) b
    change relativeCochain U p c.val hc
      (((complex U).d (p + 1) p).hom (quotientMap U (p + 1) a)) = 0
    rw [boundary_quotientMap, relativeCochain_quotientMap]
    exact LinearMap.congr_fun (cocycle_condition (singularCochainComplex X) p c) a)

theorem relativeCocycle_quotientMap (c : Cocycle (singularCochainComplex X) p)
    (hc : c.val.comp (inducedChain (subtypeInclusion U) p) = 0) (b : Chains X p) :
    (relativeCocycle U p c hc).val (quotientMap U p b) = c.val b :=
  relativeCochain_quotientMap U p c.val hc b

theorem relativeCocycle_toAbsolute (c : Cocycle (singularCochainComplex X) p)
    (hc : c.val.comp (inducedChain (subtypeInclusion U) p) = 0) :
    mapCocycles (RelativeIntegralCap.toAbsoluteMap U) p (relativeCocycle U p c hc) = c := by
  apply Subtype.ext
  rw [mapCocycles_val]
  exact relativeCochain_toAbsolute U p c.val hc

theorem relativeClass_toAbsolute (c : Cocycle (singularCochainComplex X) p)
    (hc : c.val.comp (inducedChain (subtypeInclusion U) p) = 0) :
    (HomologicalComplex.homologyMap (RelativeIntegralCap.toAbsoluteMap U) p).hom
      (cocycleClass (RelativeIntegralCap.cochainComplex U) p (relativeCocycle U p c hc)) =
    cocycleClass (singularCochainComplex X) p c := by
  rw [homologyMap_cocycleClass, relativeCocycle_toAbsolute]

end Wikipedia.HopfProblem.DegreeCollapse.IntegralRelativeCocycleLift
