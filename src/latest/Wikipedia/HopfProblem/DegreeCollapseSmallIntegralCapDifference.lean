import Wikipedia.HopfProblem.DegreeCollapseSmallIntegralCapBoundary

/-!
# Actual two-piece integral cap representatives

A cochain difference on a common ambient chain is the difference of
the two genuine localized caps. If its boundary lies in the annihilated
piece, the original localized cap boundary is -(-1)^p times cap with
the original coboundary. This is the sign needed by the connecting lift.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.SmallIntegralCap

open FirstHurewicz SingularMayerVietoris SingularCohomologyCup NoExoticSixSphere
open IntegralCap (Coefficient)
open SingularSubcomplex (SmallChains smallInclusionMap)

variable {X : Type} [TopologicalSpace X]

theorem capInDegree_difference (U V A B : Set X) {p q n : ℕ} (h : p + q = n)
    (α : Cochain X p) (β : RelativeIntegralCap.Cochain A p)
    (γ : RelativeIntegralCap.Cochain B p)
    (hα : α = RelativeIntegralCap.toAbsolute A p β - RelativeIntegralCap.toAbsolute B p γ)
    (c : Chains X n) (cU : SmallChains Coefficient U A n)
    (hcU : smallInclusionMap Coefficient U A n cU = c) (cV : SmallChains Coefficient V B n)
    (hcV : smallInclusionMap Coefficient V B n cV = c) :
    IntegralCap.capInDegree h α c =
      inducedChain (subtypeInclusion U) q (capInDegree U A h β cU) -
        inducedChain (subtypeInclusion V) q (capInDegree V B h γ cV) := by
  rw [hα, IntegralCap.capInDegree_sub, LinearMap.sub_apply]
  exact congrArg₂ (fun x y => x - y)
    ((inclusion_capInDegree U A h β cU).trans
      (congrArg (IntegralCap.capInDegree h (RelativeIntegralCap.toAbsolute A p β)) hcU)).symm
    ((inclusion_capInDegree V B h γ cV).trans
      (congrArg (IntegralCap.capInDegree h (RelativeIntegralCap.toAbsolute B p γ)) hcV)).symm

/-- The actual relative-cycle hypothesis gives precisely the signed localized coboundary cap. -/
theorem boundary_capInDegree_of_relative_cycle (U V : Set X) {p q n : ℕ}
    (h : p + q + 1 = n) (α : RelativeIntegralCap.Cochain V p)
    (c : SmallChains Coefficient U V n)
    (hc : smallInclusionMap Coefficient U V (p + q) (((complex U V).d n (p + q)).hom c) ∈
      LinearMap.range (inducedChain (subtypeInclusion V) (p + q))) :
    ((singularComplex U).d (q + 1) q).hom
        (capInDegree U V (p := p) (q := q + 1) (n := n) (by omega) α c) =
      -((-1 : ℤ) ^ p) • capInDegree U V (p := p + 1) (q := q) (n := n) (by omega)
        (RelativeIntegralCap.coboundary V α) c := by
  apply boundary_capInDegree_of_boundary_killed U V h α c
  apply inclusion_injective U q
  exact (inclusion_capInDegree U V rfl α (((complex U V).d n (p + q)).hom c)).trans
    ((IntegralCap.capInDegree_eq_zero_of_pullback_zero V rfl
      (RelativeIntegralCap.toAbsolute V p α) (RelativeIntegralCap.pullback_toAbsolute V p α)
      _ hc).trans (inducedChain (subtypeInclusion U) q).map_zero.symm)

end Wikipedia.HopfProblem.DegreeCollapse.SmallIntegralCap
