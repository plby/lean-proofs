import Wikipedia.HopfProblem.DegreeCollapseCommonSmallIntegralCapConnecting
import Wikipedia.HopfProblem.DegreeCollapseCommonSmallIntegralCapCohomology
import Wikipedia.HopfProblem.DegreeCollapseIntegralConnectingUnionCocycles

/-!
# Integral cap representatives for the two original connecting maps

The original cohomological connecting class has a union-relative
representative. The original homological connecting of the relative cap
equals -(-1)^p times its actual overlap cap class. Actual cochain lifts
and their overlap coboundary primitive prove this comparison on common-small chains.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris NoExoticSixSphere

namespace Wikipedia.HopfProblem.DegreeCollapse.CommonSmallIntegralCap

open IntegralCap (Coefficient)
open SingularSubcomplex (SmallChains smallInclusionMap)

variable {X : Type} [TopologicalSpace X] (U A V B : Set X)

/-- The original integral connecting maps agree on cap representatives with the signed factor. -/
theorem connecting_relative_cap_representative
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (α : RelativeIntegralCap.Cocycle (A ∩ B) p)
    (θ : RelativeIntegralCap.Cocycle (A ∪ B) (p + 1))
    (hθ : SingularCohomologyFree.cocycleClass _ (p + 1) θ =
      IntegralRelativeCohomologyMayerVietoris.connecting A B hA hB p
        (SingularCohomologyFree.cocycleClass _ p α))
    (c : (complex U A V B).X (p + q + 1))
    (z : ModuleHomology.Cycle (RelativeCoefficients.complex Coefficient (A ∩ B)) (p + (q + 1)))
    (hz : z.val = RelativeCoefficients.quotientMap Coefficient (A ∩ B) (p + q + 1)
      (((inclusion U A V B).f (p + q + 1)).hom c)) :
    ∃ w : ModuleHomology.Cycle (singularComplex (U ∩ V : Set X)) q,
      w.val = capInDegree U A V B (p := p + 1) (q := q) (by omega)
        (SmallRelativeIntegralCochains.unionCocycle A B (p + 1) θ).val c ∧
      connectingHomomorphism U V hU hV hcover q
        (RelativeIntegralCap.homologyCap (A ∩ B) p (q + 1) α.val
          (RelativeIntegralCap.cocycle_coboundary_zero (A ∩ B) p α)
          (ModuleHomology.cycleClass _ (p + (q + 1)) z)) =
        -((-1 : ℤ) ^ p) • ModuleHomology.cycleClass (singularComplex (U ∩ V : Set X)) q w := by
  obtain ⟨β, γ, η, hdiff, _, hβ, hγ, hη⟩ :=
    IntegralRelativeCohomologyMayerVietoris.exists_connecting_absolute_cochains A B p α
  have hdz : ((RelativeCoefficients.complex Coefficient (A ∩ B)).d
      (p + q + 1) (p + q)).hom z.val = 0 :=
    (congrArg (fun j => ((RelativeCoefficients.complex Coefficient (A ∩ B)).d
      (p + (q + 1)) j).hom z.val = 0) (show p + (q + 1) - 1 = p + q by omega)).mp
        (ModuleHomology.cycle_condition _ (p + (q + 1)) z)
  have hdq : ((RelativeCoefficients.complex Coefficient (A ∩ B)).d
      (p + q + 1) (p + q)).hom
        (RelativeCoefficients.quotientMap Coefficient (A ∩ B) (p + q + 1)
          (((inclusion U A V B).f (p + q + 1)).hom c)) = 0 :=
    (congrArg ((RelativeCoefficients.complex Coefficient (A ∩ B)).d
      (p + q + 1) (p + q)).hom hz).symm.trans hdz
  have hc : ((inclusion U A V B).f (p + q)).hom
      (((complex U A V B).d (p + q + 1) (p + q)).hom c) ∈
      LinearMap.range ((RelativeCoefficients.inclusion Coefficient (A ∩ B)).f (p + q)).hom :=
    (RelativeCoefficients.quotientMap_eq_zero_iff Coefficient (A ∩ B) (p + q) _).mp
      ((congrArg (RelativeCoefficients.quotientMap Coefficient (A ∩ B) (p + q))
        (boundary_inclusion U A V B (p + q + 1) (p + q) c)).symm.trans
          ((RelativeCoefficients.boundary_quotientMap Coefficient (A ∩ B)
            (p + q + 1) (p + q) _).symm.trans hdq))
  have hcA : ((inclusion U A V B).f ((p + q + 1) - 1)).hom
      (((complex U A V B).d (p + q + 1) ((p + q + 1) - 1)).hom c) ∈
      LinearMap.range ((RelativeCoefficients.inclusion Coefficient A).f ((p + q + 1) - 1)).hom :=
    (congrArg (fun j => ((inclusion U A V B).f j).hom
      (((complex U A V B).d (p + q + 1) j).hom c) ∈
        LinearMap.range ((RelativeCoefficients.inclusion Coefficient A).f j).hom)
      (Nat.add_sub_cancel (p + q) 1)).mpr
        ((SingularSubcomplex.inclusion_range_inter Coefficient A B (p + q)).le hc).1
  have hsmall :=
    (SingularSubcomplex.commonSmallInclusion_range U A V B Coefficient (p + q + 1)).le ⟨c, rfl⟩
  obtain ⟨cU, hcU⟩ := hsmall.1
  obtain ⟨cV, hcV⟩ := hsmall.2
  let a := RelativeIntegralCap.capCycles (A ∩ B) p (q + 1) α.val
    (RelativeIntegralCap.cocycle_coboundary_zero (A ∩ B) p α) z
  have ha : a.val = IntegralCap.capInDegree (p := p) (q := q + 1) (by omega)
      (RelativeIntegralCap.toAbsolute (A ∩ B) p α.val)
        (((inclusion U A V B).f (p + q + 1)).hom c) :=
    (RelativeIntegralCap.capCycles_val (A ∩ B) p (q + 1) α.val
      (RelativeIntegralCap.cocycle_coboundary_zero (A ∩ B) p α) z).trans
        ((congrArg (RelativeIntegralCap.capInDegree (A ∩ B) (p := p) (q := q + 1)
          (n := p + q + 1) (by omega) α.val) hz).trans
            (RelativeIntegralCap.capInDegree_quotientMap (A ∩ B) (p := p) (q := q + 1)
              (by omega) α.val _))
  let wη := capCycle U A V B (p := p + 1) (q := q) (n := p + q + 1) (by omega) η c hcA
  let wθ := capCycle U A V B (p := p + 1) (q := q) (n := p + q + 1) (by omega)
    (SmallRelativeIntegralCochains.unionCocycle A B (p + 1) θ) c hcA
  have hconnect := connecting_cap_representatives U A V B hU hV hcover p q
    (RelativeIntegralCap.toAbsolute (A ∩ B) p α.val) β γ hdiff.symm η.val hβ hγ
    c hc cU hcU cV hcV a ha wη rfl
  have hclasses := IntegralRelativeCohomologyMayerVietoris.unionCocycle_class_of_connecting
    A B hA hB p (SingularCohomologyFree.cocycleClass _ p α) η hη θ hθ
  have hcaps := capCycle_class_eq_of_cohomology_eq U A V B (p := p) (q := q)
    (n := p + q + 1) (by omega)
    (SmallRelativeIntegralCochains.unionCocycle A B (p + 1) θ) η hclasses c hcA
  refine ⟨wθ, rfl, ?_⟩
  exact (congrArg (connectingHomomorphism U V hU hV hcover q)
    (RelativeIntegralCap.homologyCap_cycleClass (A ∩ B) p (q + 1) α.val
      (RelativeIntegralCap.cocycle_coboundary_zero (A ∩ B) p α) z)).trans
        (hconnect.trans (congrArg (fun t => -((-1 : ℤ) ^ p) • t) hcaps.symm))

end Wikipedia.HopfProblem.DegreeCollapse.CommonSmallIntegralCap
