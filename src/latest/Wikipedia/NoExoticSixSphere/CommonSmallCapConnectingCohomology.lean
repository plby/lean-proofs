import Wikipedia.NoExoticSixSphere.CommonSmallCapConnecting
import Wikipedia.NoExoticSixSphere.RelativeModTwoConnectingUnionCocycles

/-!
# Cap representatives for the two original connecting maps

The original cohomological connecting class has a union-relative
representative. Its overlap cap class equals the homological connecting
of the original relative cap. Actual cochain lifts and their overlap
coboundary primitive prove this comparison on common-small chains.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.CommonSmallModTwoCap

open ModTwoCapProduct (Coefficient)
open SingularSubcomplex (SmallChains smallInclusionMap)

variable {X : Type} [TopologicalSpace X] (U A V B : Set X)

/-- Relative cap and both original connecting maps agree on common-small representatives. -/
theorem connecting_relative_cap_representative
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hA : IsOpen A) (hB : IsOpen B) (p q : ℕ)
    (α : RelativeModTwoCochains.Cocycle (A ∩ B) p)
    (θ : RelativeModTwoCochains.Cocycle (A ∪ B) (p + 1))
    (hθ : SingularCohomologyFree.cocycleClass _ (p + 1) θ =
      RelativeModTwoMayerVietoris.connecting A B hA hB p
        (SingularCohomologyFree.cocycleClass _ p α))
    (c : (complex U A V B).X (p + q + 1))
    (z : ModuleHomology.Cycle (RelativeCoefficients.complex Coefficient (A ∩ B)) (p + (q + 1)))
    (hz : z.val = RelativeCoefficients.quotientMap Coefficient (A ∩ B) (p + q + 1)
      (((inclusion U A V B).f (p + q + 1)).hom c)) :
    ∃ w : ModuleHomology.Cycle (modComplex 2 (U ∩ V : Set X)) q,
      w.val = capInDegree U A V B (p := p + 1) (q := q) (by omega)
        (SmallRelativeModTwoCochains.unionCocycle A B (p + 1) θ).val c ∧
      ModTwoMayerVietoris.connecting U V hU hV hcover q
        (RelativeModTwoCap.homologyCap (A ∩ B) p (q + 1) α.val
          (RelativeModTwoCochains.cocycle_coboundary_zero (A ∩ B) p α)
          (ModuleHomology.cycleClass _ (p + (q + 1)) z)) =
        ModuleHomology.cycleClass (modComplex 2 (U ∩ V : Set X)) q w := by
  obtain ⟨β, γ, η, hdiff, _, hβ, hγ, hη⟩ :=
    RelativeModTwoMayerVietoris.exists_connecting_absolute_cochains A B p α
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
  let a := RelativeModTwoCap.capCycles (A ∩ B) p (q + 1) α.val
    (RelativeModTwoCochains.cocycle_coboundary_zero (A ∩ B) p α) z
  have ha : a.val = ModTwoCapProduct.capInDegree (p := p) (q := q + 1) (by omega)
      (RelativeModTwoCochains.toAbsolute (A ∩ B) p α.val)
        (((inclusion U A V B).f (p + q + 1)).hom c) :=
    (RelativeModTwoCap.capCycles_val (A ∩ B) p (q + 1) α.val
      (RelativeModTwoCochains.cocycle_coboundary_zero (A ∩ B) p α) z).trans
        ((congrArg (RelativeModTwoCap.capInDegree (A ∩ B) (p := p) (q := q + 1)
          (n := p + q + 1) (by omega) α.val) hz).trans
            (RelativeModTwoCap.capInDegree_quotientMap (A ∩ B) (p := p) (q := q + 1)
              (by omega) α.val _))
  let wη := capCycle U A V B (p := p + 1) (q := q) (n := p + q + 1) (by omega) η c hcA
  let wθ := capCycle U A V B (p := p + 1) (q := q) (n := p + q + 1) (by omega)
    (SmallRelativeModTwoCochains.unionCocycle A B (p + 1) θ) c hcA
  have hconnect := connecting_cap_representatives U A V B hU hV hcover p q
    (RelativeModTwoCochains.toAbsolute (A ∩ B) p α.val) β γ hdiff.symm η.val hβ hγ
    c hc cU hcU cV hcV a ha wη rfl
  have hclasses := RelativeModTwoMayerVietoris.unionCocycle_class_of_connecting
    A B hA hB p (SingularCohomologyFree.cocycleClass _ p α) η hη θ hθ
  have hcaps := capCycle_class_eq_of_cohomology_eq U A V B (p := p) (q := q)
    (n := p + q + 1) (by omega)
    (SmallRelativeModTwoCochains.unionCocycle A B (p + 1) θ) η hclasses c hcA
  refine ⟨wθ, rfl, ?_⟩
  exact (congrArg (ModTwoMayerVietoris.connecting U V hU hV hcover q)
    (RelativeModTwoCap.homologyCap_cycleClass (A ∩ B) p (q + 1) α.val
      (RelativeModTwoCochains.cocycle_coboundary_zero (A ∩ B) p α) z)).trans
        (hconnect.trans hcaps.symm)

end NoExoticSixSphere.CommonSmallModTwoCap
