import Wikipedia.HopfProblem.DegreeCollapseIntegralRelativeCohomologyMayerVietoris

/-!
# The original signed integral relative cohomology maps

In the canonical product coordinates, the first Mayer--Vietoris map
is the pair of original restrictions and the second is their actual
integer difference. Agreement therefore lifts to an original relative
class on the union, without any replacement exactness assumption.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralRelativeCohomologyMayerVietoris

open SingularCohomologyFree NoExoticSixSphere

variable {X : Type} [TopologicalSpace X] (U V : Set X)

theorem firstMap_apply (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (a : Cohomology (U ∪ V) n) :
    firstMap U V hU hV n a =
      ((HomologicalComplex.homologyMap (dualMap
          (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
            (Set.subset_union_left : U ⊆ U ∪ V))) n).hom a,
        (HomologicalComplex.homologyMap (dualMap
          (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
            (Set.subset_union_right : V ⊆ U ∪ V))) n).hom a) := by
  rw [firstMap_eq]
  exact IntegralCochainBiproduct.cohomologyBiprodEquiv_map_desc _ _ n a

/-- The minus sign is retained in the original integral pullback formula. -/
theorem differenceMap_apply (n : ℕ) (a : Cohomology U n) (b : Cohomology V n) :
    differenceMap U V n (a, b) =
      (HomologicalComplex.homologyMap (dualMap
        (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
          (Set.inter_subset_left : U ∩ V ⊆ U))) n).hom a -
      (HomologicalComplex.homologyMap (dualMap
        (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
          (Set.inter_subset_right : U ∩ V ⊆ V))) n).hom b := by
  have he := IntegralCochainBiproduct.cohomologyBiprodEquiv_map_lift
    (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) (Set.inter_subset_left : U ∩ V ⊆ U))
    (-RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) (Set.inter_subset_right : U ∩ V ⊆ V))
    n ((middleEquiv U V n).symm (a, b))
  change differenceMap U V n (a, b) =
    (HomologicalComplex.homologyMap (dualMap
      (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) Set.inter_subset_left)) n).hom
      (middleEquiv U V n ((middleEquiv U V n).symm (a, b))).1 +
    (HomologicalComplex.homologyMap (dualMap
      (-RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) Set.inter_subset_right)) n).hom
      (middleEquiv U V n ((middleEquiv U V n).symm (a, b))).2 at he
  rw [LinearEquiv.apply_symm_apply, IntegralCochainBiproduct.dualMap_neg,
    HomologicalComplex.homologyMap_neg] at he
  simpa only [ModuleCat.hom_neg, LinearMap.neg_apply, sub_eq_add_neg] using he

theorem exists_lift_of_agree (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (a : Cohomology U n) (b : Cohomology V n)
    (hab : (HomologicalComplex.homologyMap (dualMap
        (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
          (Set.inter_subset_left : U ∩ V ⊆ U))) n).hom a =
      (HomologicalComplex.homologyMap (dualMap
        (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
          (Set.inter_subset_right : U ∩ V ⊆ V))) n).hom b) :
    ∃ c : Cohomology (U ∪ V) n,
      (HomologicalComplex.homologyMap (dualMap
          (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
            (Set.subset_union_left : U ⊆ U ∪ V))) n).hom c = a ∧
        (HomologicalComplex.homologyMap (dualMap
          (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
            (Set.subset_union_right : V ⊆ U ∪ V))) n).hom c = b := by
  have hz : (a, b) ∈ LinearMap.ker (differenceMap U V n) := by
    change differenceMap U V n (a, b) = 0
    rw [differenceMap_apply, hab, sub_self]
  obtain ⟨c, hc⟩ := (exact_middle U V hU hV n).ge hz
  rw [firstMap_apply] at hc
  exact ⟨c, congrArg Prod.fst hc, congrArg Prod.snd hc⟩

end Wikipedia.HopfProblem.DegreeCollapse.IntegralRelativeCohomologyMayerVietoris
