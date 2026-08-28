import Wikipedia.NoExoticSixSphere.RelativeModTwoMayerVietoris
import Wikipedia.NoExoticSixSphere.ModTwoDualBiproductMaps

/-!
# Original restriction and difference maps in relative cohomological Mayer--Vietoris

The canonical product marking retains the actual identity-ambient maps
of pairs. The first map is the pair of pullbacks from the union, and
the second is the difference of the pullbacks to the intersection.
-/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.RelativeModTwoMayerVietoris

open RelativeModTwoCochains (Cohomology)

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- The first map has the two original pair pullbacks as its actual coordinates. -/
theorem firstMap_apply (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (a : Cohomology (U ∪ V) n) :
    firstMap U V hU hV n a =
      ((HomologicalComplex.homologyMap (ModTwoDualComplex.map
          (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
            (Set.subset_union_left : U ⊆ U ∪ V))) n).hom a,
        (HomologicalComplex.homologyMap (ModTwoDualComplex.map
          (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
            (Set.subset_union_right : V ⊆ U ∪ V))) n).hom a) := by
  rw [firstMap_eq]
  exact ModTwoDualComplex.cohomologyBiprodEquiv_map_desc _ _ n a

/-- The second map is the difference of the original pair pullbacks. -/
theorem differenceMap_apply (n : ℕ) (a : Cohomology U n) (b : Cohomology V n) :
    differenceMap U V n (a, b) =
      (HomologicalComplex.homologyMap (ModTwoDualComplex.map
        (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
          (Set.inter_subset_left : U ∩ V ⊆ U))) n).hom a -
      (HomologicalComplex.homologyMap (ModTwoDualComplex.map
        (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
          (Set.inter_subset_right : U ∩ V ⊆ V))) n).hom b := by
  have he := ModTwoDualComplex.cohomologyBiprodEquiv_map_lift
    (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) (Set.inter_subset_left : U ∩ V ⊆ U))
    (-RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) (Set.inter_subset_right : U ∩ V ⊆ V))
    n ((middleEquiv U V n).symm (a, b))
  change differenceMap U V n (a, b) =
    (HomologicalComplex.homologyMap (ModTwoDualComplex.map
      (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) Set.inter_subset_left)) n).hom
      (middleEquiv U V n ((middleEquiv U V n).symm (a, b))).1 +
    (HomologicalComplex.homologyMap (ModTwoDualComplex.map
      (-RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) Set.inter_subset_right)) n).hom
      (middleEquiv U V n ((middleEquiv U V n).symm (a, b))).2 at he
  rw [LinearEquiv.apply_symm_apply, ModTwoDualComplex.map_neg,
    HomologicalComplex.homologyMap_neg] at he
  simpa only [ModuleCat.hom_neg, LinearMap.neg_apply, sub_eq_add_neg] using he

/-- A pair whose original difference vanishes comes from an actual class on the union. -/
theorem exists_lift_of_agree (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (a : Cohomology U n) (b : Cohomology V n)
    (hab : (HomologicalComplex.homologyMap (ModTwoDualComplex.map
        (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
          (Set.inter_subset_left : U ∩ V ⊆ U))) n).hom a =
      (HomologicalComplex.homologyMap (ModTwoDualComplex.map
        (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
          (Set.inter_subset_right : U ∩ V ⊆ V))) n).hom b) :
    ∃ c : Cohomology (U ∪ V) n,
      (HomologicalComplex.homologyMap (ModTwoDualComplex.map
          (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
            (Set.subset_union_left : U ⊆ U ∪ V))) n).hom c = a ∧
        (HomologicalComplex.homologyMap (ModTwoDualComplex.map
          (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
            (Set.subset_union_right : V ⊆ U ∪ V))) n).hom c = b := by
  have hz : (a, b) ∈ LinearMap.ker (differenceMap U V n) := by
    change differenceMap U V n (a, b) = 0
    rw [differenceMap_apply, hab, sub_self]
  obtain ⟨c, hc⟩ := (exact_middle U V hU hV n).ge hz
  rw [firstMap_apply] at hc
  exact ⟨c, congrArg Prod.fst hc, congrArg Prod.snd hc⟩

end NoExoticSixSphere.RelativeModTwoMayerVietoris
