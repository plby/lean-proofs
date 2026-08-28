import Wikipedia.NoExoticSixSphere.RelativeSmallMayerVietoris
import Wikipedia.HopfProblem.SingularMayerVietorisSequenceTransport
import Wikipedia.HopfProblem.SingularMayerVietorisSequenceRightTransport

/-!
# Mayer–Vietoris for the original relative singular homology groups

For two open subsets, the actual relative groups of their intersection,
the two subsets, and their union form a long exact sequence. The incoming
maps are the original identity-ambient pair maps with signs `(+,-)` and
`(+,+)`. The connecting map is transported from the proved small-chain
short exact sequence through its actual open-union quasi-isomorphism.
-/

noncomputable section

open CategoryTheory Limits
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.RelativeMayerVietoris

open RelativeCoefficients

variable {X : Type} [TopologicalSpace X] (R : ModuleCat.{0} ℤ) (U V : Set X)

abbrev rightMap : complex R U ⊞ complex R V ⟶ complex R (U ∪ V) :=
  biprod.desc (subsetMap R (Set.subset_union_left : U ⊆ U ∪ V))
    (subsetMap R (Set.subset_union_right : V ⊆ U ∪ V))

theorem toSmallLeft_quotient :
    toSmallLeft R U V ≫ smallToUnionQuotient R U V = subsetMap R Set.subset_union_left := by
  apply (cancel_epi (cokernel.π (inclusion R U))).mp
  change projection R U ≫ (_ ≫ _) = projection R U ≫ subsetMap R _
  exact (projection_toSmallLeft_assoc R U V _).trans
    ((projection_smallToUnionQuotient R U V).trans (projection_subsetMap R _).symm)

theorem toSmallRight_quotient :
    toSmallRight R U V ≫ smallToUnionQuotient R U V = subsetMap R Set.subset_union_right := by
  apply (cancel_epi (cokernel.π (inclusion R V))).mp
  change projection R V ≫ (_ ≫ _) = projection R V ≫ subsetMap R _
  exact (projection_toSmallRight_assoc R U V _).trans
    ((projection_smallToUnionQuotient R U V).trans (projection_subsetMap R _).symm)

/-- The small-relative comparison factors the original sum map of pairs. -/
theorem smallRightMap_quotient :
    smallRightMap R U V ≫ smallToUnionQuotient R U V = rightMap R U V := by
  apply biprod.hom_ext'
  · simp only [smallRightMap, rightMap, biprod.inl_desc_assoc, biprod.inl_desc,
      toSmallLeft_quotient]
  · simp only [smallRightMap, rightMap, biprod.inr_desc_assoc, biprod.inr_desc,
      toSmallRight_quotient]

def firstMap (n : ℕ) : (complex R (U ∩ V)).homology n →ₗ[ℤ]
    ((complex R U).homology n × (complex R V).homology n) :=
  biprodSequenceFirstMap (leftMap R U V) n

def secondMap (n : ℕ) : ((complex R U).homology n × (complex R V).homology n) →ₗ[ℤ]
    (complex R (U ∪ V)).homology n := biprodSequenceSecondMap (rightMap R U V) n

theorem firstMap_apply (n : ℕ) (a : (complex R (U ∩ V)).homology n) :
    firstMap R U V n a =
      (homologyLinearMap (subsetMap R Set.inter_subset_left) n a,
        -homologyLinearMap (subsetMap R Set.inter_subset_right) n a) :=
  biprodSequenceFirstMap_lift_neg _ _ n a

theorem secondMap_apply (n : ℕ) (a : (complex R U).homology n) (b : (complex R V).homology n) :
    secondMap R U V n (a, b) =
      homologyLinearMap (subsetMap R Set.subset_union_left) n a +
        homologyLinearMap (subsetMap R Set.subset_union_right) n b :=
  biprodSequenceSecondMap_desc _ _ n (a, b)

variable (p : ℕ) (hp : p ≠ 0) (hU : IsOpen U) (hV : IsOpen V)

/-- The actual relative open-union comparison, in homology. -/
def smallUnionEquiv (n : ℕ) :
    (smallRelativeComplex (ModuleCat.of ℤ (ZMod p)) U V).homology n ≃ₗ[ℤ]
      ModHomology p (U ∪ V) n := by
  let := smallToUnionQuotient_mod_quasiIso U V p hp hU hV
  exact (isoOfQuasiIsoAt (smallToUnionQuotient (ModuleCat.of ℤ (ZMod p)) U V) n).toLinearEquiv

theorem secondMap_eq (n : ℕ) :
    secondMap (ModuleCat.of ℤ (ZMod p)) U V n =
      (smallUnionEquiv U V p hp hU hV n).toLinearMap.comp
        (biprodSequenceSecondMap (smallRightMap (ModuleCat.of ℤ (ZMod p)) U V) n) := by
  change (homologyLinearMap (rightMap (ModuleCat.of ℤ (ZMod p)) U V) n).comp _ =
    (homologyLinearMap (smallToUnionQuotient (ModuleCat.of ℤ (ZMod p)) U V) n).comp
      ((homologyLinearMap (smallRightMap (ModuleCat.of ℤ (ZMod p)) U V) n).comp _)
  rw [← LinearMap.comp_assoc, ← homologyLinearMap_comp, smallRightMap_quotient]

/-- The connecting map is the genuine small-chain connecting map under the actual comparison. -/
def connecting (n : ℕ) : ModHomology p (U ∪ V) (n + 1) →ₗ[ℤ] ModHomology p (U ∩ V) n :=
  (connectingMap (smallSequence_shortExact (ModuleCat.of ℤ (ZMod p)) U V) n).comp
    (smallUnionEquiv U V p hp hU hV (n + 1)).symm.toLinearMap

include hp hU hV

theorem exact_left (n : ℕ) :
    LinearMap.range (connecting U V p hp hU hV n) =
      LinearMap.ker (firstMap (ModuleCat.of ℤ (ZMod p)) U V n) := by
  rw [connecting, rightTransport_connecting_range]
  exact biprodSequence_exact_at_leftHomology
    (smallSequence_shortExact (ModuleCat.of ℤ (ZMod p)) U V) n

theorem exact_middle (n : ℕ) :
    LinearMap.range (firstMap (ModuleCat.of ℤ (ZMod p)) U V n) =
      LinearMap.ker (secondMap (ModuleCat.of ℤ (ZMod p)) U V n) := by
  rw [secondMap_eq U V p hp hU hV, rightTransport_second_ker]
  exact biprodSequence_exact_at_middleHomology
    (smallSequence_shortExact (ModuleCat.of ℤ (ZMod p)) U V) n

theorem exact_right (n : ℕ) :
    LinearMap.range (secondMap (ModuleCat.of ℤ (ZMod p)) U V (n + 1)) =
      LinearMap.ker (connecting U V p hp hU hV n) := by
  rw [secondMap_eq U V p hp hU hV]
  exact rightTransport_range_eq_ker (smallUnionEquiv U V p hp hU hV (n + 1)) _ _
    (biprodSequence_exact_at_rightHomology
      (smallSequence_shortExact (ModuleCat.of ℤ (ZMod p)) U V) n)

theorem secondMap_zero_surjective :
    Function.Surjective (secondMap (ModuleCat.of ℤ (ZMod p)) U V 0) := by
  rw [secondMap_eq U V p hp hU hV]
  exact rightTransport_second_surjective (smallUnionEquiv U V p hp hU hV 0) _
    (biprodSequence_second_zero_surjective
      (smallSequence_shortExact (ModuleCat.of ℤ (ZMod p)) U V))

/-- Matching actual relative classes lift together through the original two restriction maps. -/
theorem exists_lift_of_agree (n : ℕ) (a : ModHomology p U n) (b : ModHomology p V n)
    (hab : homologyLinearMap (subsetMap (ModuleCat.of ℤ (ZMod p)) Set.subset_union_left) n a =
      homologyLinearMap (subsetMap (ModuleCat.of ℤ (ZMod p)) Set.subset_union_right) n b) :
    ∃ c : ModHomology p (U ∩ V) n,
      homologyLinearMap (subsetMap (ModuleCat.of ℤ (ZMod p)) Set.inter_subset_left) n c = a ∧
        homologyLinearMap (subsetMap (ModuleCat.of ℤ (ZMod p)) Set.inter_subset_right) n c = b := by
  have hz : secondMap (ModuleCat.of ℤ (ZMod p)) U V n (a, -b) = 0 := by
    rw [secondMap_apply, map_neg, hab, add_neg_cancel]
  have hr : (a, -b) ∈ LinearMap.range (firstMap (ModuleCat.of ℤ (ZMod p)) U V n) := by
    rw [exact_middle U V p hp hU hV n]
    exact hz
  obtain ⟨c, hc⟩ := hr
  rw [firstMap_apply] at hc
  exact ⟨c, congrArg Prod.fst hc, neg_injective (congrArg Prod.snd hc)⟩

end NoExoticSixSphere.RelativeMayerVietoris
