import Wikipedia.NoExoticSixSphere.RelativeMayerVietoris

/-!
# Subset maps on the original relative Mayer--Vietoris chain sequence

Enlarging both subspaces gives a map of the actual small-relative
short exact rows. The quotient maps retain their original projection
formulas, including the comparison with the relative open union.
-/

noncomputable section

open CategoryTheory Limits

namespace NoExoticSixSphere.RelativeCoefficients

open SingularSubcomplex

variable {X : Type} [TopologicalSpace X] (R : ModuleCat.{0} ℤ)
  {U V U' V' W : Set X}

theorem subsetMap_trans (h : U ⊆ V) (k : V ⊆ W) :
    subsetMap R h ≫ subsetMap R k = subsetMap R (h.trans k) := by
  change mapChain R (ContinuousMap.id X) _ ≫ mapChain R (ContinuousMap.id X) _ = _
  rw [← mapChain_comp]
  rfl

/-- The original identity-ambient quotient map on the two small-relative complexes. -/
def smallSubsetMap (hU : U ⊆ U') (hV : V ⊆ V') :
    smallRelativeComplex R U V ⟶ smallRelativeComplex R U' V' :=
  SubcomplexRelative.mapChain R (sup_le_sup (support_mono hU) (support_mono hV))

theorem projection_smallSubsetMap (hU : U ⊆ U') (hV : V ⊆ V') :
    smallRelativeProjection R U V ≫ smallSubsetMap R hU hV =
      smallRelativeProjection R U' V' :=
  SubcomplexRelative.projection_mapChain R _

/-- The small-to-union comparison commutes with the original subset quotient maps. -/
theorem smallSubsetMap_quotient (hU : U ⊆ U') (hV : V ⊆ V') :
    smallSubsetMap R hU hV ≫ smallToUnionQuotient R U' V' =
      smallToUnionQuotient R U V ≫ subsetMap R (Set.union_subset_union hU hV) := by
  apply (cancel_epi (smallRelativeProjection R U V)).mp
  rw [← Category.assoc, projection_smallSubsetMap, projection_smallToUnionQuotient,
    projection_smallToUnionQuotient_assoc]
  exact (projection_subsetMap R (Set.union_subset_union hU hV)).symm

end NoExoticSixSphere.RelativeCoefficients

namespace NoExoticSixSphere.RelativeMayerVietoris

open RelativeCoefficients

variable {X : Type} [TopologicalSpace X] (R : ModuleCat.{0} ℤ) {U V U' V' : Set X}

theorem toSmallLeft_subset (hU : U ⊆ U') (hV : V ⊆ V') :
    toSmallLeft R U V ≫ smallSubsetMap R hU hV = subsetMap R hU ≫ toSmallLeft R U' V' := by
  apply (cancel_epi (cokernel.π (inclusion R U))).mp
  change projection R U ≫ (_ ≫ _) = projection R U ≫ (_ ≫ _)
  exact (projection_toSmallLeft_assoc R U V _).trans
    ((projection_smallSubsetMap R hU hV).trans
      ((projection_subsetMap_assoc R hU _).trans (projection_toSmallLeft R U' V')).symm)

theorem toSmallRight_subset (hU : U ⊆ U') (hV : V ⊆ V') :
    toSmallRight R U V ≫ smallSubsetMap R hU hV = subsetMap R hV ≫ toSmallRight R U' V' := by
  apply (cancel_epi (cokernel.π (inclusion R V))).mp
  change projection R V ≫ (_ ≫ _) = projection R V ≫ (_ ≫ _)
  exact (projection_toSmallRight_assoc R U V _).trans
    ((projection_smallSubsetMap R hU hV).trans
      ((projection_subsetMap_assoc R hV _).trans (projection_toSmallRight R U' V')).symm)

/-- A map of original small-relative Mayer--Vietoris rows under enlargement of both subspaces. -/
def smallSequenceSubsetMap (hU : U ⊆ U') (hV : V ⊆ V') :
    smallSequence R U V ⟶ smallSequence R U' V' where
  τ₁ := subsetMap R (Set.inter_subset_inter hU hV)
  τ₂ := biprod.map (subsetMap R hU) (subsetMap R hV)
  τ₃ := smallSubsetMap R hU hV
  comm₁₂ := by
    change subsetMap R _ ≫ leftMap R U' V' =
      leftMap R U V ≫ biprod.map (subsetMap R hU) (subsetMap R hV)
    apply biprod.hom_ext
    · simp only [leftMap, Category.assoc, biprod.lift_fst, biprod.map_fst,
        biprod.lift_fst_assoc, subsetMap_trans]
    · simp only [leftMap, Category.assoc, biprod.lift_snd, biprod.map_snd,
        biprod.lift_snd_assoc, Preadditive.comp_neg, Preadditive.neg_comp, subsetMap_trans]
  comm₂₃ := by
    change biprod.map (subsetMap R hU) (subsetMap R hV) ≫ smallRightMap R U' V' =
      smallRightMap R U V ≫ smallSubsetMap R hU hV
    apply biprod.hom_ext'
    · simp only [smallRightMap, biprod.inl_map_assoc, biprod.inl_desc,
        biprod.inl_desc_assoc, toSmallLeft_subset]
    · simp only [smallRightMap, biprod.inr_map_assoc, biprod.inr_desc,
        biprod.inr_desc_assoc, toSmallRight_subset]

end NoExoticSixSphere.RelativeMayerVietoris
