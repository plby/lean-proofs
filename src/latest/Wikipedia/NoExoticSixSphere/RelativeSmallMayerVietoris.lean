import Wikipedia.NoExoticSixSphere.RelativeSmallUnionQuotient

/-!
# The actual relative small-chain Mayer–Vietoris sequence

The first two terms are the original relative singular complexes for the
intersection and the two subsets. The last is the original ambient complex
modulo small chains. The difference and sum maps are retained explicitly,
and comparison with the subcomplex quotient row proves short exactness.
-/

noncomputable section

open CategoryTheory Limits

namespace NoExoticSixSphere.RelativeMayerVietoris

open RelativeCoefficients SingularSubcomplex

variable {X : Type} [TopologicalSpace X] (R : ModuleCat.{0} ℤ) (U V : Set X)

/-- The original first relative quotient maps into the small-relative quotient. -/
def toSmallLeft : complex R U ⟶ smallRelativeComplex R U V :=
  (supportRelativeIso R U).hom ≫
    SubcomplexRelative.mapChain R (le_sup_left : support U ≤ support U ⊔ support V)

def toSmallRight : complex R V ⟶ smallRelativeComplex R U V :=
  (supportRelativeIso R V).hom ≫
    SubcomplexRelative.mapChain R (le_sup_right : support V ≤ support U ⊔ support V)

@[reassoc]
theorem projection_toSmallLeft : projection R U ≫ toSmallLeft R U V =
    smallRelativeProjection R U V := by
  change projection R U ≫ ((supportRelativeIso R U).hom ≫ _) = _
  exact (projection_supportRelativeIso_assoc R U _).trans
    (SubcomplexRelative.projection_mapChain R le_sup_left)

@[reassoc]
theorem projection_toSmallRight : projection R V ≫ toSmallRight R U V =
    smallRelativeProjection R U V := by
  change projection R V ≫ ((supportRelativeIso R V).hom ≫ _) = _
  exact (projection_supportRelativeIso_assoc R V _).trans
    (SubcomplexRelative.projection_mapChain R le_sup_right)

theorem intersection_comm :
    subsetMap R (Set.inter_subset_left : U ∩ V ⊆ U) ≫ toSmallLeft R U V =
      subsetMap R (Set.inter_subset_right : U ∩ V ⊆ V) ≫ toSmallRight R U V := by
  apply (cancel_epi (cokernel.π (inclusion R (U ∩ V)))).mp
  change projection R (U ∩ V) ≫ (_ ≫ _) = projection R (U ∩ V) ≫ (_ ≫ _)
  rw [projection_subsetMap_assoc, projection_toSmallLeft,
    projection_subsetMap_assoc, projection_toSmallRight]

abbrev leftMap : complex R (U ∩ V) ⟶ complex R U ⊞ complex R V :=
  biprod.lift (subsetMap R (Set.inter_subset_left : U ∩ V ⊆ U))
    (-subsetMap R (Set.inter_subset_right : U ∩ V ⊆ V))

abbrev smallRightMap : complex R U ⊞ complex R V ⟶ smallRelativeComplex R U V :=
  biprod.desc (toSmallLeft R U V) (toSmallRight R U V)

abbrev smallSequence : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (leftMap R U V) (smallRightMap R U V)
    (by rw [biprod.lift_desc, Preadditive.neg_comp, intersection_comm, add_neg_cancel])

theorem intersectionRelativeIso_left :
    (intersectionRelativeIso R U V).hom ≫
        SubcomplexRelative.mapChain R (inf_le_left : support U ⊓ support V ≤ support U) =
      subsetMap R (Set.inter_subset_left : U ∩ V ⊆ U) ≫ (supportRelativeIso R U).hom := by
  apply (cancel_epi (cokernel.π (inclusion R (U ∩ V)))).mp
  change projection R (U ∩ V) ≫ (_ ≫ _) = projection R (U ∩ V) ≫ (_ ≫ _)
  exact (projection_intersectionRelativeIso_assoc R U V _).trans
    ((SubcomplexRelative.projection_mapChain R inf_le_left).trans
      ((projection_subsetMap_assoc R Set.inter_subset_left _).trans
        (projection_supportRelativeIso R U)).symm)

theorem intersectionRelativeIso_right :
    (intersectionRelativeIso R U V).hom ≫
        SubcomplexRelative.mapChain R (inf_le_right : support U ⊓ support V ≤ support V) =
      subsetMap R (Set.inter_subset_right : U ∩ V ⊆ V) ≫ (supportRelativeIso R V).hom := by
  apply (cancel_epi (cokernel.π (inclusion R (U ∩ V)))).mp
  change projection R (U ∩ V) ≫ (_ ≫ _) = projection R (U ∩ V) ≫ (_ ≫ _)
  exact (projection_intersectionRelativeIso_assoc R U V _).trans
    ((SubcomplexRelative.projection_mapChain R inf_le_right).trans
      ((projection_subsetMap_assoc R Set.inter_subset_right _).trans
        (projection_supportRelativeIso R V)).symm)

/-- The canonical relative comparison retains both original inclusion maps. -/
def smallSequenceComparison :
    smallSequence R U V ⟶ SubcomplexRelative.sequence R (support U) (support V) where
  τ₁ := (intersectionRelativeIso R U V).hom
  τ₂ := biprod.map (supportRelativeIso R U).hom (supportRelativeIso R V).hom
  τ₃ := 𝟙 (smallRelativeComplex R U V)
  comm₁₂ := by
    change (intersectionRelativeIso R U V).hom ≫
        biprod.lift (SubcomplexRelative.mapChain R inf_le_left)
          (-SubcomplexRelative.mapChain R inf_le_right) =
      biprod.lift (subsetMap R Set.inter_subset_left) (-subsetMap R Set.inter_subset_right) ≫
        biprod.map (supportRelativeIso R U).hom (supportRelativeIso R V).hom
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst,
        biprod.lift_fst_assoc, intersectionRelativeIso_left]
    · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc,
        Preadditive.comp_neg, Preadditive.neg_comp, intersectionRelativeIso_right]
  comm₂₃ := by
    change biprod.map (supportRelativeIso R U).hom (supportRelativeIso R V).hom ≫
        biprod.desc (SubcomplexRelative.mapChain R le_sup_left)
          (SubcomplexRelative.mapChain R le_sup_right) =
      biprod.desc (toSmallLeft R U V) (toSmallRight R U V) ≫ 𝟙 (smallRelativeComplex R U V)
    rw [Category.comp_id]
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_desc]
      rfl
    · simp only [biprod.inr_map_assoc, biprod.inr_desc]
      rfl

instance smallSequenceComparison_isIso : IsIso (smallSequenceComparison R U V) := by
  apply (ShortComplex.isIso_iff _).mpr
  refine ⟨?_, ?_, ?_⟩
  · exact inferInstanceAs (IsIso (intersectionRelativeIso R U V).hom)
  · exact inferInstanceAs
      (IsIso (biprod.mapIso (supportRelativeIso R U) (supportRelativeIso R V)).hom)
  · exact inferInstanceAs (IsIso (𝟙 (smallRelativeComplex R U V)))

/-- The actual relative small-chain sequence is short exact with arbitrary coefficients. -/
theorem smallSequence_shortExact : (smallSequence R U V).ShortExact :=
  ShortComplex.shortExact_of_iso (asIso (smallSequenceComparison R U V)).symm
    (SubcomplexRelative.sequence_shortExact R (support U) (support V))

end NoExoticSixSphere.RelativeMayerVietoris
