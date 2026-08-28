import Wikipedia.NoExoticSixSphere.SubcomplexChainSequence

/-!
# Actual relative chains of simplicial subcomplexes

The quotient is the native cokernel of the original inclusion. Inclusion
of subcomplexes gives the original identity-ambient map on these quotients.
The two-set relative sequence uses the actual difference and sum of these
maps, with their projection formulas proved explicitly.
-/

noncomputable section

open CategoryTheory Limits

namespace NoExoticSixSphere.SubcomplexRelative

open SimplicialCoefficients

variable (R : ModuleCat.{0} ℤ) {X : SSet.{0}}

abbrev complex (A : X.Subcomplex) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  cokernel ((chains R).map A.ι)

abbrev projection (A : X.Subcomplex) : X.chainComplex R ⟶ complex R A :=
  cokernel.π ((chains R).map A.ι)

theorem inclusion_comp (A B : X.Subcomplex) (h : A ≤ B) :
    (chains R).map A.ι ≫ 𝟙 (X.chainComplex R) =
      (chains R).map (SSet.Subcomplex.homOfLE h) ≫ (chains R).map B.ι := by
  rw [Category.comp_id, ← Functor.map_comp, SSet.Subcomplex.homOfLE_ι]

/-- The actual relative map induced by inclusion of subcomplexes and the ambient identity. -/
def mapChain {A B : X.Subcomplex} (h : A ≤ B) : complex R A ⟶ complex R B :=
  cokernel.map ((chains R).map A.ι) ((chains R).map B.ι)
    ((chains R).map (SSet.Subcomplex.homOfLE h)) (𝟙 (X.chainComplex R))
    (inclusion_comp R A B h)

@[reassoc]
theorem projection_mapChain {A B : X.Subcomplex} (h : A ≤ B) :
    projection R A ≫ mapChain R h = projection R B := by
  exact (cokernel.π_desc _ _ _).trans (Category.id_comp _)

theorem mapChain_trans {A B D : X.Subcomplex} (h : A ≤ B) (k : B ≤ D) :
    mapChain R h ≫ mapChain R k = mapChain R (h.trans k) := by
  apply (cancel_epi (projection R A)).mp
  rw [projection_mapChain_assoc, projection_mapChain, projection_mapChain]

theorem mapChain_refl (A : X.Subcomplex) : mapChain R (le_refl A) = 𝟙 (complex R A) := by
  apply (cancel_epi (projection R A)).mp
  rw [projection_mapChain, Category.comp_id]

variable (A B : X.Subcomplex)

/-- The square of actual relative inclusion maps for the intersection and union. -/
theorem relativeSquare :
    CommSq (mapChain R (inf_le_left : A ⊓ B ≤ A))
      (mapChain R (inf_le_right : A ⊓ B ≤ B))
      (mapChain R (le_sup_left : A ≤ A ⊔ B))
      (mapChain R (le_sup_right : B ≤ A ⊔ B)) where
  w := by rw [mapChain_trans, mapChain_trans]

abbrev sequence : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk
    (biprod.lift (mapChain R (inf_le_left : A ⊓ B ≤ A))
      (-mapChain R (inf_le_right : A ⊓ B ≤ B)))
    (biprod.desc (mapChain R (le_sup_left : A ≤ A ⊔ B))
      (mapChain R (le_sup_right : B ≤ A ⊔ B)))
    (by rw [biprod.lift_desc, Preadditive.neg_comp, (relativeSquare R A B).w, add_neg_cancel])

/-- The projection onto the two native relative quotients. -/
abbrev middleProjection : X.chainComplex R ⊞ X.chainComplex R ⟶ complex R A ⊞ complex R B :=
  biprod.map (projection R A) (projection R B)

/-- The left quotient square retains the actual difference map. -/
theorem projection_sequence_f :
    projection R (A ⊓ B) ≫ (sequence R A B).f =
      (ambientSequence R X).f ≫ middleProjection R A B := by
  change projection R (A ⊓ B) ≫
      biprod.lift (mapChain R inf_le_left) (-mapChain R inf_le_right) =
    biprod.lift (𝟙 (X.chainComplex R)) (-(𝟙 (X.chainComplex R))) ≫
      biprod.map (projection R A) (projection R B)
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst,
      biprod.lift_fst_assoc, Category.id_comp, projection_mapChain]
  · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd,
      biprod.lift_snd_assoc, Preadditive.comp_neg, Preadditive.neg_comp,
      Category.id_comp, projection_mapChain]

/-- The right quotient square retains the actual sum map. -/
theorem projection_sequence_g :
    middleProjection R A B ≫ (sequence R A B).g =
      (ambientSequence R X).g ≫ projection R (A ⊔ B) := by
  change biprod.map (projection R A) (projection R B) ≫
      biprod.desc (mapChain R le_sup_left) (mapChain R le_sup_right) =
    biprod.desc (𝟙 (X.chainComplex R)) (𝟙 (X.chainComplex R)) ≫ projection R (A ⊔ B)
  apply biprod.hom_ext'
  · simp only [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc,
      Category.id_comp, projection_mapChain]
  · simp only [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc,
      Category.id_comp, projection_mapChain]

end NoExoticSixSphere.SubcomplexRelative
