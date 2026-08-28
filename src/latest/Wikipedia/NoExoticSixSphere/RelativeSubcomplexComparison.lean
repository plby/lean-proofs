import Wikipedia.NoExoticSixSphere.SingularSmallSubcomplex
import Wikipedia.NoExoticSixSphere.SubcomplexRelativeExact

/-!
# Original relative singular complexes and actual subcomplex quotients

The native singular set of a subspace is isomorphic to its actual range
subcomplex. Taking the original cokernels gives canonical relative-chain
isomorphisms whose forward maps retain the quotient projections.
-/

noncomputable section

open CategoryTheory Limits

namespace NoExoticSixSphere.RelativeCoefficients

open SimplicialCoefficients SingularSubcomplex

variable {X : Type} [TopologicalSpace X] (R : ModuleCat.{0} ℤ)

/-- The original relative complex is canonically the quotient by the actual singular subcomplex. -/
def supportRelativeIso (U : Set X) :
    complex R U ≅ SubcomplexRelative.complex R (support U) :=
  cokernel.mapIso (inclusion R U) ((chains R).map (support U).ι)
    ((chains R).mapIso (supportIso U)) (Iso.refl _) (by
      change (chains R).map (SingularSubcomplex.inclusion U) ≫
          𝟙 ((singular X).chainComplex R) =
        (chains R).map (supportIso U).hom ≫ (chains R).map (support U).ι
      rw [Category.comp_id, ← Functor.map_comp, supportIso_hom_inclusion])

@[reassoc]
theorem projection_supportRelativeIso (U : Set X) :
    projection R U ≫ (supportRelativeIso R U).hom = SubcomplexRelative.projection R (support U) :=
  (cokernel.π_desc _ _ _).trans (Category.id_comp _)

/-- The original relative complex for the intersection, with its actual intersection subcomplex. -/
def intersectionRelativeIso (U V : Set X) :
    complex R (U ∩ V) ≅ SubcomplexRelative.complex R (support U ⊓ support V) :=
  cokernel.mapIso (inclusion R (U ∩ V)) ((chains R).map (support U ⊓ support V).ι)
    ((chains R).mapIso (intersectionIso U V)) (Iso.refl _) (by
      change (chains R).map (SingularSubcomplex.inclusion (U ∩ V)) ≫
          𝟙 ((singular X).chainComplex R) =
        (chains R).map (intersectionIso U V).hom ≫ (chains R).map (support U ⊓ support V).ι
      rw [Category.comp_id, ← Functor.map_comp, intersectionIso_hom_inclusion])

@[reassoc]
theorem projection_intersectionRelativeIso (U V : Set X) :
    projection R (U ∩ V) ≫ (intersectionRelativeIso R U V).hom =
      SubcomplexRelative.projection R (support U ⊓ support V) :=
  (cokernel.π_desc _ _ _).trans (Category.id_comp _)

/-- Subset inclusion acts by the actual identity-ambient relative map. -/
abbrev subsetMap {U V : Set X} (h : U ⊆ V) : complex R U ⟶ complex R V :=
  mapChain R (ContinuousMap.id X) (show Set.MapsTo (ContinuousMap.id X) U V from h)

@[reassoc]
theorem projection_subsetMap {U V : Set X} (h : U ⊆ V) :
    projection R U ≫ subsetMap R h = projection R V := by
  rw [projection_mapChain, spaceMap_id, Category.id_comp]

/-- The canonical comparison commutes with the actual subset map. -/
theorem supportRelativeIso_subsetMap {U V : Set X} (h : U ⊆ V) :
    (supportRelativeIso R U).hom ≫ SubcomplexRelative.mapChain R (support_mono h) =
      subsetMap R h ≫ (supportRelativeIso R V).hom := by
  apply (cancel_epi (cokernel.π (inclusion R U))).mp
  change projection R U ≫ (_ ≫ _) = projection R U ≫ (_ ≫ _)
  exact (projection_supportRelativeIso_assoc R U _).trans
    ((SubcomplexRelative.projection_mapChain R (support_mono h)).trans
      ((projection_subsetMap_assoc R h _).trans (projection_supportRelativeIso R V)).symm)

end NoExoticSixSphere.RelativeCoefficients
