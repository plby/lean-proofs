import Wikipedia.HopfProblem.SheafLerayLowDegreesAbstractHomology
import Wikipedia.HopfProblem.SheafLerayLowDegreesAbstractCoreNaturality
import Wikipedia.HopfProblem.SheafLerayLowDegreesAbstractResolutionMap

/-!
# The genuine low-degree Leray sequence for a cochain complex

If the degree-zero term of a natural-degree cochain complex is
injective, there is an exact sequence
`0 → Ext¹(A,H⁰K) → H¹(Hom(A,K)) → Hom(A,H¹K) → Ext²(A,H⁰K)`.
All terms are Mathlib's native Ext, homology, and morphism groups.
The three arrows come from native cycles and the two actual Ext
connecting maps of the canonical low-degree augmented resolution.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees.Abstract

private theorem first_composite_zero {D : Type*} [Category D] [HasZeroMorphisms D]
    {X B B' H H' : D} (f : X ⟶ B) (g : B ⟶ H) (e : B ≅ B') (d : H ≅ H')
    (hfg : f ≫ g = 0) : (f ≫ e.hom) ≫ (e.inv ≫ g ≫ d.hom) = 0 := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% hfg, zero_comp]

private theorem second_composite_zero {D : Type*} [Category D] [HasZeroMorphisms D]
    {B B' H H' T : D} (f : B ⟶ H) (g : H ⟶ T) (e : B ≅ B') (d : H ≅ H')
    (hfg : f ≫ g = 0) : (e.inv ≫ f ≫ d.hom) ≫ (d.inv ≫ g) = 0 := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc, hfg, comp_zero]

private theorem iso_cancel_comp {D : Type*} [Category D] {B B' H H' : D}
    (f : B ⟶ H) (e : B ≅ B') (d : H ≅ H') :
    e.hom ≫ (e.inv ≫ f ≫ d.hom) = f ≫ d.hom := by
  simp only [Iso.hom_inv_id_assoc]

private theorem iso_cancel_comp_id {D : Type*} [Category D] {H H' T : D}
    (f : H ⟶ T) (d : H ≅ H') : d.hom ≫ (d.inv ≫ f) = f ≫ 𝟙 T := by
  simp only [Iso.hom_inv_id_assoc, Category.comp_id]

universe u

variable {C : Type u} [Category.{0} C] [Abelian C] [HasExt.{0} C]
  (A : C) (K : CochainComplex C ℕ)

/-- The native edge map from evaluated-complex cohomology to homology-valued morphisms. -/
def edgeMap :
    (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).obj K).homology 1 ⟶
      AddCommGrpCat.of (A ⟶ K.homology 1) :=
  (middleIso A K).inv ≫ Core.edgeMap A (resolution K) ≫
    (extZeroHomIso A (K.homology 1)).hom

/-- The transgression is defined by the two genuine native Ext connecting maps. -/
def transgression : AddCommGrpCat.of (A ⟶ K.homology 1) ⟶
    AddCommGrpCat.of (Ext A (K.homology 0) 2) :=
  (extZeroHomIso A (K.homology 1)).inv ≫ Core.transgression A (resolution K)

theorem edgeMap_transgression : edgeMap A K ≫ transgression A K = 0 :=
  second_composite_zero (Core.edgeMap A (resolution K))
    (Core.transgression A (resolution K)) (middleIso A K)
    (extZeroHomIso A (K.homology 1)) (Core.edgeMap_transgression A (resolution K))

/-- The right short complex of the actual low-degree sequence. -/
def secondComplex : ShortComplex AddCommGrpCat :=
  ShortComplex.mk (edgeMap A K) (transgression A K) (edgeMap_transgression A K)

variable [Injective (K.X 0)]

/-- The native degree-one Ext map into evaluated-complex homology. -/
def firstMap : AddCommGrpCat.of (Ext A (K.homology 0) 1) ⟶
    (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).obj K).homology 1 := by
  letI : Injective (resolution K).complex.X₁ := inferInstanceAs (Injective (K.X 0))
  exact Core.firstMap A (resolution K) ≫ (middleIso A K).hom

theorem firstMap_edgeMap : firstMap A K ≫ edgeMap A K = 0 := by
  let : Injective (resolution K).complex.X₁ := inferInstanceAs (Injective (K.X 0))
  exact first_composite_zero (Core.firstMap A (resolution K))
    (Core.edgeMap A (resolution K)) (middleIso A K) (extZeroHomIso A (K.homology 1))
    (Core.firstMap_edgeMap A (resolution K))

/-- The left short complex of the actual low-degree sequence. -/
def firstComplex : ShortComplex AddCommGrpCat :=
  ShortComplex.mk (firstMap A K) (edgeMap A K) (firstMap_edgeMap A K)

instance firstMap_mono : Mono (firstMap A K) := by
  let : Injective (resolution K).complex.X₁ := inferInstanceAs (Injective (K.X 0))
  let : Mono (Core.firstMap A (resolution K)) := Core.firstMap_mono A (resolution K)
  change Mono (Core.firstMap A (resolution K) ≫ (middleIso A K).hom)
  infer_instance

/-- Exactness at the native degree-one evaluated-complex homology group. -/
theorem firstComplex_exact : (firstComplex A K).Exact := by
  let : Injective (resolution K).complex.X₁ := inferInstanceAs (Injective (K.X 0))
  let e : Core.firstComplex A (resolution K) ≅ firstComplex A K :=
    ShortComplex.isoMk (Iso.refl _) (middleIso A K) (extZeroHomIso A (K.homology 1))
      (Category.id_comp _)
      (iso_cancel_comp (Core.edgeMap A (resolution K)) (middleIso A K)
        (extZeroHomIso A (K.homology 1)))
  exact ShortComplex.exact_of_iso e (Core.firstComplex_exact A (resolution K))

/-- Exactness at the native homology-valued morphism group. -/
theorem secondComplex_exact : (secondComplex A K).Exact := by
  let : Injective (resolution K).complex.X₁ := inferInstanceAs (Injective (K.X 0))
  let e : Core.secondComplex A (resolution K) ≅ secondComplex A K :=
    ShortComplex.isoMk (middleIso A K) (extZeroHomIso A (K.homology 1)) (Iso.refl _)
      (iso_cancel_comp (Core.edgeMap A (resolution K)) (middleIso A K)
        (extZeroHomIso A (K.homology 1)))
      (iso_cancel_comp_id (Core.transgression A (resolution K))
        (extZeroHomIso A (K.homology 1)))
  exact ShortComplex.exact_of_iso e (Core.secondComplex_exact A (resolution K))

end Wikipedia.HopfProblem.SheafLerayLowDegrees.Abstract
