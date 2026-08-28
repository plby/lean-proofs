import Wikipedia.HopfProblem.SheafHigherDirectImageExt

/-!
# Coefficient naturality of the actual Ext-resolution comparison

The comparison is checked on genuine injective-resolution cocycles.
Native Ext postcomposition and the actual map of Hom complexes carry
each representative to the same postcomposed morphism.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace Wikipedia.HopfProblem.SheafHigherDirectImage.ExtBridge

universe u

variable {C : Type u} [Category.{0} C] [Abelian C] [HasExt.{0} C]
  {F G : C} (I : InjectiveResolution F) (J : InjectiveResolution G)

/-- Naturality in the coefficient object for the integer-indexed
resolution comparison, proved on actual Ext representatives. -/
@[reassoc] theorem extExtendedHomologyIso_hom_coefficient_naturality
    {g : F ⟶ G} (φ : InjectiveResolution.Hom I J g) (A : C) (n : ℕ) :
    ((extFunctor n).obj (op A)).map g ≫ (extExtendedHomologyIso J A n).hom =
      (extExtendedHomologyIso I A n).hom ≫
        HomologicalComplex.homologyMap
          (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).map φ.hom')
          (n : ℤ) := by
  apply AddCommGrpCat.ext
  intro α
  obtain ⟨a, ha, rfl⟩ := I.extMk_surjective α (n + 1) rfl
  have haφ : (a ≫ φ.hom.f n) ≫ J.cocomplex.d n (n + 1) = 0 := by
    simp [reassoc_of% ha]
  have haext := extMk_extended_isCycle I a (n + 1) rfl ha
  have haφext := extMk_extended_isCycle J (a ≫ φ.hom.f n) (n + 1) rfl haφ
  have hrep : (a ≫ (I.cochainComplexXIso n n rfl).inv) ≫ φ.hom'.f n =
      (a ≫ φ.hom.f n) ≫ (J.cochainComplexXIso n n rfl).inv := by
    simp only [φ.hom'_f n n rfl, Category.assoc, Iso.inv_hom_id_assoc]
  change (extExtendedHomologyIso J A n).hom
      ((I.extMk a (n + 1) rfl ha).comp (Ext.mk₀ g) (add_zero n)) =
    HomologicalComplex.homologyMap
      (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).map φ.hom')
      (n : ℤ) ((extExtendedHomologyIso I A n).hom (I.extMk a (n + 1) rfl ha))
  rw [InjectiveResolution.extMk_comp_mk₀ a (n + 1) rfl ha φ,
    extExtendedHomologyIso_hom_extMk J (a ≫ φ.hom.f n) (n + 1) rfl haφ haφext,
    extExtendedHomologyIso_hom_extMk I a (n + 1) rfl ha haext]
  have hc := homologyMap_cycleClass
    (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).map φ.hom')
    (n : ℤ) (a ≫ (I.cochainComplexXIso n n rfl).inv) haext
    (by
      change ((((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj
        J.cochainComplex).sc (n : ℤ)).g
          ((a ≫ (I.cochainComplexXIso n n rfl).inv) ≫ φ.hom'.f n) = 0
      rw [hrep]
      exact haφext)
  change HomologicalComplex.homologyMap
      (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).map φ.hom')
      (n : ℤ)
      (cycleClass (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj
        I.cochainComplex) (n : ℤ) (a ≫ (I.cochainComplexXIso n n rfl).inv) haext) =
    cycleClass (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj
      J.cochainComplex) (n : ℤ)
      ((a ≫ (I.cochainComplexXIso n n rfl).inv) ≫ φ.hom'.f n) _ at hc
  simpa only [hrep] using hc.symm

omit [HasExt C] in
/-- Extension from natural to integer degrees commutes with the
actual lifted coefficient map. -/
@[reassoc] theorem resolutionExtendHomologyIso_hom_coefficient_naturality
    {g : F ⟶ G} (φ : InjectiveResolution.Hom I J g) (A : C) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).map φ.hom')
        (n : ℤ) ≫ (resolutionExtendHomologyIso J A n).hom =
      (resolutionExtendHomologyIso I A n).hom ≫
        HomologicalComplex.homologyMap
          (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).map φ.hom) n :=
  coyonedaExtendHomologyIso_hom_complexMap A φ.hom n

/-- The native Ext-to-Hom-homology isomorphism is natural for a
genuine morphism of injective resolutions. -/
@[reassoc] theorem extHomologyIso_hom_coefficient_naturality
    {g : F ⟶ G} (φ : InjectiveResolution.Hom I J g) (A : C) (n : ℕ) :
    ((extFunctor n).obj (op A)).map g ≫ (extHomologyIso J A n).hom =
      (extHomologyIso I A n).hom ≫
        HomologicalComplex.homologyMap
          (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).map φ.hom) n := by
  apply AddCommGrpCat.ext
  intro α
  have h₁ := ConcreteCategory.congr_hom
    (extExtendedHomologyIso_hom_coefficient_naturality I J φ A n) α
  have h₂ := ConcreteCategory.congr_hom
    (resolutionExtendHomologyIso_hom_coefficient_naturality I J φ A n)
    ((extExtendedHomologyIso I A n).hom α)
  exact (congrArg (resolutionExtendHomologyIso J A n).hom h₁).trans h₂

/-- The same naturality statement for an unbundled complex map with
its literal degree-zero lifting square. -/
@[reassoc] theorem extHomologyIso_hom_coefficient_naturality_of_lift
    (g : F ⟶ G) (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = g ≫ J.ι.f 0) (A : C) (n : ℕ) :
    ((extFunctor n).obj (op A)).map g ≫ (extHomologyIso J A n).hom =
      (extHomologyIso I A n).hom ≫
        HomologicalComplex.homologyMap
          (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).map φ) n :=
  extHomologyIso_hom_coefficient_naturality I J (g := g)
    ⟨φ, hφ.trans (congrArg (fun k : F ⟶ G => k ≫ J.ι.f 0)
      (CochainComplex.single₀_map_f_zero g).symm)⟩ A n

end Wikipedia.HopfProblem.SheafHigherDirectImage.ExtBridge
