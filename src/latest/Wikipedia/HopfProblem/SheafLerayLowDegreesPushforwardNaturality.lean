import Wikipedia.HopfProblem.SheafLerayLowDegreesPushforwardNaturalityExt
import Wikipedia.HopfProblem.SheafLerayLowDegreesPushforward

/-!
# Naturality of source cohomology in the Leray complex comparison

For a genuine coefficient morphism and any actual lift to the chosen
injective resolutions, source sheaf-cohomology maps agree with the
induced maps on the pushed-forward Hom complexes.  This applies in
particular to scalar endomorphisms of the coefficient sheaf.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees

open SheafHigherDirectImage
open CuspNormalization.SheafCohomologyFinitePushforward (integerSheaf)

variable {X Y : TopCat.{0}} (p : X ⟶ Y)

/-- The global-Hom homology comparison commutes with actual complex maps. -/
@[reassoc] theorem globalHomComplexHomologyIso_hom_naturality
    {K L : CochainComplex (AbelianSheaf X) ℕ} (φ : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op (integerSheaf X))).mapHomologicalComplex _).map φ) n ≫
      (globalHomComplexHomologyIso p L n).hom =
    (globalHomComplexHomologyIso p K n).hom ≫
      HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op (integerSheaf Y))).mapHomologicalComplex _).map
          (((pushforward p).mapHomologicalComplex _).map φ)) n := by
  have h := congrArg
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n).map)
    (globalHomComplexIso_hom_naturality p φ)
  simp only [Functor.map_comp] at h
  exact h

/-- Actual source cohomology maps agree with the maps of the genuine
pushed-forward resolution complexes, for every continuous base map. -/
@[reassoc] theorem sourceCohomologyIso_hom_naturality
    {F G : AbelianSheaf X} (I : InjectiveResolution F) (J : InjectiveResolution G)
    (g : F ⟶ G) (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = g ≫ J.ι.f 0) (n : ℕ) :
    AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map g n) ≫
      (sourceCohomologyIso p G J n).hom =
    (sourceCohomologyIso p F I n).hom ≫
      HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op (integerSheaf Y))).mapHomologicalComplex _).map
          (((pushforward p).mapHomologicalComplex _).map φ)) n := by
  apply AddCommGrpCat.ext
  intro α
  have h₁ := ConcreteCategory.congr_hom
    (ExtBridge.extHomologyIso_hom_coefficient_naturality_of_lift I J g φ hφ
      (integerSheaf X) n) α
  have h₂ := ConcreteCategory.congr_hom
    (globalHomComplexHomologyIso_hom_naturality p φ n)
    ((ExtBridge.extHomologyIso I (integerSheaf X) n).hom α)
  exact (congrArg (globalHomComplexHomologyIso p J.cocomplex n).hom h₁).trans h₂

end Wikipedia.HopfProblem.SheafLerayLowDegrees
