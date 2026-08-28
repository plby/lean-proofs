import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageStalkNaturalityCohomologySections
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageStalkNaturalityCohomologyPushforward
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageStalkNaturalityCohomologyComponents
import Wikipedia.HopfProblem.SheafHigherDirectImageCohomology
import Wikipedia.HopfProblem.SheafLerayLowDegreesPushforwardNaturalityExt

/-!
# Coefficient naturality of the original resolution cohomology presheaf

An actual map of injective resolutions lifting the coefficient morphism
commutes with the original Ext-to-resolution comparison on every open.
The same square survives literal presheaf pushforward. All maps remain
the native Ext coefficient maps and the actual homology maps of the
given resolution morphism.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkNaturality

open SheafHigherDirectImage HolomorphicSheafCohomology.OpenRestriction

private theorem compose_squares {C : Type*} [Category C]
    {A₁ A₂ B₁ B₂ C₁ C₂ : C}
    (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂) (g₁ : B₁ ⟶ C₁) (g₂ : B₂ ⟶ C₂)
    (a : A₁ ⟶ A₂) (b : B₁ ⟶ B₂) (c : C₁ ⟶ C₂)
    (hf : a ≫ f₂ = f₁ ≫ b) (hg : b ≫ g₂ = g₁ ≫ c) :
    a ≫ (f₂ ≫ g₂) = (f₁ ≫ g₁) ≫ c :=
  (Category.assoc a f₂ g₂).symm.trans
    ((congrArg (fun k => k ≫ g₂) hf).trans
      ((Category.assoc f₁ b g₂).trans
        ((congrArg (fun k => f₁ ≫ k) hg).trans (Category.assoc f₁ g₁ c).symm)))

variable {X Y : TopCat.{0}} {F G : AbelianSheaf X}
  (I : InjectiveResolution F) (J : InjectiveResolution G)
  (g : F ⟶ G) (φ : I.cocomplex ⟶ J.cocomplex)
  (hφ : I.ι.f 0 ≫ φ.f 0 = g ≫ J.ι.f 0)

include hφ

/-- Coefficient naturality of the original resolution cohomology
presheaf comparison for a literal lift of the coefficient map. -/
@[reassoc] theorem resolutionCohomologyPresheafIso_hom_naturality_of_lift (n : ℕ) :
    (CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology X) n).map g ≫
      (resolutionCohomologyPresheafIso J n).hom =
    (resolutionCohomologyPresheafIso I n).hom ≫
      HomologicalComplex.homologyMap
        (((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex _).map φ) n := by
  apply NatTrans.ext
  funext U
  cases U with
  | op U =>
    simp only [NatTrans.comp_app, resolutionCohomologyPresheafIso_hom_app,
      cohomologyPresheafFunctor_map_app]
    exact compose_squares _ _ _ _ _ _ _
      (ExtBridge.extHomologyIso_hom_coefficient_naturality_of_lift I J g φ hφ (freeOpen U) n)
      (homSectionsHomologyIso_hom_naturality_complex φ U n)

/-- The inverse of the same original comparison is coefficient-natural
for the actual homology map, without defining that map by transport. -/
@[reassoc] theorem resolutionCohomologyPresheafIso_inv_naturality_of_lift (n : ℕ) :
    HomologicalComplex.homologyMap
        (((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex _).map φ) n ≫
      (resolutionCohomologyPresheafIso J n).inv =
    (resolutionCohomologyPresheafIso I n).inv ≫
      (CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology X) n).map g := by
  apply (Iso.eq_inv_comp (resolutionCohomologyPresheafIso I n)).mpr
  rw [← Category.assoc,
    ← resolutionCohomologyPresheafIso_hom_naturality_of_lift I J g φ hφ n,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable (f : X ⟶ Y)

/-- The original pushed-resolution comparison commutes with actual
coefficient maps and the actual lifted resolution homology map. -/
@[reassoc] theorem pushedResolutionCohomologyPresheafIso_hom_naturality_of_lift (n : ℕ) :
    HomologicalComplex.homologyMap
        (((TopCat.Sheaf.forget AddCommGrpCat Y).mapHomologicalComplex _).map
          (((pushforward f).mapHomologicalComplex _).map φ)) n ≫
      (pushedResolutionCohomologyPresheafIso f J n).hom =
    (pushedResolutionCohomologyPresheafIso f I n).hom ≫
      Functor.whiskerLeft (Opens.map f).op
        ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
          (Opens.grothendieckTopology X) n).map g) := by
  let P := presheafPushforward f
  let m := HomologicalComplex.homologyMap
    (((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex _).map φ) n
  let q := HomologicalComplex.homologyMap
    (((TopCat.Sheaf.forget AddCommGrpCat Y).mapHomologicalComplex _).map
      (((pushforward f).mapHomologicalComplex _).map φ)) n
  let a := (CategoryTheory.Sheaf.cohomologyPresheafFunctor
    (Opens.grothendieckTopology X) n).map g
  let eI := homologyPresheafPushforwardIso f I.cocomplex n
  let eJ := homologyPresheafPushforwardIso f J.cocomplex n
  let rI := resolutionCohomologyPresheafIso I n
  let rJ := resolutionCohomologyPresheafIso J n
  have h₁ : q ≫ eJ.hom = eI.hom ≫ P.map m :=
    homologyPresheafPushforwardIso_hom_naturality_complex f φ n
  have h₂ : P.map m ≫ P.map rJ.inv = P.map rI.inv ≫ P.map a :=
    (P.map_comp m rJ.inv).symm.trans
      ((congrArg P.map
        (resolutionCohomologyPresheafIso_inv_naturality_of_lift I J g φ hφ n)).trans
        (P.map_comp rI.inv a))
  change q ≫ (eJ.hom ≫ P.map rJ.inv) = (eI.hom ≫ P.map rI.inv) ≫ P.map a
  exact compose_squares _ _ _ _ _ _ _ h₁ h₂

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkNaturality
