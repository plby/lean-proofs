import Wikipedia.HopfProblem.SheafHigherDirectImagePresheaf

/-!
# Naturality of the original presheaf pushforward homology comparison

Literal presheaf pushforward is exact. Its existing homology comparison
commutes with every actual map of the underlying sheaf complexes.
The maps on both sides are the original homology and inverse-open-set
presheaf maps.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkNaturality

open SheafHigherDirectImage

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

/-- The original pushforward comparison is natural for actual sheaf
complex maps, with literal whiskering on the source homology presheaf. -/
@[reassoc] theorem homologyPresheafPushforwardIso_hom_naturality_complex
    {K L : CochainComplex (AbelianSheaf X) ℕ} (φ : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((TopCat.Sheaf.forget AddCommGrpCat Y).mapHomologicalComplex _).map
          (((pushforward f).mapHomologicalComplex _).map φ)) n ≫
      (homologyPresheafPushforwardIso f L n).hom =
    (homologyPresheafPushforwardIso f K n).hom ≫
      Functor.whiskerLeft (Opens.map f).op
        (HomologicalComplex.homologyMap
          (((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex _).map φ) n) :=
  mapComplexHomologyIso_hom_naturality
    (((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex _).map φ)
    (presheafPushforward f) n

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.StalkNaturality
