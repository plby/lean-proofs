import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardExact
import Wikipedia.HopfProblem.CuspNormalizationSheafEvaluationSheaf

/-!
# Actual scalar actions on holomorphic direct images and skyscrapers

The direct-image action is the direct image of pointwise multiplication.
The skyscraper action is the skyscraper functor applied to multiplication
on its actual complex coefficient group.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution

open SheafCohomology SheafEvaluation

attribute [local instance] Classical.propDecidable

section DirectImage

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {B : Type} [TopologicalSpace B]

/-- The actual pushforward of the holomorphic pointwise scalar action. -/
def pushedScalarEnd (p : TopCat.of M ⟶ TopCat.of B) :
    ℂ →+* End (pushedHolomorphicSheaf I p) :=
  (mapEndRingHom (TopCat.Sheaf.pushforward AddCommGrpCat p)
    (HolomorphicFunctionSheaf.additiveSheaf I M)).comp (holomorphicScalarEnd I M)

@[simp] theorem pushedScalarEnd_apply (p : TopCat.of M ⟶ TopCat.of B)
    (c : ℂ) (U : Opens B)
    (s : HolomorphicFunctionSheaf.Section I M ((Opens.map p).obj U)) :
    (pushedScalarEnd I p c).hom.app (op U) s = c • s := rfl

end DirectImage

section Skyscraper

variable {X : TopCat.{0}} (b : X)

/-- The actual skyscraper functor map acts by its coefficient map on neighborhoods. -/
theorem skyscraperMap_app {A D : AddCommGrpCat.{0}} (f : A ⟶ D)
    (U : Opens X) (hb : b ∈ U) :
    ((skyscraperSheafFunctor (C := AddCommGrpCat.{0}) b).map f).hom.app (op U) ≫
        (skyscraperSectionIso b D U hb).hom =
      (skyscraperSectionIso b A U hb).hom ≫ f := by
  classical
  change (SkyscraperPresheafFunctor.map' b f).app (op U) ≫
      (skyscraperSectionIso b D U hb).hom = _
  dsimp only [SkyscraperPresheafFunctor.map', skyscraperSectionIso, eqToIso,
    skyscraper, skyscraperSheaf, skyscraperPresheaf]
  rw [dif_pos hb]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- Multiplication on the actual skyscraper coefficient group. -/
def skyscraperScalarEnd : ℂ →+* End (skyscraper b (AddCommGrpCat.of ℂ)) := by
  classical
  letI : (skyscraperSheafFunctor (C := AddCommGrpCat.{0}) b).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact (mapEndRingHom (skyscraperSheafFunctor (C := AddCommGrpCat.{0}) b)
    (AddCommGrpCat.of ℂ)).comp (ModuleCat.of ℂ ℂ).smul

/-- On every neighborhood of the support, the action is literal complex multiplication. -/
theorem skyscraperScalarEnd_app (c : ℂ) (U : Opens X) (hb : b ∈ U) :
    (skyscraperScalarEnd b c).hom.app (op U) ≫
        (skyscraperSectionIso b (AddCommGrpCat.of ℂ) U hb).hom =
      (skyscraperSectionIso b (AddCommGrpCat.of ℂ) U hb).hom ≫
        (ModuleCat.of ℂ ℂ).smul c :=
  skyscraperMap_app b ((ModuleCat.of ℂ ℂ).smul c) U hb

theorem skyscraperScalarEnd_apply (c : ℂ) (U : Opens X) (hb : b ∈ U)
    (s : (skyscraper b (AddCommGrpCat.of ℂ)).presheaf.obj (op U)) :
    (skyscraperSectionIso b (AddCommGrpCat.of ℂ) U hb).hom
        ((skyscraperScalarEnd b c).hom.app (op U) s) =
      c • (skyscraperSectionIso b (AddCommGrpCat.of ℂ) U hb).hom s :=
  ConcreteCategory.congr_hom (skyscraperScalarEnd_app b c U hb) s

end Skyscraper

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution
