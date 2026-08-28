import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackSheafGlobal
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCoefficientGlobal

/-!
# Continuous pullback commutes with original coefficient changes

These squares involve the actual native constant-sheaf coefficient map,
the actual sheafification of singular-cochain postcomposition, and the
original global-section complexes. They follow from the original raw
pullback square and the native sheafification unit, with no restriction
on the abelian coefficient homomorphism or continuous map.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackSheaf

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {A B : AddCommGrpCat.{0}}

/-- Constant raw pullback commutes with the actual constant-presheaf
map of arbitrary coefficient groups. -/
theorem rawConstantPullback_coefficient (α : A ⟶ B) :
    constantPresheafCoefficientMap Y α ≫ rawConstantPullback f B =
      rawConstantPullback f A ≫ (TopCat.Presheaf.pushforward AddCommGrpCat f).map
        (constantPresheafCoefficientMap X α) := by
  apply NatTrans.ext
  funext U
  change α ≫ 𝟙 B = 𝟙 A ≫ α
  rw [Category.comp_id, Category.id_comp]

/-- Actual constant-sheaf pullback commutes with Mathlib's original
constant-sheaf map of coefficient groups. -/
@[reassoc]
theorem constantPullback_coefficient (α : A ⟶ B) :
    constantPullback f A ≫ (TopCat.Sheaf.pushforward AddCommGrpCat f).map
        ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X)
          AddCommGrpCat.{0}).map α) =
      (CategoryTheory.constantSheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{0}).map α ≫ constantPullback f B :=
  (sheafifyPullback_naturality f (constantPresheafCoefficientMap Y α)
    (constantPresheafCoefficientMap X α) (rawConstantPullback f A)
    (rawConstantPullback f B) (rawConstantPullback_coefficient f α)).symm

/-- The actual cochain-sheaf pullback commutes with the original
sheafified coefficient postcomposition in every degree. -/
@[reassoc]
theorem cochainPullback_coefficient (α : A ⟶ B) (n : ℕ) :
    cochainPullback f A n ≫ (TopCat.Sheaf.pushforward AddCommGrpCat f).map
        (sheafCoefficientMap X α n) =
      sheafCoefficientMap Y α n ≫ cochainPullback f B n :=
  (sheafifyPullback_naturality f (presheafCoefficientMap Y α n)
    (presheafCoefficientMap X α n) (rawPullback f A n) (rawPullback f B n)
    (rawPullback_coefficient f α n).symm).symm

/-- Coefficient changes commute with the actual map of sheaf cochain
complexes, before taking any global sections or cohomology. -/
theorem cochainPullbackComplex_coefficient (α : A ⟶ B) :
    cochainPullbackComplex f A ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat f).mapHomologicalComplex (.up ℕ)).map
          (sheafCoefficientComplexMap X α) =
      sheafCoefficientComplexMap Y α ≫ cochainPullbackComplex f B := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact cochainPullback_coefficient f α n

/-- The actual global-section pullback commutes with the original
global coefficient map of cochain complexes. -/
theorem globalSheafPullback_coefficient (α : A ⟶ B) :
    globalSheafPullback f A ≫ globalSheafCoefficientMap X α =
      globalSheafCoefficientMap Y α ≫ globalSheafPullback f B := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact NatTrans.congr_app
    (congrArg (fun θ : cochainSheaf Y A n ⟶
        (TopCat.Sheaf.pushforward AddCommGrpCat f).obj (cochainSheaf X B n) => θ.hom)
      (cochainPullback_coefficient f α n)) (op ⊤)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackSheaf
