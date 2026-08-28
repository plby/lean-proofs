import Wikipedia.HopfProblem.SheafSingularCupComparisonRowGlobalBasic
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonGlobalComplex
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowExtCokernel

/-!
# Original global additive cochains in the actual ring-row coordinates

The window maps are the original forgotten-ring sheaf isomorphisms,
evaluated on the top open set. The unit identities retain the original
global singular-cochain unit in every degree.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.RowGlobal

open CuspNormalization.SheafCohomologyResolution
open ResolutionRow RingCochains ConstantSheafSingularComparison

variable (X : TopCat.{0})

/-- The actual first row window, compared with the original global additive cochains. -/
def oneOriginalWindowIso : oneComplex X ≅
    (globalSheafCochainComplex X (AddCommGrpCat.of ℂ)).sc' 0 1 2 :=
  (globalSectionsFunctor X).mapShortComplex.mapIso (rowOneIso X)

/-- The actual second row window, compared with the original global additive cochains. -/
def twoOriginalWindowIso : twoComplex X ≅
    (globalSheafCochainComplex X (AddCommGrpCat.of ℂ)).sc' 1 2 3 :=
  (globalSectionsFunctor X).mapShortComplex.mapIso (rowTwoIso X)

/-- The original standard degree-one indexing isomorphism, with no altered cochains. -/
def originalOneWindow :
    (globalSheafCochainComplex X (AddCommGrpCat.of ℂ)).sc 1 ≅
      (globalSheafCochainComplex X (AddCommGrpCat.of ℂ)).sc' 0 1 2 :=
  (globalSheafCochainComplex X (AddCommGrpCat.of ℂ)).isoSc' 0 1 2
    ((ComplexShape.up ℕ).prev_eq' (by rfl)) ((ComplexShape.up ℕ).next_eq' (by rfl))

/-- The original standard degree-two indexing isomorphism, with no altered cochains. -/
def originalTwoWindow :
    (globalSheafCochainComplex X (AddCommGrpCat.of ℂ)).sc 2 ≅
      (globalSheafCochainComplex X (AddCommGrpCat.of ℂ)).sc' 1 2 3 :=
  (globalSheafCochainComplex X (AddCommGrpCat.of ℂ)).isoSc' 1 2 3
    ((ComplexShape.up ℕ).prev_eq' (by rfl)) ((ComplexShape.up ℕ).next_eq' (by rfl))

/-- The original row-to-additive comparison on actual first global cohomology. -/
def oneOriginalIso : (oneComplex X).homology ≅
    (globalSheafCochainComplex X (AddCommGrpCat.of ℂ)).homology 1 :=
  ShortComplex.homologyMapIso (oneOriginalWindowIso X) ≪≫
    (ShortComplex.homologyMapIso (originalOneWindow X)).symm

/-- The original row-to-additive comparison on actual second global cohomology. -/
def twoOriginalIso : (twoComplex X).homology ≅
    (globalSheafCochainComplex X (AddCommGrpCat.of ℂ)).homology 2 :=
  ShortComplex.homologyMapIso (twoOriginalWindowIso X) ≪≫
    (LowExt.CycleCokernel.windowHomologyIso₂
      (globalSheafCochainComplex X (AddCommGrpCat.of ℂ))).symm

theorem oneOriginalIso_inv : (oneOriginalIso X).inv =
    ShortComplex.homologyMap (originalOneWindow X).hom ≫
      ShortComplex.homologyMap (oneOriginalWindowIso X).inv := rfl

theorem twoOriginalIso_inv : (twoOriginalIso X).inv =
    ShortComplex.homologyMap (originalTwoWindow X).hom ≫
      ShortComplex.homologyMap (twoOriginalWindowIso X).inv := by
  change (𝟙 _ ≫ ShortComplex.homologyMap (originalTwoWindow X).hom) ≫
    ShortComplex.homologyMap (twoOriginalWindowIso X).inv = _
  rw [Category.id_comp]

/-- Evaluation followed by the genuine ring unit recovers the original additive unit. -/
theorem evaluation_unit_forget (n : ℕ) (a : Cochains X (AddCommGrpCat.of ℂ) n) :
    (forgetSheafIso X n).hom.hom.app (op ⊤)
        (globalUnit X n (Singular.evaluation X ℂ n a)) =
      globalCochainUnit X (AddCommGrpCat.of ℂ) n a := by
  have he : cochainFromValues X (AddCommGrpCat.of ℂ) n
      (Singular.evaluation X ℂ n a) = a :=
    (Singular.evaluation X ℂ n).symm_apply_apply a
  exact (globalUnit_additive X n (Singular.evaluation X ℂ n a)).trans
    (congrArg (globalCochainUnit X (AddCommGrpCat.of ℂ) n) he)

/-- The same identity in actual forgotten-ring global coordinates. -/
theorem evaluation_unit_forget_inv (n : ℕ) (a : Cochains X (AddCommGrpCat.of ℂ) n) :
    (forgetSheafIso X n).inv.hom.app (op ⊤)
        (globalCochainUnit X (AddCommGrpCat.of ℂ) n a) =
      globalUnit X n (Singular.evaluation X ℂ n a) := by
  let e := (globalSectionsFunctor X).mapIso (forgetSheafIso X n)
  exact (congrArg e.inv (evaluation_unit_forget X n a)).symm.trans
    (ConcreteCategory.congr_hom e.hom_inv_id _)

/-- The original global unit is retained as an equality of its actual degree maps. -/
theorem evaluation_unit_forget_map (n : ℕ) :
    (Singular.evaluationIso X ℂ n).hom ≫
        AddCommGrpCat.ofHom (globalUnit X n).toAddMonoidHom ≫
          (globalSectionsFunctor X).map (forgetSheafIso X n).hom =
      globalCochainUnit X (AddCommGrpCat.of ℂ) n := by
  ext a
  exact evaluation_unit_forget X n a

end Wikipedia.HopfProblem.SheafSingularCupComparison.RowGlobal
