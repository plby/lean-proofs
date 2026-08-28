import Wikipedia.HopfProblem.SheafSingularCupComparisonRowGlobalOriginal
import Wikipedia.HopfProblem.SheafSingularCupComparisonRowGlobalUnit

/-!
# The ring-unit quotient maps are the original global cochain comparison

The original native cochain comparison, followed by the original
forgotten-ring window isomorphisms, acts on each cocycle by the actual
ring unit. Surjectivity of the canonical cycle projections then proves
equality of the original native homology maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.RowGlobal

open RingCochains ConstantSheafSingularComparison

variable (X : TopCat.{0})

/-- Original first singular cocycles, mapped through the original global comparison. -/
def originalOneCocycleMap : Singular.Cocycle X ℂ 1 →+ (globalData X).CocycleOne :=
  (Singular.shortCocycleMap (oneOriginalWindowIso X).inv).comp
    ((Singular.shortCocycleMap (originalOneWindow X).hom).comp
      (Singular.shortCocycleMap
        ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{0} (ComplexShape.up ℕ) 1).map
          (globalCochainComparison X (AddCommGrpCat.of ℂ)))))

/-- Original second singular cocycles, mapped through the original global comparison. -/
def originalTwoCocycleMap : Singular.Cocycle X ℂ 2 →+ (globalData X).CocycleTwo :=
  (Singular.shortCocycleMap (twoOriginalWindowIso X).inv).comp
    ((Singular.shortCocycleMap (originalTwoWindow X).hom).comp
      (Singular.shortCocycleMap
        ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{0} (ComplexShape.up ℕ) 2).map
          (globalCochainComparison X (AddCommGrpCat.of ℂ)))))

@[simp] theorem originalOneCocycleMap_val (a : Singular.Cocycle X ℂ 1) :
    (originalOneCocycleMap X a).val =
      (forgetSheafIso X 1).inv.hom.app (op ⊤)
        (globalCochainUnit X (AddCommGrpCat.of ℂ) 1 a.val) := rfl

@[simp] theorem originalTwoCocycleMap_val (a : Singular.Cocycle X ℂ 2) :
    (originalTwoCocycleMap X a).val =
      (forgetSheafIso X 2).inv.hom.app (op ⊤)
        (globalCochainUnit X (AddCommGrpCat.of ℂ) 2 a.val) := rfl

/-- The original first cocycle comparison is precisely the actual ring-unit map. -/
theorem originalOneCocycleMap_eq_unit (a : Singular.Cocycle X ℂ 1) :
    originalOneCocycleMap X a =
      (globalUnitMorphism X).cocycleOneMap (Singular.oneCocycleEvaluation X ℂ a) := by
  apply Subtype.ext
  exact evaluation_unit_forget_inv X 1 a.val

/-- The original second cocycle comparison is precisely the actual ring-unit map. -/
theorem originalTwoCocycleMap_eq_unit (a : Singular.Cocycle X ℂ 2) :
    originalTwoCocycleMap X a =
      (globalUnitMorphism X).cocycleTwoMap (Singular.twoCocycleEvaluation X ℂ a) := by
  apply Subtype.ext
  exact evaluation_unit_forget_inv X 2 a.val

/-- Canonical first classes follow the original cochain map in original row coordinates. -/
theorem originalOne_homology_class (a : Singular.Cocycle X ℂ 1) :
    (oneOriginalIso X).inv
        (HomologicalComplex.homologyMap
          (globalCochainComparison X (AddCommGrpCat.of ℂ)) 1
            (Singular.classMap X ℂ 1 a)) =
      Singular.shortClass (oneComplex X) (originalOneCocycleMap X a) := by
  change ShortComplex.homologyMap (oneOriginalWindowIso X).inv
    (ShortComplex.homologyMap (originalOneWindow X).hom
      (ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{0} (ComplexShape.up ℕ) 1).map
          (globalCochainComparison X (AddCommGrpCat.of ℂ))) (Singular.shortClass _ a))) = _
  rw [Singular.shortClass_naturality, Singular.shortClass_naturality,
    Singular.shortClass_naturality]
  rfl

/-- Canonical second classes follow the original cochain map in original row coordinates. -/
theorem originalTwo_homology_class (a : Singular.Cocycle X ℂ 2) :
    (twoOriginalIso X).inv
        (HomologicalComplex.homologyMap
          (globalCochainComparison X (AddCommGrpCat.of ℂ)) 2
            (Singular.classMap X ℂ 2 a)) =
      Singular.shortClass (twoComplex X) (originalTwoCocycleMap X a) := by
  change ShortComplex.homologyMap (twoOriginalWindowIso X).inv
    (ShortComplex.homologyMap (originalTwoWindow X).hom
      (ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{0} (ComplexShape.up ℕ) 2).map
          (globalCochainComparison X (AddCommGrpCat.of ℂ))) (Singular.shortClass _ a))) = _
  rw [Singular.shortClass_naturality, Singular.shortClass_naturality,
    Singular.shortClass_naturality]
  rfl

/-- Exact equality with the original native degree-one global-cochain comparison. -/
theorem unitOne_original :
    HomologicalComplex.homologyMap (globalCochainComparison X (AddCommGrpCat.of ℂ)) 1 ≫
        (oneOriginalIso X).inv ≫ (oneHomologyIso X).hom =
      AddCommGrpCat.ofHom (unitOne X) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Singular.classMap_surjective X ℂ 1 a
  change oneHomologyEquiv X ((oneOriginalIso X).inv
    (HomologicalComplex.homologyMap (globalCochainComparison X (AddCommGrpCat.of ℂ)) 1
      (Singular.classMap X ℂ 1 a))) = unitOne X (Singular.classMap X ℂ 1 a)
  rw [originalOne_homology_class, oneHomologyEquiv_class, unitOne_class,
    originalOneCocycleMap_eq_unit]

/-- Exact equality with the original native degree-two global-cochain comparison. -/
theorem unitTwo_original :
    HomologicalComplex.homologyMap (globalCochainComparison X (AddCommGrpCat.of ℂ)) 2 ≫
        (twoOriginalIso X).inv ≫ (twoHomologyIso X).hom =
      AddCommGrpCat.ofHom (unitTwo X) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Singular.classMap_surjective X ℂ 2 a
  change twoHomologyEquiv X ((twoOriginalIso X).inv
    (HomologicalComplex.homologyMap (globalCochainComparison X (AddCommGrpCat.of ℂ)) 2
      (Singular.classMap X ℂ 2 a))) = unitTwo X (Singular.classMap X ℂ 2 a)
  rw [originalTwo_homology_class, twoHomologyEquiv_class, unitTwo_class,
    originalTwoCocycleMap_eq_unit]

end Wikipedia.HopfProblem.SheafSingularCupComparison.RowGlobal
