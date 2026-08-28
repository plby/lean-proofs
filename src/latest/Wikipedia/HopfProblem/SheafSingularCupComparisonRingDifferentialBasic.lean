import Wikipedia.HopfProblem.SheafSingularCupComparisonRingSheaf
import Wikipedia.HopfProblem.SheafSingularCupComparisonSingularComplex

/-!
# The actual alternating singular-coface differentials

The low-degree differentials are literal alternating sums of the actual
ring cofaces after forgetting multiplication. On presheaves their
comparison with the original singular-chain differential is proved by
evaluation on the original simplex generators.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.RingCochains

open ConstantSheafSingularComparison
open CuspNormalization.SheafForgetStalk (forgetToAdd)

variable (X : TopCat.{0})

def presheafD0 : presheaf X 0 ⋙ forgetToAdd ⟶ presheaf X 1 ⋙ forgetToAdd :=
  Functor.whiskerRight (cofacePresheaf X 0 0) forgetToAdd -
    Functor.whiskerRight (cofacePresheaf X 0 1) forgetToAdd

def presheafD1 : presheaf X 1 ⋙ forgetToAdd ⟶ presheaf X 2 ⋙ forgetToAdd :=
  Functor.whiskerRight (cofacePresheaf X 1 0) forgetToAdd -
    Functor.whiskerRight (cofacePresheaf X 1 1) forgetToAdd +
      Functor.whiskerRight (cofacePresheaf X 1 2) forgetToAdd

def presheafD2 : presheaf X 2 ⋙ forgetToAdd ⟶ presheaf X 3 ⋙ forgetToAdd :=
  Functor.whiskerRight (cofacePresheaf X 2 0) forgetToAdd -
    Functor.whiskerRight (cofacePresheaf X 2 1) forgetToAdd +
      Functor.whiskerRight (cofacePresheaf X 2 2) forgetToAdd -
        Functor.whiskerRight (cofacePresheaf X 2 3) forgetToAdd

@[reassoc] theorem presheafD0_additive :
    presheafD0 X ≫ (presheafAddIso X 1).hom =
      (presheafAddIso X 0).hom ≫ presheafDifferential X (AddCommGrpCat.of ℂ) 0 1 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  change Singular.Values U.unop ℂ 0 at a
  apply (Singular.evaluation U.unop ℂ 1).injective
  change Singular.evaluation U.unop ℂ 1
      ((Singular.evaluation U.unop ℂ 1).symm ((Singular.cofaceData U.unop ℂ).d0 a)) =
    Singular.evaluation U.unop ℂ 1
      ((singularCochainComplex U.unop (AddCommGrpCat.of ℂ)).d 0 1
        ((Singular.evaluation U.unop ℂ 0).symm a))
  rw [Singular.evaluation_d0, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

@[reassoc] theorem presheafD1_additive :
    presheafD1 X ≫ (presheafAddIso X 2).hom =
      (presheafAddIso X 1).hom ≫ presheafDifferential X (AddCommGrpCat.of ℂ) 1 2 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  change Singular.Values U.unop ℂ 1 at a
  apply (Singular.evaluation U.unop ℂ 2).injective
  change Singular.evaluation U.unop ℂ 2
      ((Singular.evaluation U.unop ℂ 2).symm ((Singular.cofaceData U.unop ℂ).d1 a)) =
    Singular.evaluation U.unop ℂ 2
      ((singularCochainComplex U.unop (AddCommGrpCat.of ℂ)).d 1 2
        ((Singular.evaluation U.unop ℂ 1).symm a))
  rw [Singular.evaluation_d1, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

@[reassoc] theorem presheafD2_additive :
    presheafD2 X ≫ (presheafAddIso X 3).hom =
      (presheafAddIso X 2).hom ≫ presheafDifferential X (AddCommGrpCat.of ℂ) 2 3 := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  change Singular.Values U.unop ℂ 2 at a
  apply (Singular.evaluation U.unop ℂ 3).injective
  change Singular.evaluation U.unop ℂ 3
      ((Singular.evaluation U.unop ℂ 3).symm ((Singular.cofaceData U.unop ℂ).d2 a)) =
    Singular.evaluation U.unop ℂ 3
      ((singularCochainComplex U.unop (AddCommGrpCat.of ℂ)).d 2 3
        ((Singular.evaluation U.unop ℂ 2).symm a))
  rw [Singular.evaluation_d2, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- The literal first alternating differential of the actual ring sheaves. -/
def d0 : (forgetSheaf X).obj (sheaf X 0) ⟶ (forgetSheaf X).obj (sheaf X 1) :=
  (forgetSheaf X).map (coface X 0 0) - (forgetSheaf X).map (coface X 0 1)

/-- The literal second alternating differential of the actual ring sheaves. -/
def d1 : (forgetSheaf X).obj (sheaf X 1) ⟶ (forgetSheaf X).obj (sheaf X 2) :=
  (forgetSheaf X).map (coface X 1 0) - (forgetSheaf X).map (coface X 1 1) +
    (forgetSheaf X).map (coface X 1 2)

/-- The literal third alternating differential of the actual ring sheaves. -/
def d2 : (forgetSheaf X).obj (sheaf X 2) ⟶ (forgetSheaf X).obj (sheaf X 3) :=
  (forgetSheaf X).map (coface X 2 0) - (forgetSheaf X).map (coface X 2 1) +
    (forgetSheaf X).map (coface X 2 2) - (forgetSheaf X).map (coface X 2 3)

@[simp] theorem d0_app (U : Opens X) (a : (sheaf X 0).obj.obj (op U)) :
    (d0 X).hom.app (op U) a = (sectionData X U).d0 a := rfl

@[simp] theorem d1_app (U : Opens X) (a : (sheaf X 1).obj.obj (op U)) :
    (d1 X).hom.app (op U) a = (sectionData X U).d1 a := rfl

@[simp] theorem d2_app (U : Opens X) (a : (sheaf X 2).obj.obj (op U)) :
    (d2 X).hom.app (op U) a = (sectionData X U).d2 a := rfl

end Wikipedia.HopfProblem.SheafSingularCupComparison.RingCochains
