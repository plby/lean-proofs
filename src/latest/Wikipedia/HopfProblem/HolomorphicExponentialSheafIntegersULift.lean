import Wikipedia.HopfProblem.HolomorphicExponentialSheafIntegersBasic

/-!
# The native universe-lifted integer constant sheaf

The integer source used by mathlib's sheaf-cohomology definition is the
native constant sheaf on `ULift ℤ`. Applying the constant-sheaf functor
to the usual additive `ULift` equivalence gives its canonical comparison
with the actual integer sheaf used by the exponential sequence.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicExponentialSheaf

/-- The literal constant sheaf on `ULift ℤ`, as used by sheaf cohomology. -/
abbrev integerULiftSheaf (X : TopCat.{0}) : IntegerAdditiveSheaf X :=
  (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
    (AddCommGrpCat.of (ULift.{0} ℤ))

/-- The actual sheafification unit for the lifted constant presheaf. -/
def integerULiftUnit (X : TopCat.{0}) :
    (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{0} ℤ)) ⟶
      (integerULiftSheaf X).obj :=
  CategoryTheory.toSheafify (Opens.grothendieckTopology X) _

/-- The comparison is the native constant-sheaf functor applied to the
usual additive equivalence, rather than a replacement constant object. -/
def integerSheafULiftIso (X : TopCat.{0}) :
    integerSheaf X ≅ integerULiftSheaf X :=
  ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).mapIso
    ((AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).toAddCommGrpIso)).symm

@[simp] theorem integerSheafULiftIso_hom_app_unit
    (X : TopCat.{0}) (U : Opens X) (n : ℤ) :
    (integerSheafULiftIso X).hom.hom.app (op U) ((integerUnit X).app (op U) n) =
      (integerULiftUnit X).app (op U) (ULift.up n) := by
  let η := (Functor.const (Opens X)ᵒᵖ).map
    ((AddEquiv.toAddCommGrpIso (X := AddCommGrpCat.of (ULift.{0} ℤ))
      (Y := AddCommGrpCat.of ℤ) AddEquiv.ulift).inv)
  exact (ConcreteCategory.congr_hom
    (NatTrans.congr_app (CategoryTheory.toSheafify_naturality
      (Opens.grothendieckTopology X) η) (op U)) n).symm

@[simp] theorem integerSheafULiftIso_inv_app_unit
    (X : TopCat.{0}) (U : Opens X) (n : ULift.{0} ℤ) :
    (integerSheafULiftIso X).inv.hom.app (op U) ((integerULiftUnit X).app (op U) n) =
      (integerUnit X).app (op U) n.down := by
  let η := (Functor.const (Opens X)ᵒᵖ).map
    ((AddEquiv.toAddCommGrpIso (X := AddCommGrpCat.of (ULift.{0} ℤ))
      (Y := AddCommGrpCat.of ℤ) AddEquiv.ulift).hom)
  exact (ConcreteCategory.congr_hom
    (NatTrans.congr_app (CategoryTheory.toSheafify_naturality
      (Opens.grothendieckTopology X) η) (op U)) n).symm

end Wikipedia.HopfProblem.HolomorphicExponentialSheaf
