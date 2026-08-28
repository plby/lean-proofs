import Wikipedia.HopfProblem.SheafCupProductNativeLinear

/-!
# Bilinearity for an already identified original scalar action

This adapter uses an equality of actual scalar sheaf endomorphisms.
It keeps the existing module structures induced by those endomorphisms,
and its underlying pairing is definitionally the original native cup.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafCupProduct

open GodementRing

variable {X : TopCat.{0}} {F : RingSheaf X}
  (c : Scalars.Coefficients F) (ρ : ℂ →+* End ((forgetSheaf X).obj F))
  (hρ : Scalars.scalarEnd c = ρ)

include hρ

theorem cup_scalar_left_of_eq (z : ℂ) (a b : H F 1) :
    cup F ρ (CategoryTheory.Sheaf.H.map (ρ z).asHom 1 a) b =
      CategoryTheory.Sheaf.H.map (ρ z).asHom 2 (cup F ρ a b) := by
  subst ρ
  exact cup_scalar_left c z a b

theorem cup_scalar_right_of_eq (z : ℂ) (a b : H F 1) :
    cup F ρ a (CategoryTheory.Sheaf.H.map (ρ z).asHom 1 b) =
      CategoryTheory.Sheaf.H.map (ρ z).asHom 2 (cup F ρ a b) := by
  subst ρ
  exact cup_scalar_right c z a b

/-- The actual native cup, complex-bilinear for an identified original
scalar action of the sheaf itself. -/
def linearCupOfScalarEnd :
    letI := CuspNormalization.SheafCohomology.cohomologyModule ((forgetSheaf X).obj F) ρ 1
    letI := CuspNormalization.SheafCohomology.cohomologyModule ((forgetSheaf X).obj F) ρ 2
    H F 1 →ₗ[ℂ] H F 1 →ₗ[ℂ] H F 2 := by
  letI := CuspNormalization.SheafCohomology.cohomologyModule ((forgetSheaf X).obj F) ρ 1
  letI := CuspNormalization.SheafCohomology.cohomologyModule ((forgetSheaf X).obj F) ρ 2
  exact pairingLinear (cup F ρ)
    (cup_scalar_left_of_eq c ρ hρ) (cup_scalar_right_of_eq c ρ hρ)

@[simp] theorem linearCupOfScalarEnd_apply (a b : H F 1) :
    linearCupOfScalarEnd c ρ hρ a b = cup F ρ a b := rfl

end Wikipedia.HopfProblem.SheafCupProduct
