import Wikipedia.HopfProblem.SheafCupProductNativeScalarsComparison
import Wikipedia.HopfProblem.SheafCupProductCohomologyScalars
import Wikipedia.HopfProblem.SheafCupProductTransportScalars

/-!
# The native cup product is complex-bilinear for the original scalars

Actual scalar multiplication on Godement cochains satisfies the two
Alexander--Whitney scalar identities.  The genuine Ext comparisons
retain the scalar endomorphisms of the original sheaf, so these become
bilinearity of the native cup product for its original module structures.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafCupProduct

open GodementRing

variable {X : TopCat.{0}} {F : RingSheaf X} (c : Scalars.Coefficients F)

/-- The original scalar sheaf map can be applied to either the first
input or the resulting native degree-two cup class. -/
theorem cup_scalar_left (z : ℂ) (a b : H F 1) :
    cup F (Scalars.scalarEnd c)
        (CategoryTheory.Sheaf.H.map (Scalars.scalarEnd c z).asHom 1 a) b =
      CategoryTheory.Sheaf.H.map (Scalars.scalarEnd c z).asHom 2
        (cup F (Scalars.scalarEnd c) a b) :=
  transportPairing_scalar_left
    (h1CofaceEquiv F (Scalars.scalarEnd c)) (h2CofaceEquiv F (Scalars.scalarEnd c))
    (globalData F).cup (ScalarQuotient.scalarOne c z) (ScalarQuotient.scalarTwo c z)
    (CategoryTheory.Sheaf.H.map (Scalars.scalarEnd c z).asHom 1)
    (CategoryTheory.Sheaf.H.map (Scalars.scalarEnd c z).asHom 2)
    (h1CofaceEquiv_scalar c z) (h2CofaceEquiv_scalar c z)
    (ScalarQuotient.cup_scalar_left c z) a b

/-- The original scalar sheaf map also acts through the second input. -/
theorem cup_scalar_right (z : ℂ) (a b : H F 1) :
    cup F (Scalars.scalarEnd c) a
        (CategoryTheory.Sheaf.H.map (Scalars.scalarEnd c z).asHom 1 b) =
      CategoryTheory.Sheaf.H.map (Scalars.scalarEnd c z).asHom 2
        (cup F (Scalars.scalarEnd c) a b) :=
  transportPairing_scalar_right
    (h1CofaceEquiv F (Scalars.scalarEnd c)) (h2CofaceEquiv F (Scalars.scalarEnd c))
    (globalData F).cup (ScalarQuotient.scalarOne c z) (ScalarQuotient.scalarTwo c z)
    (CategoryTheory.Sheaf.H.map (Scalars.scalarEnd c z).asHom 1)
    (CategoryTheory.Sheaf.H.map (Scalars.scalarEnd c z).asHom 2)
    (h1CofaceEquiv_scalar c z) (h2CofaceEquiv_scalar c z)
    (ScalarQuotient.cup_scalar_right c z) a b

theorem cup_smul_left (z : ℂ) (a b : H F 1) :
    letI := Scalars.cohomologyModule c 1
    letI := Scalars.cohomologyModule c 2
    cup F (Scalars.scalarEnd c) (z • a) b = z • cup F (Scalars.scalarEnd c) a b :=
  cup_scalar_left c z a b

theorem cup_smul_right (z : ℂ) (a b : H F 1) :
    letI := Scalars.cohomologyModule c 1
    letI := Scalars.cohomologyModule c 2
    cup F (Scalars.scalarEnd c) a (z • b) = z • cup F (Scalars.scalarEnd c) a b :=
  cup_scalar_right c z a b

/-- The same actual native product, bundled as a complex-bilinear map. -/
def linearCup :
    letI := Scalars.cohomologyModule c 1
    letI := Scalars.cohomologyModule c 2
    H F 1 →ₗ[ℂ] H F 1 →ₗ[ℂ] H F 2 := by
  letI := Scalars.cohomologyModule c 1
  letI := Scalars.cohomologyModule c 2
  exact pairingLinear (cup F (Scalars.scalarEnd c)) (cup_smul_left c) (cup_smul_right c)

@[simp] theorem linearCup_apply (a b : H F 1) :
    linearCup c a b = cup F (Scalars.scalarEnd c) a b := rfl

theorem linearCup_self (a : H F 1) : linearCup c a a = 0 :=
  cup_self_eq_zero F (Scalars.scalarEnd c) a

theorem linearCup_skew (a b : H F 1) : linearCup c a b = -linearCup c b a :=
  cup_skew_comm F (Scalars.scalarEnd c) a b

end Wikipedia.HopfProblem.SheafCupProduct
