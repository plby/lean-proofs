import Wikipedia.HopfProblem.SheafCupProductScalarQuotientHomology
import Wikipedia.HopfProblem.SheafCupProductScalars
import Wikipedia.HopfProblem.SheafCupProductNativeBasic

/-!
# Actual scalar quotient maps for the multiplicative Godement complex

The compatible coefficient maps are the original global constants and
their proved germ insertions. Thus the quotient scalar maps and the
two Alexander–Whitney scalar laws below are actual Godement statements,
with no compatibility or cohomology premise left to supply.
-/

noncomputable section

open CategoryTheory Opposite

namespace Wikipedia.HopfProblem.SheafCupProduct.ScalarQuotient

open GodementRing

variable {X : TopCat.{0}} {F : RingSheaf X}

/-- Actual iterated global constants satisfy every original coface compatibility. -/
def globalCoefficients (c : Scalars.Coefficients F) :
    CompatibleCoefficients ℂ (globalData F) where
  c0 := Scalars.coefficients0 c
  c1 := Scalars.coefficients1 c
  c2 := Scalars.coefficients2 c
  c3 := Scalars.coefficients3 c
  face0 i z := congrArg (fun e : Scalars.Coefficients (term1 F) => e z)
    (Scalars.face0_coefficients c i)
  face1 i z := congrArg (fun e : Scalars.Coefficients (term2 F) => e z)
    (Scalars.face1_coefficients c i)
  face2 i z := congrArg (fun e : Scalars.Coefficients (term3 F) => e z)
    (Scalars.face2_coefficients c i)

/-- Original coefficient multiplication on the actual first cocycle group. -/
abbrev cocycleScalarOne (c : Scalars.Coefficients F) (z : ℂ) :=
  (globalCoefficients c).cocycleScalarOne z

/-- Original coefficient multiplication on the actual second cocycle group. -/
abbrev cocycleScalarTwo (c : Scalars.Coefficients F) (z : ℂ) :=
  (globalCoefficients c).cocycleScalarTwo z

@[simp] theorem cocycleScalarOne_coe (c : Scalars.Coefficients F) (z : ℂ)
    (a : (globalData F).CocycleOne) :
    ((cocycleScalarOne c z a).val : (term1 F).presheaf.obj (op ⊤)) =
      @Mul.mul ((term1 F).presheaf.obj (op ⊤)) inferInstance
        (Scalars.coefficients1 c z) a.val := rfl

@[simp] theorem cocycleScalarTwo_coe (c : Scalars.Coefficients F) (z : ℂ)
    (a : (globalData F).CocycleTwo) :
    ((cocycleScalarTwo c z a).val : (term2 F).presheaf.obj (op ⊤)) =
      @Mul.mul ((term2 F).presheaf.obj (op ⊤)) inferInstance
        (Scalars.coefficients2 c z) a.val := rfl

/-- Actual multiplication descended to the actual first Godement quotient. -/
abbrev scalarOne (c : Scalars.Coefficients F) (z : ℂ) :
    (globalData F).CohomologyOne →+ (globalData F).CohomologyOne :=
  (globalCoefficients c).scalarOne z

/-- Actual multiplication descended to the actual second Godement quotient. -/
abbrev scalarTwo (c : Scalars.Coefficients F) (z : ℂ) :
    (globalData F).CohomologyTwo →+ (globalData F).CohomologyTwo :=
  (globalCoefficients c).scalarTwo z

@[simp] theorem scalarOne_class (c : Scalars.Coefficients F) (z : ℂ)
    (a : (globalData F).CocycleOne) :
    scalarOne c z ((globalData F).classOne a) =
      (globalData F).classOne (cocycleScalarOne c z a) := rfl

@[simp] theorem scalarTwo_class (c : Scalars.Coefficients F) (z : ℂ)
    (a : (globalData F).CocycleTwo) :
    scalarTwo c z ((globalData F).classTwo a) =
      (globalData F).classTwo (cocycleScalarTwo c z a) := rfl

/-- Actual Godement quotient cup products are scalar-linear in the first variable. -/
theorem cup_scalar_left (c : Scalars.Coefficients F) (z : ℂ)
    (a b : (globalData F).CohomologyOne) :
    (globalData F).cup (scalarOne c z a) b = scalarTwo c z ((globalData F).cup a b) :=
  (globalCoefficients c).cup_scalar_left z a b

/-- Actual Godement quotient cup products are scalar-linear in the second variable. -/
theorem cup_scalar_right (c : Scalars.Coefficients F) (z : ℂ)
    (a b : (globalData F).CohomologyOne) :
    (globalData F).cup a (scalarOne c z b) = scalarTwo c z ((globalData F).cup a b) :=
  (globalCoefficients c).cup_scalar_right z a b

end Wikipedia.HopfProblem.SheafCupProduct.ScalarQuotient
