import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyGodementFunctor
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalars

/-!
# Complex scalar actions and the actual injective presentations

An actual complex scalar action makes every actual stalk divisible as an
abelian group, hence injective. It therefore supplies the constructed
Godement injective presentation without an extra injectivity premise.
The actual additive successor functor carries the scalar action to the
actual cokernel, allowing repeated presentations with the same property.
-/

noncomputable section

open CategoryTheory
open scoped AlgebraicGeometry

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.Godement

open CuspNormalization.SheafCohomology

/-- Division by a nonzero integer in an actual complex module is scalar
multiplication by the reciprocal complex integer. -/
@[instance_reducible] def complexModuleDivisible (A : Type) [AddCommGroup A] [Module ℂ A] :
    DivisibleBy A ℤ where
  div a n := (n : ℂ)⁻¹ • a
  div_zero a := by simp
  div_cancel {n} a hn := by
    rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul, mul_inv_cancel₀ (Int.cast_ne_zero.mpr hn),
      one_smul]

/-- An actual complex scalar action on an abelian group makes that
group injective, by the proved divisibility criterion. -/
theorem injective_of_complexScalarEnd (A : AddCommGrpCat.{0}) (ρ : ℂ →+* End A) :
    Injective A := by
  let := moduleOfScalarEnd A ρ
  let := complexModuleDivisible A
  exact AddCommGrpCat.injective_of_divisible A

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X) (ρ : ℂ →+* End F)

/-- The actual stalk functor carries the actual complex scalar action. -/
def stalkScalarEnd (x : X) : ℂ →+* End (F.presheaf.stalk x) :=
  (mapEndRingHom (CuspNormalization.SheafBiproduct.stalkFunctor X x) F).comp ρ

include ρ

/-- All actual stalk groups of a complex-linear sheaf are injective. -/
theorem stalk_injective_of_scalarEnd (x : X) : Injective (F.presheaf.stalk x) :=
  injective_of_complexScalarEnd (F.presheaf.stalk x) (stalkScalarEnd F ρ x)

/-- The actual Godement presentation with injectivity derived from the
actual scalar action, not supplied as an assumption. -/
def complexPresentation : InjectivePresentation F :=
  presentation F (stalk_injective_of_scalarEnd F ρ)

/-- The actual cokernel retains the scalar action through the proved
additive successor functor. -/
def successorScalarEnd : ℂ →+* End (successor F) :=
  (mapEndRingHom (successorFunctor (X := X)) F).comp ρ

/-- The next actual stalk groups are again injective. -/
theorem successor_stalk_injective (x : X) :
    Injective ((successor F).presheaf.stalk x) :=
  stalk_injective_of_scalarEnd (successor F) (successorScalarEnd F ρ) x

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.Godement
