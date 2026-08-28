import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Ring.Basic

/-!
# The actual complex scalar maps on the additive coefficient group

Each scalar acts by literal left multiplication on the original additive
group of complex numbers. The resulting coefficient endomorphisms form
the actual scalar action before applying any sheaf or cohomology functor.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.OriginalConstants

/-- Literal multiplication by a complex scalar on the additive coefficient group. -/
def complexScalarCoefficient (z : ℂ) : AddCommGrpCat.of ℂ ⟶ AddCommGrpCat.of ℂ :=
  AddCommGrpCat.ofHom (AddMonoidHom.mulLeft z)

@[simp]
theorem complexScalarCoefficient_apply (z c : ℂ) : complexScalarCoefficient z c = z * c := rfl

/-- The original coefficient multiplication, bundled as its endomorphism action. -/
def complexScalarCoefficientEnd : ℂ →+* End (AddCommGrpCat.of ℂ) where
  toFun := complexScalarCoefficient
  map_one' := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext fun c => one_mul c
  map_mul' z w := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext fun c => mul_assoc z w c
  map_zero' := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext fun c => zero_mul c
  map_add' z w := by
    apply AddCommGrpCat.hom_ext
    exact AddMonoidHom.ext fun c => add_mul z w c

@[simp]
theorem complexScalarCoefficientEnd_asHom (z : ℂ) :
    (complexScalarCoefficientEnd z).asHom = complexScalarCoefficient z := rfl

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.OriginalConstants
