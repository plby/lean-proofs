import Wikipedia.HopfProblem.SingularCohomologyCupClasses

/-!
# Integer scaling of the genuine singular cup product

We first prove the bilinear scaling identities with abstract integer modules,
using the same coherent pointwise linear-map module as the actual cup-product
construction. Specializing those identities keeps the categorical cohomology
objects opaque and preserves their original scalar actions.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open PeriodTorusHigherHomology SingularCohomologyFree SingularCohomologyCup

attribute [local instance] integerLinearMapModule

section IntegerBilinear

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [Module ℤ A] [Module ℤ B] [Module ℤ C]

/-- Left integer linearity, with the fixed pointwise integer action on linear maps. -/
theorem integerBilinear_smul_left (f : A →ₗ[ℤ] B →ₗ[ℤ] C)
    (m : ℤ) (a : A) (b : B) : f (m • a) b = m • f a b := by
  simpa only [integerBilinearRightApply_apply] using
    map_zsmul (integerBilinearRightApply f b) m a

/-- Right integer linearity in the specified input and output modules. -/
theorem integerBilinear_smul_right (f : A →ₗ[ℤ] B →ₗ[ℤ] C)
    (n : ℤ) (a : A) (b : B) : f a (n • b) = n • f a b :=
  map_zsmul (f a) n b

/-- Simultaneous scaling of an actual integer-bilinear map. -/
theorem integerBilinear_smul_smul (f : A →ₗ[ℤ] B →ₗ[ℤ] C)
    (m n : ℤ) (a : A) (b : B) :
    f (m • a) (n • b) = (m * n) • f a b := by
  rw [integerBilinear_smul_left, integerBilinear_smul_right]
  exact (mul_zsmul (f a b) m n).symm

end IntegerBilinear

variable (X : Type) [TopologicalSpace X] (p q : ℕ)

/-- Left integer linearity of the actual native Alexander--Whitney cup product. -/
theorem cupProduct_smul_left (m : ℤ)
    (a : SingularCohomology X p) (b : SingularCohomology X q) :
    cupProduct X p q (m • a) b = m • cupProduct X p q a b :=
  integerBilinear_smul_left (cupProduct X p q) m a b

/-- Right integer linearity of the actual native Alexander--Whitney cup product. -/
theorem cupProduct_smul_right (n : ℤ)
    (a : SingularCohomology X p) (b : SingularCohomology X q) :
    cupProduct X p q a (n • b) = n • cupProduct X p q a b :=
  integerBilinear_smul_right (cupProduct X p q) n a b

/-- The genuine native singular cup product scales by the product of the two integers. -/
theorem cupProduct_smul_smul (m n : ℤ)
    (a : SingularCohomology X p) (b : SingularCohomology X q) :
    cupProduct X p q (m • a) (n • b) = (m * n) • cupProduct X p q a b :=
  integerBilinear_smul_smul (cupProduct X p q) m n a b

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
