import Wikipedia.NoExoticSixSphere.ModTwoBilinearDescent
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainBasic

/-!
# Actual mod-two-valued functionals on the original scalar quotient

Every integral-linear functional into `ZMod 2` kills twice its source.
The original quotient universal map therefore gives a unique functional
on the scalar quotient, with its literal evaluation formula. This is
the coefficient-quotient comparison needed for native homology evaluation.
-/

noncomputable section

namespace NoExoticSixSphere.ModTwoFunctional

open Wikipedia.HopfProblem.SphereHomologyCoefficients

variable (A : Type) [AddCommGroup A] [Module ℤ A]

/-- A genuine mod-two-valued functional kills the actual image of multiplication by two. -/
theorem scalarImage_le_ker (f : A →ₗ[ℤ] ZMod 2) : scalarImage 2 A ≤ LinearMap.ker f := by
  rintro z ⟨a, rfl⟩
  change f ((2 : ℤ) • a) = 0
  rw [two_zsmul, map_add, ← two_mul, show (2 : ZMod 2) = 0 from by decide, zero_mul]

/-- The actual quotient lift of the original functional. -/
def quotientLift (f : A →ₗ[ℤ] ZMod 2) : (A ⧸ scalarImage 2 A) →ₗ[ℤ] ZMod 2 :=
  (QuotientAddGroup.lift (scalarImage 2 A).toAddSubgroup f.toAddMonoidHom
    (fun _ ha => scalarImage_le_ker A f ha)).toIntLinearMap

theorem quotientLift_mk (f : A →ₗ[ℤ] ZMod 2) (a : A) :
    quotientLift A f (Submodule.Quotient.mk a) = f a := rfl

/-- Lifting preserves the original addition and integer scalar operations on functionals. -/
def quotientLiftLinear : (A →ₗ[ℤ] ZMod 2) →ₗ[ℤ] ((A ⧸ scalarImage 2 A) →ₗ[ℤ] ZMod 2) where
  toFun := quotientLift A
  map_add' f g := by
    apply LinearMap.ext
    intro c
    obtain ⟨a, rfl⟩ := (scalarImage 2 A).mkQ_surjective c
    rfl
  map_smul' z f := by
    apply LinearMap.ext
    intro c
    obtain ⟨a, rfl⟩ := (scalarImage 2 A).mkQ_surjective c
    rfl

/-- Literal precomposition supplies a preimage, and quotient generators detect equality. -/
theorem quotientLift_bijective : Function.Bijective (quotientLiftLinear A) := by
  constructor
  · intro f g hfg
    apply LinearMap.ext
    intro a
    exact congrArg (fun h : (A ⧸ scalarImage 2 A) →ₗ[ℤ] ZMod 2 =>
      h (Submodule.Quotient.mk a)) hfg
  · intro g
    let f : A →ₗ[ℤ] ZMod 2 :=
      Wikipedia.HopfProblem.ConstantSheafSingularComparison.addHomToIntLinearMap
        (g.toAddMonoidHom.comp (scalarImage 2 A).mkQ.toAddMonoidHom)
    refine ⟨f, ?_⟩
    apply LinearMap.ext
    intro c
    obtain ⟨a, rfl⟩ := (scalarImage 2 A).mkQ_surjective c
    exact quotientLift_mk A f a

/-- The equivalence retains the original quotient lift as its forward map. -/
def quotientEquiv : (A →ₗ[ℤ] ZMod 2) ≃ₗ[ℤ] ((A ⧸ scalarImage 2 A) →ₗ[ℤ] ZMod 2) :=
  LinearEquiv.ofBijective (quotientLiftLinear A) (quotientLift_bijective A)

theorem quotientEquiv_mk (f : A →ₗ[ℤ] ZMod 2) (a : A) :
    quotientEquiv A f (Submodule.Quotient.mk a) = f a := rfl

variable {H : Type} [AddCommGroup H] [Module ℤ H]

/-- Transport along a specified actual scalar-quotient equivalence. -/
def transportEquiv (e : (A ⧸ scalarImage 2 A) ≃ₗ[ℤ] H) :
    (A →ₗ[ℤ] ZMod 2) ≃ₗ[ℤ] (H →ₗ[ℤ] ZMod 2) :=
  (quotientEquiv A).trans (LinearEquiv.arrowCongr e (LinearEquiv.refl ℤ (ZMod 2)))

theorem transportEquiv_mk (e : (A ⧸ scalarImage 2 A) ≃ₗ[ℤ] H)
    (f : A →ₗ[ℤ] ZMod 2) (a : A) :
    transportEquiv A e f (e (Submodule.Quotient.mk a)) = f a := by
  change quotientEquiv A f (e.symm (e (Submodule.Quotient.mk a))) = f a
  rw [LinearEquiv.symm_apply_apply, quotientEquiv_mk]

end NoExoticSixSphere.ModTwoFunctional
