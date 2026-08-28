import Wikipedia.HopfProblem.SphereHomologyCoefficientsSequence
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.Module.ZMod

/-!
# Descent of an integral mod-two-valued bilinear form

An actual integral bilinear map into `ZMod 2` kills twice the source in
each variable. Quotient lifting therefore descends it to the scalar
quotient in both variables. The evaluation formula retains the original
map. On actual `ZMod 2` modules, additivity gives the compatible scalar
linearity without changing the underlying function.
-/

noncomputable section

namespace NoExoticSixSphere.ModTwoBilinear

open Wikipedia.HopfProblem.SphereHomologyCoefficients

variable {A D : Type} [AddCommGroup A] [Module ℤ A] [AddCommGroup D] [Module ℤ D]

theorem scalarImage_le_ker (B : A →ₗ[ℤ] D →ₗ[ℤ] ZMod 2) :
    scalarImage 2 A ≤ LinearMap.ker B := by
  rintro z ⟨a, rfl⟩
  change B ((2 : ℤ) • a) = 0
  rw [two_zsmul, B.map_add]
  ext d
  change B a d + B a d = 0
  rw [← two_mul, show (2 : ZMod 2) = 0 from by decide, zero_mul]

def quotientLeft (B : A →ₗ[ℤ] A →ₗ[ℤ] ZMod 2) :
    (A ⧸ scalarImage 2 A) →ₗ[ℤ] A →ₗ[ℤ] ZMod 2 :=
  (QuotientAddGroup.lift (scalarImage 2 A).toAddSubgroup B.toAddMonoidHom
    (fun _ ha ↦ scalarImage_le_ker B ha)).toIntLinearMap

def quotientForm (B : A →ₗ[ℤ] A →ₗ[ℤ] ZMod 2) :
    (A ⧸ scalarImage 2 A) →ₗ[ℤ] (A ⧸ scalarImage 2 A) →ₗ[ℤ] ZMod 2 :=
  (QuotientAddGroup.lift (scalarImage 2 A).toAddSubgroup (quotientLeft B).flip.toAddMonoidHom
    (fun _ ha ↦ scalarImage_le_ker (quotientLeft B).flip ha)).toIntLinearMap.flip

theorem quotientForm_mk (B : A →ₗ[ℤ] A →ₗ[ℤ] ZMod 2) (a b : A) :
    quotientForm B (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = B a b := rfl

variable [Module (ZMod 2) A]

def scalarUpgradeLeft (B : A →ₗ[ℤ] A →ₗ[ℤ] ZMod 2) (a : A) : A →ₗ[ZMod 2] ZMod 2 :=
  (B a).toAddMonoidHom.toZModLinearMap 2

def scalarUpgrade (B : A →ₗ[ℤ] A →ₗ[ℤ] ZMod 2) : A →ₗ[ZMod 2] A →ₗ[ZMod 2] ZMod 2 :=
  ({ toFun := scalarUpgradeLeft B
     map_zero' := by
       ext a
       exact LinearMap.congr_fun B.map_zero a
     map_add' a b := by
       ext c
       exact LinearMap.congr_fun (B.map_add a b) c } :
    A →+ (A →ₗ[ZMod 2] ZMod 2)).toZModLinearMap 2

theorem scalarUpgrade_apply (B : A →ₗ[ℤ] A →ₗ[ℤ] ZMod 2) (a b : A) :
    scalarUpgrade B a b = B a b := rfl

end NoExoticSixSphere.ModTwoBilinear
