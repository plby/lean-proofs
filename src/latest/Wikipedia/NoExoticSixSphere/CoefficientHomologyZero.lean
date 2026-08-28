import Wikipedia.NoExoticSixSphere.CoefficientChainPresentation
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainBasic
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleConnectingCycles
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

/-!
# Actual augmentation on native coefficient zero-chains

Every zero-chain is an actual cycle. The original singular homology
augmentation sends each native simplex summand to its coefficient, so
on every chain it is the sum of its coefficients. In a path-connected
space this same augmentation is the actual degree-zero homology isomorphism.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem FirstHurewicz SphereHomologyCoefficients
  SingularMayerVietoris ModuleHomology

namespace NoExoticSixSphere.CoefficientChains

variable (A : ModuleCat.{0} ℤ) (X : Type) [TopologicalSpace X]

/-- The original degree-zero cycle with the specified native coefficient chain. -/
def zeroCycles : Chains A X 0 →ₗ[ℤ] Cycle (coefficientComplex A X) 0 :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    { toFun := fun c => mkCycle (coefficientComplex A X) 0 c
        (congrArg (fun f => f.hom c) ((coefficientComplex A X).shape 0 0 (by simp)))
      map_zero' := Subtype.ext rfl
      map_add' _ _ := Subtype.ext rfl }

theorem zeroCycles_val (c : Chains A X 0) : (zeroCycles A X c).val = c := rfl

/-- The actual class of a native zero-chain. -/
def zeroClass : Chains A X 0 →ₗ[ℤ] (coefficientComplex A X).homology 0 :=
  (cycleClass (coefficientComplex A X) 0).comp (zeroCycles A X)

/-- The original singular homology augmentation with this coefficient object. -/
abbrev augmentation : (coefficientComplex A X).homology 0 →ₗ[ℤ] A :=
  ((TopCat.of X).singularHomology₀ε A).hom

/-- Sum the coefficients of the original zero-simplex summands. -/
def augmentationChain : Chains A X 0 →ₗ[ℤ] A := lift A X 0 (fun _ => LinearMap.id)

theorem augmentationChain_simplex (σ : SingularSimplex X 0) (a : A) :
    augmentationChain A X (simplex A X 0 σ a) = a :=
  lift_simplex A X 0 (fun _ => LinearMap.id) σ a

theorem simplexZero_boundary (σ : SingularSimplex X 0) :
    (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := A) (simplexIndex X 0 σ) ≫
      (coefficientComplex A X).d 0 0 = 0 := by
  rw [(coefficientComplex A X).shape 0 0 (by simp)]
  exact CategoryTheory.Limits.comp_zero

/-- The original categorical cycle lift of a native zero-simplex summand. -/
def simplexZeroCycleLift (σ : SingularSimplex X 0) : A ⟶ (coefficientComplex A X).cycles 0 :=
  (coefficientComplex A X).liftCycles
    ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := A) (simplexIndex X 0 σ))
    0 (by simp) (simplexZero_boundary A X σ)

theorem zeroClass_simplex_eq_lift (σ : SingularSimplex X 0) (a : A) :
    zeroClass A X (simplex A X 0 σ a) =
      ((coefficientComplex A X).homologyπ 0).hom ((simplexZeroCycleLift A X σ).hom a) := by
  rw [zeroClass, LinearMap.comp_apply, cycleClass_eq_homologyClassOfCycle, homologyClassOfCycle]
  apply congrArg ((coefficientComplex A X).homologyπ 0).hom
  apply (ModuleCat.mono_iff_injective ((coefficientComplex A X).iCycles 0)).mp inferInstance
  have h₁ := (coefficientComplex A X).i_cyclesMk
    (zeroCycles A X (simplex A X 0 σ a)).val (0 - 1) (next_nat 0)
    (cycle_condition (coefficientComplex A X) 0 (zeroCycles A X (simplex A X 0 σ a)))
  have h₂ := congrArg (fun f => f.hom a)
    ((coefficientComplex A X).liftCycles_i
      ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := A) (simplexIndex X 0 σ))
      0 (by simp) (simplexZero_boundary A X σ))
  exact h₁.trans h₂.symm

/-- Native augmentation sends every actual zero-simplex summand to its original coefficient. -/
theorem augmentation_zeroClass_simplex (σ : SingularSimplex X 0) (a : A) :
    augmentation A X (zeroClass A X (simplex A X 0 σ a)) = a := by
  rw [zeroClass_simplex_eq_lift]
  exact congrArg (fun f => f.hom a)
    ((TopCat.toSSet.obj (TopCat.of X)).liftCycles_ιChainComplex_homologyπ_homology₀ε
      A (simplexIndex X 0 σ))

/-- The original augmentation on a zero-chain class is its actual coefficient sum. -/
theorem augmentation_zeroClass (c : Chains A X 0) :
    augmentation A X (zeroClass A X c) = augmentationChain A X c := by
  have he : (augmentation A X).comp (zeroClass A X) = augmentationChain A X := by
    apply map_ext A X 0
    intro σ a
    exact (augmentation_zeroClass_simplex A X σ a).trans
      (augmentationChain_simplex A X σ a).symm
  exact LinearMap.congr_fun he c

theorem augmentation_cycleClass (z : Cycle (coefficientComplex A X) 0) :
    augmentation A X (cycleClass (coefficientComplex A X) 0 z) =
      augmentationChain A X z.val := by
  have hz : zeroCycles A X z.val = z := Subtype.ext rfl
  exact (congrArg (fun w => augmentation A X (cycleClass (coefficientComplex A X) 0 w))
    hz).symm.trans (augmentation_zeroClass A X z.val)

/-- The actual augmentation is an isomorphism on a path-connected space. -/
def connectedZeroEquiv [PathConnectedSpace X] : (coefficientComplex A X).homology 0 ≃ₗ[ℤ] A :=
  (asIso ((TopCat.of X).singularHomology₀ε A)).toLinearEquiv

theorem connectedZeroEquiv_toLinearMap [PathConnectedSpace X] :
    (connectedZeroEquiv A X).toLinearMap = augmentation A X := rfl

end NoExoticSixSphere.CoefficientChains
