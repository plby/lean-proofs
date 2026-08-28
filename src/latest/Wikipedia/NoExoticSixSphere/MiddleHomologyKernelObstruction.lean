import Wikipedia.NoExoticSixSphere.CoefficientKernelObstruction
import Wikipedia.NoExoticSixSphere.ZeroSecondHomologyEvaluation

/-!
# The coefficient obstruction for the original middle homology map

For a continuous map from a space with zero integral second homology,
the original coefficient sequence constructs the exact kernel-lifting
obstruction. Its half-image is in the original target third homology.
No connectivity, freeness, or absence of torsion is required of the target.
In particular this applies to the actual, possibly disconnected boundary.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris SphereHomologyCoefficients

namespace NoExoticSixSphere.MiddleKernelCoefficients

attribute [local instance] Submodule.Quotient.module

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [Subsingleton (SingularHomology X 2)] (j : C(X, Y))

abbrev Indeterminacy : Submodule ℤ (SingularHomology Y 3) :=
  CoefficientKernelLifting.halfIndeterminacy (singularHomologyMap j 3)

def obstruction : LinearMap.ker (modHomologyMap 2 j 3) →ₗ[ℤ]
    SingularHomology Y 3 ⧸ Indeterminacy j :=
  CoefficientKernelLifting.obstruction (reductionHomologyMap 2 X 3)
    (scalarImage_eq_reduction_ker 2 (by decide) X 3).symm (singularHomologyMap j 3)
    (reductionHomologyMap 2 Y 3) (scalarImage_eq_reduction_ker 2 (by decide) Y 3).symm
    (modHomologyMap 2 j 3) (modHomologyMap_reduction 2 j 3)
    (ZeroSecondHomologyEvaluation.reduction_surjective X)

theorem kernel_iff_has_half (v : ModHomology 2 X 3) :
    modHomologyMap 2 j 3 v = 0 ↔
      ∃ a : SingularHomology X 3, ∃ b : SingularHomology Y 3,
        reductionHomologyMap 2 X 3 a = v ∧ singularHomologyMap j 3 a = (2 : ℤ) • b :=
  CoefficientKernelLifting.mod_kernel_iff_has_half (reductionHomologyMap 2 X 3)
    (singularHomologyMap j 3) (reductionHomologyMap 2 Y 3)
    (scalarImage_eq_reduction_ker 2 (by decide) Y 3).symm (modHomologyMap 2 j 3)
    (modHomologyMap_reduction 2 j 3) (ZeroSecondHomologyEvaluation.reduction_surjective X) v

theorem obstruction_eq (v : LinearMap.ker (modHomologyMap 2 j 3))
    (a : SingularHomology X 3) (b : SingularHomology Y 3)
    (ha : reductionHomologyMap 2 X 3 a = v.val)
    (hb : singularHomologyMap j 3 a = (2 : ℤ) • b) :
    obstruction j v = Submodule.Quotient.mk b :=
  CoefficientKernelLifting.obstruction_eq _ _ _ _ _ _ _ _ v a b ha hb

theorem obstruction_zero_iff (v : LinearMap.ker (modHomologyMap 2 j 3)) :
    obstruction j v = 0 ↔ ∃ a : SingularHomology X 3,
      singularHomologyMap j 3 a = 0 ∧ reductionHomologyMap 2 X 3 a = v.val :=
  CoefficientKernelLifting.obstruction_zero_iff _ _ _ _ _ _ _ _ v

theorem obstruction_twice (v : LinearMap.ker (modHomologyMap 2 j 3)) :
    (2 : ℤ) • obstruction j v = 0 :=
  CoefficientKernelLifting.obstruction_twice _ _ _ _ _ _ _ _ v

def integralKernelReduction : LinearMap.ker (singularHomologyMap j 3) →ₗ[ℤ]
    LinearMap.ker (modHomologyMap 2 j 3) :=
  CoefficientKernelLifting.integralKernelReduction (reductionHomologyMap 2 X 3)
    (singularHomologyMap j 3) (reductionHomologyMap 2 Y 3) (modHomologyMap 2 j 3)
    (modHomologyMap_reduction 2 j 3)

omit [Subsingleton (SingularHomology X 2)] in
theorem integralKernelReduction_val (a : LinearMap.ker (singularHomologyMap j 3)) :
    (integralKernelReduction j a).val = reductionHomologyMap 2 X 3 a := rfl

theorem obstruction_ker : LinearMap.ker (obstruction j) =
    LinearMap.range (integralKernelReduction j) :=
  CoefficientKernelLifting.obstruction_ker _ _ _ _ _ _ _ _

end NoExoticSixSphere.MiddleKernelCoefficients
