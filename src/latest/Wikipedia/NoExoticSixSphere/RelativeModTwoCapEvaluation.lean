import Wikipedia.NoExoticSixSphere.ModTwoCapAugmentation
import Wikipedia.NoExoticSixSphere.RelativeModTwoCapDegree
import Wikipedia.NoExoticSixSphere.RelativeModTwoCohomologyEvaluation

/-!
# Actual top cap followed by augmentation is cohomology evaluation

The identity is proved on genuine cycle and cocycle representatives and
descends through their original homology quotients. Coefficient reduction
and cap are the original maps, not maps defined through abstract markings.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RelativeModTwoCap

open ModTwoCapProduct (Coefficient)

variable {X : Type} [TopologicalSpace X] (U : Set X)

/-- Augmenting the original top cap of a reduced integral class is actual evaluation. -/
theorem augmentation_capProduct_reduction (n : ℕ)
    (a : RelativeModTwoCochains.Cohomology U n)
    (c : RelativeSingularHomology.Homology U n) :
    CoefficientChains.augmentation Coefficient X
        (capProductInDegree U (q := 0) (Nat.add_zero n) a
          (RelativeCoefficients.reductionMap 2 U n c)) =
      RelativeModTwoCochains.evaluation U n a c := by
  obtain ⟨α, rfl⟩ :=
    SingularCohomologyFree.cocycleClass_surjective (RelativeModTwoCochains.complex U) n a
  obtain ⟨z, rfl⟩ := ModuleHomology.cycleClass_surjective (RelativeSingularHomology.complex U) n c
  rw [RelativeCoefficients.reductionMap, ModuleHomology.homologyMap_cycleClass,
    capProductInDegree_cocycle_cycle, CoefficientChains.augmentation_cycleClass]
  have hcap := capCyclesInDegree_val U (q := 0) (Nat.add_zero n) α.val
    (RelativeModTwoCochains.cocycle_coboundary_zero U n α)
    (ModuleHomology.mapCycles (RelativeCoefficients.reduction 2 U) n z)
  have hmap := ModuleHomology.mapCycles_val (RelativeCoefficients.reduction 2 U) n z
  apply (congrArg (CoefficientChains.augmentationChain Coefficient X) hcap).trans
  apply (congrArg (fun b => CoefficientChains.augmentationChain Coefficient X
    (capInDegree U (q := 0) (Nat.add_zero n) α.val b)) hmap).trans
  exact (augmentation_cap_reduction U n α.val z.val).trans
    (ModTwoCohomologyEvaluation.evaluation_cocycle_cycle
      (RelativeSingularHomology.complex U) n α z).symm

end NoExoticSixSphere.RelativeModTwoCap
