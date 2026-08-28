import Wikipedia.NoExoticSixSphere.CoefficientHomologyZero
import Wikipedia.NoExoticSixSphere.CoefficientChainChange
import Wikipedia.NoExoticSixSphere.ModTwoCapUnit
import Wikipedia.NoExoticSixSphere.RelativeModTwoCapChains

/-!
# Augmentation of the original top-degree cap chain

After native coefficient reduction, the augmentation of the capped
zero-chain is exactly the original cochain value. The relative formula
uses the original coefficient-change square and actual quotient maps.
These are identities on chains before any homology descent.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem FirstHurewicz SphereHomologyCoefficients SingularCohomologyCup

namespace NoExoticSixSphere.ModTwoCapProduct

variable {X : Type} [TopologicalSpace X]

/-- On every original simplex, augmented top cap is the literal cochain value. -/
theorem augmentation_cap_reduction_simplex (n : ℕ) (α : Cochain X n)
    (σ : SingularSimplex X n) :
    CoefficientChains.augmentationChain Coefficient X
        (capInDegree (q := 0) (Nat.add_zero n) α
          (((reductionChainMap 2 X).f n).hom (simplexChain X n σ))) =
      α (simplexChain X n σ) := by
  rw [CoefficientChains.reduction_simplex]
  have he := capInDegree_simplex (p := n) (q := 0) (Nat.add_zero n) α σ 1
  apply (congrArg (CoefficientChains.augmentationChain Coefficient X) he).trans
  rw [CoefficientChains.augmentationChain_simplex, windowFace_full,
    ContinuousMap.comp_id, mul_one]

/-- The original augmentation-cap identity holds on every integral chain. -/
theorem augmentation_cap_reduction (n : ℕ) (α : Cochain X n) (c : Chains X n) :
    CoefficientChains.augmentationChain Coefficient X
        (capInDegree (q := 0) (Nat.add_zero n) α (((reductionChainMap 2 X).f n).hom c)) = α c := by
  have he : (CoefficientChains.augmentationChain Coefficient X).comp
      ((capInDegree (q := 0) (Nat.add_zero n) α).comp ((reductionChainMap 2 X).f n).hom) =
    ConstantSheafSingularComparison.addHomToIntLinearMap α := by
    apply chainMap_ext X n
    intro σ
    exact augmentation_cap_reduction_simplex n α σ
  exact LinearMap.congr_fun he c

end NoExoticSixSphere.ModTwoCapProduct

namespace NoExoticSixSphere.RelativeModTwoCap

open ModTwoCapProduct (Coefficient)

variable {X : Type} [TopologicalSpace X] (U : Set X)

/-- The actual relative quotient and coefficient reduction retain the same cap evaluation. -/
theorem augmentation_cap_reduction (n : ℕ) (α : RelativeModTwoCochains.Cochain U n)
    (c : (RelativeSingularHomology.complex U).X n) :
    CoefficientChains.augmentationChain Coefficient X
        (capInDegree U (q := 0) (Nat.add_zero n) α
          (((RelativeCoefficients.reduction 2 U).f n).hom c)) = α c := by
  obtain ⟨b, rfl⟩ := RelativeCoefficients.quotientMap_surjective (ModuleCat.of ℤ ℤ) U n c
  have he := congrArg (fun f => (f.f n).hom b)
    (RelativeCoefficients.projection_change (reductionCoefficient 2) U)
  change ((RelativeCoefficients.reduction 2 U).f n).hom
      (RelativeCoefficients.quotientMap (ModuleCat.of ℤ ℤ) U n b) =
    RelativeCoefficients.quotientMap Coefficient U n (((reductionChainMap 2 X).f n).hom b) at he
  rw [he, capInDegree_quotientMap]
  exact ModTwoCapProduct.augmentation_cap_reduction n (RelativeModTwoCochains.toAbsolute U n α) b

end NoExoticSixSphere.RelativeModTwoCap
