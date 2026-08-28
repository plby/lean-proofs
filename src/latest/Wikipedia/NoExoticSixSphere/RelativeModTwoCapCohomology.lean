import Wikipedia.NoExoticSixSphere.RelativeModTwoCapCochainExact
import Wikipedia.HopfProblem.SingularCohomologyCupDescent

/-!
# Cap on the original relative cohomology and homology

The factorization on relative chains descends through both genuine
cycle quotients. The result takes values in absolute homology, retaining
the original front/back cap chain on representatives.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RelativeModTwoCap

open ModTwoCapProduct (Coefficient)
open RelativeModTwoCochains (Cochain Cocycle Cohomology complex cocycle_coboundary_zero)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule

variable {X : Type} [TopologicalSpace X] (U : Set X)

/-- Cap varies linearly with the original relative cocycle. -/
def capCocycles (p q : ℕ) : Cocycle U p →ₗ[ℤ]
    ((RelativeCoefficients.complex Coefficient U).homology (p + q) →ₗ[ℤ] ModHomology 2 X q) :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    { toFun := fun α => homologyCap U p q α.val (cocycle_coboundary_zero U p α)
      map_zero' := homologyCap_zero U p q _
      map_add' α β := homologyCap_add U p q α.val β.val _ _ _ }

theorem capCocycles_apply (p q : ℕ) (α : Cocycle U p) :
    capCocycles U p q α = homologyCap U p q α.val (cocycle_coboundary_zero U p α) := rfl

/-- All actual incoming coboundaries act trivially, also in degree zero. -/
theorem capCocycles_coboundary (p q : ℕ) (β : (complex U).X (p - 1)) :
    capCocycles U p q (SingularCohomologyFree.coboundaryCocycle (complex U) p β) = 0 := by
  cases p with
  | zero =>
      have he : SingularCohomologyFree.coboundaryCocycle (complex U) 0 β = 0 := by
        apply Subtype.ext
        change ((complex U).d 0 0).hom β = 0
        rw [(complex U).shape 0 0 (by simp)]
        rfl
      rw [he, map_zero]
  | succ p =>
      exact homologyCap_coboundary U p q β

/-- The genuine relative cap product with values in absolute homology. -/
def capProduct (p q : ℕ) : Cohomology U p →ₗ[ℤ]
    ((RelativeCoefficients.complex Coefficient U).homology (p + q) →ₗ[ℤ] ModHomology 2 X q) :=
  SingularCohomologyCup.cohomologyDesc (complex U) p (capCocycles U p q)
    (capCocycles_coboundary U p q)

theorem capProduct_cocycleClass (p q : ℕ) (α : Cocycle U p) :
    capProduct U p q (SingularCohomologyFree.cocycleClass (complex U) p α) =
      homologyCap U p q α.val (cocycle_coboundary_zero U p α) :=
  SingularCohomologyCup.cohomologyDesc_cocycleClass (complex U) p
    (capCocycles U p q) (capCocycles_coboundary U p q) α

/-- Both actual representatives retain the original relative-chain cap formula. -/
theorem capProduct_cocycle_cycle (p q : ℕ) (α : Cocycle U p)
    (c : ModuleHomology.Cycle (RelativeCoefficients.complex Coefficient U) (p + q)) :
    capProduct U p q (SingularCohomologyFree.cocycleClass (complex U) p α)
        (ModuleHomology.cycleClass (RelativeCoefficients.complex Coefficient U) (p + q) c) =
      ModuleHomology.cycleClass (modComplex 2 X) q
        (capCycles U p q α.val (cocycle_coboundary_zero U p α) c) := by
  exact (congrArg (fun f => f
      (ModuleHomology.cycleClass (RelativeCoefficients.complex Coefficient U) (p + q) c))
    (capProduct_cocycleClass U p q α)).trans
      (homologyCap_cycleClass U p q α.val (cocycle_coboundary_zero U p α) c)

end NoExoticSixSphere.RelativeModTwoCap
