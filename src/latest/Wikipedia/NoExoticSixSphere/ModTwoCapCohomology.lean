import Wikipedia.NoExoticSixSphere.ModTwoCapCochainExact
import Wikipedia.HopfProblem.SingularCohomologyCupDescent

/-!
# The genuine mod-two cap product on cohomology and homology

The original operation on closed cochains is additive and annihilates
every actual incoming coboundary. Canonical categorical cohomology descent
therefore produces the bilinear cap product. Its value on genuine
representatives is the original front/back cap chain class.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.ModTwoCapProduct

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule

variable (X : Type) [TopologicalSpace X]

/-- The original homology cap map, varying linearly over genuine cocycles. -/
def capCocycles (p q : ℕ) : Cocycle X p →ₗ[ℤ]
    (ModHomology 2 X (p + q) →ₗ[ℤ] ModHomology 2 X q) :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    { toFun := fun α => homologyCap p q α.val (cocycle_coboundary_zero X p α)
      map_zero' := homologyCap_zero p q _
      map_add' α β := homologyCap_add p q α.val β.val _ _ _ }

theorem capCocycles_apply (p q : ℕ) (α : Cocycle X p) :
    capCocycles X p q α = homologyCap p q α.val (cocycle_coboundary_zero X p α) := rfl

/-- All original cochain boundaries act trivially, including the zero-degree convention. -/
theorem capCocycles_coboundary (p q : ℕ) (β : (cochainComplex X).X (p - 1)) :
    capCocycles X p q (SingularCohomologyFree.coboundaryCocycle (cochainComplex X) p β) = 0 := by
  cases p with
  | zero =>
      have he : SingularCohomologyFree.coboundaryCocycle (cochainComplex X) 0 β = 0 := by
        apply Subtype.ext
        change ((cochainComplex X).d 0 0).hom β = 0
        rw [(cochainComplex X).shape 0 0 (by simp)]
        rfl
      rw [he, map_zero]
  | succ p =>
      exact homologyCap_coboundary p q β

/-- The cap product of the actual mod-two cohomology and homology classes. -/
def capProduct (p q : ℕ) : Cohomology X p →ₗ[ℤ]
    (ModHomology 2 X (p + q) →ₗ[ℤ] ModHomology 2 X q) :=
  SingularCohomologyCup.cohomologyDesc (cochainComplex X) p (capCocycles X p q)
    (capCocycles_coboundary X p q)

/-- A genuine cocycle class acts by its original homology cap map. -/
theorem capProduct_cocycleClass (p q : ℕ) (α : Cocycle X p) :
    capProduct X p q (SingularCohomologyFree.cocycleClass (cochainComplex X) p α) =
      homologyCap p q α.val (cocycle_coboundary_zero X p α) :=
  SingularCohomologyCup.cohomologyDesc_cocycleClass (cochainComplex X) p
    (capCocycles X p q) (capCocycles_coboundary X p q) α

/-- The descended product retains the original cap formula on both actual representatives. -/
theorem capProduct_cocycle_cycle (p q : ℕ) (α : Cocycle X p)
    (c : ModuleHomology.Cycle (modComplex 2 X) (p + q)) :
    capProduct X p q (SingularCohomologyFree.cocycleClass (cochainComplex X) p α)
        (ModuleHomology.cycleClass (modComplex 2 X) (p + q) c) =
      ModuleHomology.cycleClass (modComplex 2 X) q
        (capCycles p q α.val (cocycle_coboundary_zero X p α) c) := by
  exact (congrArg (fun f => f (ModuleHomology.cycleClass (modComplex 2 X) (p + q) c))
    (capProduct_cocycleClass X p q α)).trans
      (homologyCap_cycleClass p q α.val (cocycle_coboundary_zero X p α) c)

end NoExoticSixSphere.ModTwoCapProduct
