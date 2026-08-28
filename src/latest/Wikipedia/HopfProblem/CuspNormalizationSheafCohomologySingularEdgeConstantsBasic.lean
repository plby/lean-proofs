import Wikipedia.HopfProblem.SheafCupProductCohomologyScalars
import Wikipedia.HopfProblem.SheafCupProductFunctionsLinear

/-!
# The original constants inclusion is complex-linear on native cohomology

The source and target scalar actions are the existing actions induced
by multiplication of actual constant and reduced holomorphic sections.
The forward map is the original sheaf cohomology map in every degree.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologySingularEdge

open SheafCupProduct

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace B] {M : Type} [TopologicalSpace M] [ChartedSpace B M]
  (I : ModelWithCorners ℂ E B) (S : Set M)

local instance constantHAddCommGroup (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0}
      (SheafConstants.complexAdditiveSheaf (TopCat.of S)) n) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

local instance reducedHAddCommGroup (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} (SheafReduced.additiveSheaf I S) n) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- The actual constants-to-reduced map commutes with the original
scalar-induced native cohomology actions. -/
theorem reducedConstantsCohomology_smul (n : ℕ) (c : ℂ)
    (a : CategoryTheory.Sheaf.H.{0}
      (SheafConstants.complexAdditiveSheaf (TopCat.of S)) n) :
    letI := constantCohomologyModule (TopCat.of S) n
    letI := reducedFunctionCohomologyModule I S n
    CategoryTheory.Sheaf.H.map (SheafConstants.reducedAdditiveMap I S) n (c • a) =
      c • CategoryTheory.Sheaf.H.map (SheafConstants.reducedAdditiveMap I S) n a := by
  let := constantCohomologyModule (TopCat.of S) n
  let := reducedFunctionCohomologyModule I S n
  have h := Scalars.cohomologyMap_scalar (SheafConstants.reducedMap I S)
    (constantCoefficients (TopCat.of S)) (reducedCoefficients I S)
    (reducedMap_coefficients I S) n c a
  rw [scalarEnd_reducedCoefficients] at h
  exact h

/-- The original map on genuine Ext groups, with its proved complex-linearity. -/
def reducedConstantsCohomologyLinearMap (n : ℕ) :
    letI := constantCohomologyModule (TopCat.of S) n
    letI := reducedFunctionCohomologyModule I S n
    CategoryTheory.Sheaf.H.{0}
        (SheafConstants.complexAdditiveSheaf (TopCat.of S)) n →ₗ[ℂ]
      CategoryTheory.Sheaf.H.{0} (SheafReduced.additiveSheaf I S) n := by
  letI := constantCohomologyModule (TopCat.of S) n
  letI := reducedFunctionCohomologyModule I S n
  exact
    { toFun := CategoryTheory.Sheaf.H.map (SheafConstants.reducedAdditiveMap I S) n
      map_add' := (CategoryTheory.Sheaf.H.map
        (SheafConstants.reducedAdditiveMap I S) n).map_add
      map_smul' := reducedConstantsCohomology_smul I S n }

/-- No new forward map is chosen in the linear upgrade. -/
@[simp] theorem reducedConstantsCohomologyLinearMap_apply (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0}
      (SheafConstants.complexAdditiveSheaf (TopCat.of S)) n) :
    reducedConstantsCohomologyLinearMap I S n a =
      CategoryTheory.Sheaf.H.map (SheafConstants.reducedAdditiveMap I S) n a := rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologySingularEdge
