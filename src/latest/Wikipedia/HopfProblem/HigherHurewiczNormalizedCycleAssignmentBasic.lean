import Wikipedia.HopfProblem.FourthHurewiczFourSimplexGenericBasic
import Wikipedia.HopfProblem.HigherHurewiczHomologyDescentConstants

/-!
# Corrected cycle assignments from actual based simplex families

An actual whole-boundary-based simplex is assigned its original singular
chain minus the constant simplex of the same degree. Its genuine cycle
condition follows from the actual face equations. Linearizing this
assignment gives a map from the original singular chain group to the
original cycle kernel in every positive degree.
-/

noncomputable section

namespace Wikipedia.HopfProblem.HigherHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]
variable (n : ℕ) (x : X)
  (f : SingularSimplex X (n + 1) → SimplexGeometry.BasedSimplex (n + 1) x)

/-- The original corrected-cycle assignment of an actual based endpoint family. -/
def normalizedCycleAssignment :
    Chains X (n + 1) →ₗ[ℤ] ModuleHomology.Cycle (singularComplex X) (n + 1) :=
  chainLift X (n + 1) fun smp =>
    correctedSimplexCycle n x (f smp).val (SimplexGeometry.basedSimplex_face (f smp))

@[simp] theorem normalizedCycleAssignment_simplex (smp : SingularSimplex X (n + 1)) :
    normalizedCycleAssignment n x f (simplexChain X (n + 1) smp) =
      correctedSimplexCycle n x (f smp).val (SimplexGeometry.basedSimplex_face (f smp)) :=
  chainLift_simplex X (n + 1) _ smp

/-- The underlying chain is the linear assignment of the actual simplex-minus-constant chains. -/
theorem normalizedCycleAssignment_val (c : Chains X (n + 1)) :
    (normalizedCycleAssignment n x f c).val =
      chainLift X (n + 1) (fun smp => simplexChain X (n + 1) (f smp).val -
        constantSimplexChain (n + 1) x) c := by
  have h : (ModuleHomology.Cycle (singularComplex X) (n + 1)).subtype.comp
        (normalizedCycleAssignment n x f) =
      chainLift X (n + 1) (fun smp => simplexChain X (n + 1) (f smp).val -
        constantSimplexChain (n + 1) x) := by
    apply chainMap_ext X (n + 1)
    intro smp
    simp only [LinearMap.comp_apply, Submodule.subtype_apply,
      normalizedCycleAssignment_simplex, correctedSimplexCycle_val, chainLift_simplex]
  exact LinearMap.congr_fun h c

end Wikipedia.HopfProblem.HigherHurewicz
