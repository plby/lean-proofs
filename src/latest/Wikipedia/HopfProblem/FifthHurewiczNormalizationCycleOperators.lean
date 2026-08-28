import Wikipedia.HopfProblem.FifthHurewiczNormalization
import Wikipedia.HopfProblem.FifthHurewiczFiveSimplexCycles
import Wikipedia.HopfProblem.HigherHurewiczNormalizedCycleAssignment

/-!
# Corrected normalized five-simplex cycles preserve actual homology

This is a specialization of the proved all-degree cycle-assignment
theorem. The actual constant-five-simplex correction is a genuine
six-boundary; it is not discarded or assumed to vanish.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FifthHurewicz

open FirstHurewicz SingularMayerVietoris SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)]

/-- The genuine corrected-cycle assignment of the actual normalized five-simplices. -/
def normalizedFiveSimplexCycleOperator :
    Chains X 5 →ₗ[ℤ] ModuleHomology.Cycle (singularComplex X) 5 :=
  HigherHurewicz.normalizedCycleAssignment 4 x (normalizedFiveSimplex x)

@[simp] theorem normalizedFiveSimplexCycleOperator_simplex (smp : SingularSimplex X 5) :
    normalizedFiveSimplexCycleOperator x (simplexChain X 5 smp) =
      basedFiveSimplexCycle (normalizedFiveSimplex x smp) :=
  HigherHurewicz.normalizedCycleAssignment_simplex 4 x (normalizedFiveSimplex x) smp

theorem normalizedFiveSimplexCycleOperator_val (c : Chains X 5) :
    (normalizedFiveSimplexCycleOperator x c).val =
      chainLift X 5 (fun smp => simplexChain X 5 (normalizedFiveSimplex x smp).val -
        simplexChain X 5 (ContinuousMap.const (Simplex 5) x)) c :=
  HigherHurewicz.normalizedCycleAssignment_val 4 x (normalizedFiveSimplex x) c

/-- The actual prism and actual constant-six-simplex boundary recover the original class. -/
theorem normalizedFiveSimplexCycleOperator_class
    (c : ModuleHomology.Cycle (singularComplex X) 5) :
    ModuleHomology.cycleClass (singularComplex X) 5
        (normalizedFiveSimplexCycleOperator x c.val) =
      ModuleHomology.cycleClass (singularComplex X) 5 c := by
  apply HigherHurewicz.normalizedCycleAssignment_class 4 x (normalizedFiveSimplex x)
    (normalizationFourSimplexHomotopy x) (normalizationFiveSimplexHomotopy x)
    (normalizationHomotopy_face x) _ (fun _ => rfl) c
  intro smp
  ext s
  exact normalizationFiveSimplexHomotopy_zero x smp s

end Wikipedia.HopfProblem.FifthHurewicz
