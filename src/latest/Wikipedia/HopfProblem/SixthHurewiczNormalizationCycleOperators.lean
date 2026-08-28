import Wikipedia.HopfProblem.SixthHurewiczNormalization
import Wikipedia.HopfProblem.SixthHurewiczSixSimplexCycles
import Wikipedia.HopfProblem.HigherHurewiczNormalizedCycleAssignment

/-!
# Corrected normalized six-simplex cycles preserve actual homology

This specializes the proved all-degree cycle-assignment theorem. In
positive even degree, the actual augmentation of a singular cycle is
zero, so the constant-simplex corrections cancel. The genuine prism
then identifies the normalized cycle with the original homology class.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SixthHurewicz

open FirstHurewicz SingularMayerVietoris SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]

/-- The genuine corrected-cycle assignment of the actual normalized six-simplices. -/
def normalizedSixSimplexCycleOperator :
    Chains X 6 →ₗ[ℤ] ModuleHomology.Cycle (singularComplex X) 6 :=
  HigherHurewicz.normalizedCycleAssignment 5 x (normalizedSixSimplex x)

@[simp] theorem normalizedSixSimplexCycleOperator_simplex (smp : SingularSimplex X 6) :
    normalizedSixSimplexCycleOperator x (simplexChain X 6 smp) =
      basedSixSimplexCycle (normalizedSixSimplex x smp) :=
  HigherHurewicz.normalizedCycleAssignment_simplex 5 x (normalizedSixSimplex x) smp

theorem normalizedSixSimplexCycleOperator_val (c : Chains X 6) :
    (normalizedSixSimplexCycleOperator x c).val =
      chainLift X 6 (fun smp => simplexChain X 6 (normalizedSixSimplex x smp).val -
        simplexChain X 6 (ContinuousMap.const (Simplex 6) x)) c :=
  HigherHurewicz.normalizedCycleAssignment_val 5 x (normalizedSixSimplex x) c

/-- The actual coherent prism recovers the original class of every singular six-cycle. -/
theorem normalizedSixSimplexCycleOperator_class
    (c : ModuleHomology.Cycle (singularComplex X) 6) :
    ModuleHomology.cycleClass (singularComplex X) 6
        (normalizedSixSimplexCycleOperator x c.val) =
      ModuleHomology.cycleClass (singularComplex X) 6 c := by
  apply HigherHurewicz.normalizedCycleAssignment_class 5 x (normalizedSixSimplex x)
    (normalizationFiveSimplexHomotopy x) (normalizationSixSimplexHomotopy x)
    (normalizationHomotopy_face x) _ (fun _ => rfl) c
  intro smp
  ext s
  exact normalizationSixSimplexHomotopy_zero x smp s

end Wikipedia.HopfProblem.SixthHurewicz
