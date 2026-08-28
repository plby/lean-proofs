import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.Normalization
import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.SevenSimplexCycles
import Wikipedia.HopfProblem.HigherHurewiczNormalizedCycleAssignment

/-!
# Corrected normalized seven-simplex cycles preserve actual homology

The general normalization theorem applies in degree seven. The remaining
constant cycle is a boundary, and the coherent prism identifies the
normalized homology class with the original one.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open FirstHurewicz SingularMayerVietoris SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] [Subsingleton (π_ 6 X x)]

/-- The genuine corrected-cycle assignment of the actual normalized seven-simplices. -/
def normalizedSevenSimplexCycleOperator :
    Chains X 7 →ₗ[ℤ] ModuleHomology.Cycle (singularComplex X) 7 :=
  HigherHurewicz.normalizedCycleAssignment 6 x (normalizedSevenSimplex x)

@[simp] theorem normalizedSevenSimplexCycleOperator_simplex (smp : SingularSimplex X 7) :
    normalizedSevenSimplexCycleOperator x (simplexChain X 7 smp) =
      basedSevenSimplexCycle (normalizedSevenSimplex x smp) :=
  HigherHurewicz.normalizedCycleAssignment_simplex 6 x (normalizedSevenSimplex x) smp

theorem normalizedSevenSimplexCycleOperator_val (c : Chains X 7) :
    (normalizedSevenSimplexCycleOperator x c).val =
      chainLift X 7 (fun smp => simplexChain X 7 (normalizedSevenSimplex x smp).val -
        simplexChain X 7 (ContinuousMap.const (Simplex 7) x)) c :=
  HigherHurewicz.normalizedCycleAssignment_val 6 x (normalizedSevenSimplex x) c

/-- The actual coherent prism recovers the original class of every singular seven-cycle. -/
theorem normalizedSevenSimplexCycleOperator_class
    (c : ModuleHomology.Cycle (singularComplex X) 7) :
    ModuleHomology.cycleClass (singularComplex X) 7
        (normalizedSevenSimplexCycleOperator x c.val) =
      ModuleHomology.cycleClass (singularComplex X) 7 c := by
  apply HigherHurewicz.normalizedCycleAssignment_class 6 x (normalizedSevenSimplex x)
    (normalizationSixSimplexHomotopy x) (normalizationSevenSimplexHomotopy x)
    (normalizationHomotopy_face x) _ (fun _ => rfl) c
  intro smp
  ext s
  exact normalizationSevenSimplexHomotopy_zero x smp s

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
