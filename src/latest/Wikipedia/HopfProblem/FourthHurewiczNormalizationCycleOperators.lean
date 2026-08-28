import Wikipedia.HopfProblem.FourthHurewiczNormalizationCycles
import Wikipedia.HopfProblem.FourthHurewiczFourSimplexCycles
import Wikipedia.HopfProblem.HigherHurewiczHomologyDescentAugmentation

/-!
# Corrected normalized four-simplex cycle operators

Each normalized simplex contributes its actual corrected four-cycle.
The proved zero coefficient sum of an actual even-dimensional cycle
cancels the constant corrections exactly, before passage to homology.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz SingularMayerVietoris SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]

/-- Linear assignment of the actual corrected cycles of the normalized four-simplices. -/
def normalizedFourSimplexCycleOperator :
    Chains X 4 →ₗ[ℤ] ModuleHomology.Cycle (singularComplex X) 4 :=
  chainLift X 4 fun smp => basedFourSimplexCycle (normalizedFourSimplex x smp)

@[simp] theorem normalizedFourSimplexCycleOperator_simplex (smp : SingularSimplex X 4) :
    normalizedFourSimplexCycleOperator x (simplexChain X 4 smp) =
      basedFourSimplexCycle (normalizedFourSimplex x smp) :=
  chainLift_simplex X 4 _ smp

theorem normalizedFourSimplexCycleOperator_val (c : Chains X 4) :
    (normalizedFourSimplexCycleOperator x c).val =
      chainLift X 4 (fun smp => simplexChain X 4 (normalizedFourSimplex x smp).val -
        simplexChain X 4 (ContinuousMap.const (Simplex 4) x)) c := by
  have h : (ModuleHomology.Cycle (singularComplex X) 4).subtype.comp
        (normalizedFourSimplexCycleOperator x) =
      chainLift X 4 (fun smp => simplexChain X 4 (normalizedFourSimplex x smp).val -
        simplexChain X 4 (ContinuousMap.const (Simplex 4) x)) := by
    apply chainMap_ext X 4
    intro smp
    simp only [LinearMap.comp_apply, normalizedFourSimplexCycleOperator_simplex,
      Submodule.subtype_apply, basedFourSimplexCycle_val, basedFourSimplexChain_eq,
      chainLift_simplex]
  exact LinearMap.congr_fun h c

/-- The constant correction cancels exactly on every actual singular four-cycle. -/
theorem normalizedFourSimplexCycleOperator_cycle
    (c : ModuleHomology.Cycle (singularComplex X) 4) :
    normalizedFourSimplexCycleOperator x c.val = normalizedFourCycle x c := by
  apply Subtype.ext
  rw [normalizedFourSimplexCycleOperator_val,
    HigherHurewicz.chainLift_sub_constant_evenCycle X 4 (by decide) (by decide),
    normalizedFourCycle_val]
  rfl

/-- The corrected assignment still represents the original actual fourth-homology class. -/
theorem normalizedFourSimplexCycleOperator_class
    (c : ModuleHomology.Cycle (singularComplex X) 4) :
    ModuleHomology.cycleClass (singularComplex X) 4
        (normalizedFourSimplexCycleOperator x c.val) =
      ModuleHomology.cycleClass (singularComplex X) 4 c := by
  rw [normalizedFourSimplexCycleOperator_cycle, normalizedFourCycle_class]

end Wikipedia.HopfProblem.FourthHurewicz
