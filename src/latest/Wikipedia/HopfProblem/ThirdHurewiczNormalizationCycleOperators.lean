import Wikipedia.HopfProblem.ThirdHurewiczNormalizationCycles
import Wikipedia.HopfProblem.ThirdHurewiczThreeSimplexCycles
import Wikipedia.HopfProblem.ThirdHurewiczHomologyDescentConstants
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedDescentAugmentation

/-!
# Corrected normalized three-simplex cycle operators

The actual cubical representative of a based three-simplex has a constant
three-simplex correction. Unlike degree two, a three-cycle need not have
coefficient sum zero. Instead the correction is an explicit multiple of
the constant three-cycle, already proved to be a genuine four-boundary.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SingularMayerVietoris SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)]

/-- Linear assignment of actual corrected cycles of the normalized three-simplices. -/
def normalizedThreeSimplexCycleOperator :
    Chains X 3 →ₗ[ℤ] ModuleHomology.Cycle (singularComplex X) 3 :=
  chainLift X 3 fun smp => basedThreeSimplexCycle (normalizedThreeSimplex x smp)

@[simp] theorem normalizedThreeSimplexCycleOperator_simplex (smp : SingularSimplex X 3) :
    normalizedThreeSimplexCycleOperator x (simplexChain X 3 smp) =
      basedThreeSimplexCycle (normalizedThreeSimplex x smp) :=
  chainLift_simplex X 3 _ smp

theorem normalizedThreeSimplexCycleOperator_val (c : Chains X 3) :
    (normalizedThreeSimplexCycleOperator x c).val =
      chainLift X 3 (fun smp => simplexChain X 3 (normalizedThreeSimplex x smp).val -
        simplexChain X 3 (ContinuousMap.const (Simplex 3) x)) c := by
  have h : (ModuleHomology.Cycle (singularComplex X) 3).subtype.comp
        (normalizedThreeSimplexCycleOperator x) =
      chainLift X 3 (fun smp => simplexChain X 3 (normalizedThreeSimplex x smp).val -
        simplexChain X 3 (ContinuousMap.const (Simplex 3) x)) := by
    apply chainMap_ext X 3
    intro smp
    simp only [LinearMap.comp_apply, normalizedThreeSimplexCycleOperator_simplex,
      Submodule.subtype_apply, basedThreeSimplexCycle_val, chainLift_simplex]
  exact LinearMap.congr_fun h c

/-- The correction is the actual coefficient sum times the actual constant cycle. -/
theorem normalizedThreeSimplexCycleOperator_cycle
    (c : ModuleHomology.Cycle (singularComplex X) 3) :
    normalizedThreeSimplexCycleOperator x c.val =
      normalizedThreeCycle x c - chainAugmentation X 3 c.val • constantThreeCycle x := by
  apply Subtype.ext
  change (normalizedThreeSimplexCycleOperator x c.val).val =
    (normalizedThreeCycle x c).val - chainAugmentation X 3 c.val • (constantThreeCycle x).val
  rw [normalizedThreeSimplexCycleOperator_val, chainLift_sub_constant,
    normalizedThreeCycle_val, constantThreeCycle_val]
  rfl

/-- The genuine four-boundary correction vanishes in the original singular
homology, so the corrected operator still represents the original class. -/
theorem normalizedThreeSimplexCycleOperator_class
    (c : ModuleHomology.Cycle (singularComplex X) 3) :
    ModuleHomology.cycleClass (singularComplex X) 3
        (normalizedThreeSimplexCycleOperator x c.val) =
      ModuleHomology.cycleClass (singularComplex X) 3 c := by
  rw [normalizedThreeSimplexCycleOperator_cycle, map_sub, map_zsmul,
    constantThreeCycle_class, zsmul_zero, sub_zero, normalizedThreeCycle_class]

end Wikipedia.HopfProblem.ThirdHurewicz
