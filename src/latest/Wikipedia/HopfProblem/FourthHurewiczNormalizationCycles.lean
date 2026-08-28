import Wikipedia.HopfProblem.FourthHurewiczNormalization
import Wikipedia.HopfProblem.HigherHurewiczPrismCycles

/-!
# The actual fourth-homology class is preserved by normalization

The full geometric homotopy acts on the original singular chain groups.
Its exact face compatibility gives a terminal cycle, and the genuine
five-dimensional prism is a boundary witness for preservation of the
original integral homology class.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz SingularMayerVietoris SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]

/-- Linearization of the actual normalized four-simplex maps. -/
def normalizedFourChain : Chains X 4 →ₗ[ℤ] Chains X 4 :=
  chainLift X 4 fun smp => simplexChain X 4 (normalizedFourSimplex x smp).val

@[simp] theorem normalizedFourChain_simplex (smp : SingularSimplex X 4) :
    normalizedFourChain x (simplexChain X 4 smp) =
      simplexChain X 4 (normalizedFourSimplex x smp).val :=
  chainLift_simplex X 4 _ smp

theorem normalizedFourChain_eq :
    normalizedFourChain x = simplexEndpointOperator 4 (normalizationFourSimplexHomotopy x) 1 :=
  rfl

/-- The genuine terminal singular four-cycle. -/
def normalizedFourCycle (c : ModuleHomology.Cycle (singularComplex X) 4) :
    ModuleHomology.Cycle (singularComplex X) 4 :=
  HigherHurewicz.straightenedCycle 3 (normalizationThreeSimplexHomotopy x)
    (normalizationFourSimplexHomotopy x) (normalizationHomotopy_face x) c

@[simp] theorem normalizedFourCycle_val (c : ModuleHomology.Cycle (singularComplex X) 4) :
    (normalizedFourCycle x c).val = normalizedFourChain x c.val := rfl

/-- The actual singular prism proves equality in the original fourth homology. -/
theorem normalizedFourCycle_class (c : ModuleHomology.Cycle (singularComplex X) 4) :
    ModuleHomology.cycleClass (singularComplex X) 4 (normalizedFourCycle x c) =
      ModuleHomology.cycleClass (singularComplex X) 4 c := by
  apply HigherHurewicz.straightenedCycle_class 3 (normalizationThreeSimplexHomotopy x)
    (normalizationFourSimplexHomotopy x) (normalizationHomotopy_face x) _ c
  intro smp
  ext s
  exact normalizationFourSimplexHomotopy_zero x smp s

end Wikipedia.HopfProblem.FourthHurewicz
