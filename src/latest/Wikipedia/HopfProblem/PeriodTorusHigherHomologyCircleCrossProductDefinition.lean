import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePaths
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductHomology

/-!
# Cross product with the actual positive circle loop

This is the proved bilinear singular-homology cross product, evaluated on
the literal quotient loop `t ↦ t mod 1`. Its two-arc representative gives
an actual chain representative for the later connecting-map calculation.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris CircleTopology CirclePaths

variable (X : Type) [TopologicalSpace X]

/-- Cross product with the genuine positively oriented circle homology class. -/
def positiveCircleCross (n : ℕ) :
    SingularHomology X n →ₗ[ℤ] SingularHomology (Circle × X) (n + 1) :=
  crossProductHomology Circle X n (loopHomologyClass positiveLoop)

/-- On actual cycle representatives this is the constructed singular chain cross product. -/
theorem positiveCircleCross_cycleClass (n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    positiveCircleCross X n (ModuleHomology.cycleClass (singularComplex X) n b) =
      ModuleHomology.cycleClass (singularComplex (Circle × X)) (n + 1)
        (crossProductCycles Circle X n (loopCycle positiveLoop) b) :=
  crossProductHomology_cycleClass Circle X n (loopCycle positiveLoop) b

/-- The same actual cross product may be represented by the sum of the two arc chains. -/
theorem positiveCircleCross_arcSum_cycleClass (n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    positiveCircleCross X n (ModuleHomology.cycleClass (singularComplex X) n b) =
      ModuleHomology.cycleClass (singularComplex (Circle × X)) (n + 1)
        (crossProductCycles Circle X n arcSumCycle b) := by
  have h : ModuleHomology.cycleClass (singularComplex Circle) 1 arcSumCycle =
      loopHomologyClass positiveLoop := arcSumCycle_positiveLoop_class
  change crossProductHomology Circle X n (loopHomologyClass positiveLoop)
    (ModuleHomology.cycleClass (singularComplex X) n b) = _
  rw [← h]
  exact crossProductHomology_cycleClass Circle X n arcSumCycle b

/-- The arc representative has the literal sum of the two arc cross-chains as its value. -/
theorem positiveCircleCross_arcSum_cycle_val (n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    (crossProductCycles Circle X n arcSumCycle b).1 =
      crossProductEdge Circle X n (pathChain uCirclePath + pathChain vCirclePath) b.1 := rfl

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
