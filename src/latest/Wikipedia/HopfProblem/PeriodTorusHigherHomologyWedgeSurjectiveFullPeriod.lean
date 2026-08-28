import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeSurjective
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeFullPeriod

/-!
# Actual marked wedge surjectivity for every full period matrix

The actual additive coordinate homeomorphism and the proved positive-loop
marking discharge the hypotheses of the coordinate-subtorus generation
argument. No special form of the full period matrix, nor any assumed
homology or exterior-power comparison, is required.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

/-- Every actual coordinate two-subtorus class is in the marked wedge image. -/
theorem fullPeriodCoordinateClass_mem_range_wedgeTwo (q : FullPeriodMatrix)
    (i : Fin (Nat.choose 4 2)) :
    coordinateTorusClassAlong q.productTorusHomeomorph 2 i ∈
      LinearMap.range (fullPeriodTorusWedgeTwo q) := by
  let := fullPeriodTorus_homology_torsionFree q 2
  exact coordinateTorusClassAlong_mem_range_latticeWedgeTwo
    q.productTorusHomeomorph q.productTorusHomeomorph_add
    (fullPeriodCoordinateH1 q) (fullPeriodCoordinateH1_surjective q) i

/-- Every actual coordinate three-subtorus class is in the marked wedge image. -/
theorem fullPeriodCoordinateClass_mem_range_wedgeThree (q : FullPeriodMatrix)
    (i : Fin (Nat.choose 4 3)) :
    coordinateTorusClassAlong q.productTorusHomeomorph 3 i ∈
      LinearMap.range (fullPeriodTorusWedgeThree q) := by
  let := fullPeriodTorus_homology_torsionFree q 2
  exact coordinateTorusClassAlong_mem_range_latticeWedgeThree
    q.productTorusHomeomorph q.productTorusHomeomorph_add
    (fullPeriodCoordinateH1 q) (fullPeriodCoordinateH1_surjective q) i

/-- The actual marked exterior-square map is surjective for every full period matrix. -/
theorem fullPeriodTorusWedgeTwo_surjective (q : FullPeriodMatrix) :
    Function.Surjective (fullPeriodTorusWedgeTwo q) :=
  surjective_of_coordinateTorusClassAlong_mem_range q.productTorusHomeomorph 2
    (fullPeriodTorusWedgeTwo q) (fullPeriodCoordinateClass_mem_range_wedgeTwo q)

/-- The actual marked exterior-cube map is surjective for every full period matrix. -/
theorem fullPeriodTorusWedgeThree_surjective (q : FullPeriodMatrix) :
    Function.Surjective (fullPeriodTorusWedgeThree q) :=
  surjective_of_coordinateTorusClassAlong_mem_range q.productTorusHomeomorph 3
    (fullPeriodTorusWedgeThree q) (fullPeriodCoordinateClass_mem_range_wedgeThree q)

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
