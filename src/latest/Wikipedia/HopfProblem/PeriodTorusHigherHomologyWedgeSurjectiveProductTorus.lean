import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeSurjective
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeProductTorus

/-!
# Surjectivity of the actual coordinate-torus exterior maps

The actual coordinate-loop marking of the four-circle torus is surjective.
The proved coordinate-subtorus basis then makes its actual exterior-square
and exterior-cube maps surjective, without any period-domain parameter or
extra topological hypothesis in the statements.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

/-- The actual positive coordinate-loop marking is surjective; an explicitly
constructed admissible period discharges the witness used in its comparison. -/
theorem coordinateH1_four_surjective : Function.Surjective (coordinateH1 4) :=
  (coordinateH1_four_bijective (Elliptic.examplePeriod .four)).surjective

/-- The actual coordinate-loop exterior-square map is unconditionally surjective. -/
theorem coordinateTorusWedgeTwo_surjective : Function.Surjective coordinateTorusWedgeTwo := by
  let := productTorus_homology_torsionFree 4 2
  exact latticeWedgeTwo_surjective_of_torusHomeomorph (Homeomorph.refl (ProductTorus 4))
    (fun _ _ => rfl) (coordinateH1 4) coordinateH1_four_surjective

/-- The actual coordinate-loop exterior-cube map is unconditionally surjective. -/
theorem coordinateTorusWedgeThree_surjective : Function.Surjective coordinateTorusWedgeThree := by
  let := productTorus_homology_torsionFree 4 2
  exact latticeWedgeThree_surjective_of_torusHomeomorph (Homeomorph.refl (ProductTorus 4))
    (fun _ _ => rfl) (coordinateH1 4) coordinateH1_four_surjective

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
