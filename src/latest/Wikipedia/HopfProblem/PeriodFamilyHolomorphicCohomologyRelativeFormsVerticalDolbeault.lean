import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsVerticalBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyMarkedLinearFrame
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeBasic

/-!
# The native vertical block of the full antiholomorphic differential

The full differential is restricted to actual vertical tangent vectors of
`ℂ × ComplexPlane₂`. Its first two inverse-period coordinate covectors are
identified with the already proved original marked Dolbeault isomorphism.
-/

noncomputable section

open Complex TopologicalSpace
open scoped Matrix BigOperators

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms

open HolomorphicDolbeaultThree

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- A single inverse-period coordinate is the original marked primitive
with its corresponding unit period value. -/
theorem verticalCoordinateLinear_eq_primitive (b : U) (j : Fin 4) :
    verticalCoordinateLinear P b j =
      MarkedLinear.primitive (P.point b) (Pi.single j 1) := by
  ext w
  simp only [verticalCoordinateLinear_apply, MarkedLinear.primitive_apply]
  simp [Pi.single_apply]
  rfl

/-- Restricting the full antiholomorphic differential to a vertical vector
gives the antiholomorphic part of the actual inverse period map. -/
theorem coordinate_dbar_vertical (j : Fin 4) (b : U) (z w : ComplexPlane₂) :
    dbar (coordinate P j) ((b : ℂ), z) (0, w) =
      antiPart (verticalCoordinateLinear P b j) w := by
  rw [dbar_apply, antiPart_apply]
  simp only [Prod.smul_mk, smul_zero, coordinate_fderiv_vertical,
    verticalCoordinateLinear_apply]

/-- The vertical standard-coordinate coefficients are the genuine
two-dimensional marked Dolbeault coefficients. -/
theorem coordinate_dbar_vertical_basis (j : Fin 4) (b : U)
    (z : ComplexPlane₂) (i : Fin 2) :
    dbar (coordinate P j) ((b : ℂ), z) (0, Pi.single i 1) =
      MarkedLinear.dbarLinear (P.point b) (Pi.single j 1) i := by
  rw [coordinate_dbar_vertical, verticalCoordinateLinear_eq_primitive,
    antiPart_apply, MarkedLinear.dbarLinear_apply]

/-- The first-two-period embedding is the literal sum of its two marked
unit vectors. -/
theorem firstCoefficients_eq_sum (c : Fin 2 → ℂ) :
    MarkedLinear.firstCoefficients c =
      c 0 • Pi.single (0 : Fin 4) 1 + c 1 • Pi.single (1 : Fin 4) 1 := by
  ext j
  fin_cases j <;> simp [MarkedLinear.firstCoefficients]

/-- The original primitive supported in the first two period coordinates
is the corresponding sum of the actual inverse-coordinate functionals. -/
theorem primitive_firstCoefficients_eq (b : U) (c : Fin 2 → ℂ) :
    MarkedLinear.primitive (P.point b) (MarkedLinear.firstCoefficients c) =
      c 0 • verticalCoordinateLinear P b 0 +
        c 1 • verticalCoordinateLinear P b 1 := by
  rw [verticalCoordinateLinear_eq_primitive, verticalCoordinateLinear_eq_primitive,
    firstCoefficients_eq_sum]
  change MarkedLinear.primitiveLinear (P.point b) (_ + _) = _
  rw [map_add, map_smul, map_smul]
  rfl

/-- The first two full coordinate covectors restrict to the original
marked primitive on every vertical tangent vector, not only on a basis. -/
theorem first_coordinate_dbar_vertical (b : U) (z w : ComplexPlane₂)
    (c : Fin 2 → ℂ) :
    (c 0 • dbar (coordinate P 0) ((b : ℂ), z) +
      c 1 • dbar (coordinate P 1) ((b : ℂ), z)) (0, w) =
        antiPart (MarkedLinear.primitive (P.point b)
          (MarkedLinear.firstCoefficients c)) w := by
  rw [primitive_firstCoefficients_eq, antiPart_add,
    antiPart_complex_smul, antiPart_complex_smul]
  simp only [add_apply, smul_apply, coordinate_dbar_vertical]

/-- The genuine vertical block of the full first-two-coordinate form is
exactly the original complex-linear Dolbeault frame isomorphism. -/
theorem first_coordinate_dbar_vertical_basis (b : U) (z : ComplexPlane₂)
    (c : Fin 2 → ℂ) (i : Fin 2) :
    (c 0 • dbar (coordinate P 0) ((b : ℂ), z) +
      c 1 • dbar (coordinate P 1) ((b : ℂ), z)) (0, Pi.single i 1) =
        MarkedLinear.firstDbarEquiv (P.point b) c i := by
  rw [first_coordinate_dbar_vertical, MarkedLinear.firstDbarEquiv_apply,
    antiPart_apply, MarkedLinear.dbarLinear_apply]

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms
