import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepFibre
import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepFlatProduct

/-!
# Integral coordinates of the original delta sweep

These formulas use the actual ordered exterior-square marking and the
actual regular-family homology marking.  In particular the delta-first
sweep of the positive gamma class has coordinate `-6`, not a primitive
unit.  The vanishing statement is the genuine global sweep vanishing,
not an assumption about the global second homology group.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep

open Elliptic TrianglePeriodFamily SingularMayerVietoris
open PeriodTorusHigherHomology PeriodTorusHigherHomologyPontryagin

/-- The exact regular-family coordinates of the actual delta-first
Pontryagin class from any original regular fibre. -/
theorem regular_delta_product_coordinates (z : TriangleRegularPoint) (v : Lattice) :
    TrianglePeriodFamily.Homology.familyH2Equiv VerticalAction.Regular.data
      (singularHomologyMap
        (TrianglePeriodFamily.Homology.pointFamilyFibreInclusion
          VerticalAction.Regular.data z) 2
        (product11 RealTorus₄ (FlatTorus.singularH1Equiv.symm deltaLattice)
          (FlatTorus.singularH1Equiv.symm v))) =
      ![-6 * v 0, 0, 0, 0, 0, 0] := by
  rw [TrianglePeriodFamily.Homology.familyH2Equiv_pointFibre, deltaLattice,
    flat_delta_product11_coordinates]
  simp [mul_neg, neg_mul]

/-- In the genuine joint monodromy coinvariant, the same delta-first
product is exactly minus six times the gamma coordinate of its input. -/
theorem jointCoinvariant_delta_product (v : Lattice) :
    TrianglePeriodFamily.HomologyDifference.cokernelTwoEquiv
      (Submodule.Quotient.mk
        (product11 RealTorus₄ (FlatTorus.singularH1Equiv.symm deltaLattice)
          (FlatTorus.singularH1Equiv.symm v))) = -6 * v 0 := by
  rw [TrianglePeriodFamily.HomologyDifference.cokernelTwoEquiv_mk, deltaLattice,
    flat_delta_product11_coordinates]
  simp [mul_neg, neg_mul]

/-- The exact marked regular-family class maps to zero in the original
global manifold. This records the integral relation without inferring
that the coefficient six is a unit. -/
theorem originalRegular_firstAxis_six_eq_zero (v : Lattice) :
    singularHomologyMap originalRegularInclusion 2
      ((TrianglePeriodFamily.Homology.familyH2Equiv VerticalAction.Regular.data).symm
        ![-6 * v 0, 0, 0, 0, 0, 0]) = 0 := by
  let z := TrianglePeriodFamily.Homology.normalizedSlitBaseLift.val
  rw [← regular_delta_product_coordinates z v, LinearEquiv.symm_apply_apply]
  have h := fibre_delta_product_eq_zero z (FlatTorus.singularH1Equiv.symm v)
  simpa only [fibreInclusion, singularHomologyMap_comp, LinearMap.comp_apply] using h

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep
