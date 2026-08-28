import Wikipedia.HopfProblem.ThreefoldHomologyFifthArithmetic
import Wikipedia.HopfProblem.ThreefoldHomologyFifthCapEquations
import Wikipedia.HopfProblem.ThreefoldHomologyFifthRegular

/-!
# Vanishing of the actual fifth integral homology

For an actual fifth homology class, genuine Wang exactness supplies three
original fibre classes.  The actual cap maps give their signed integral
coefficients, and the full regular relation gives their sum.  These
equations force the common Wang integer to vanish for every value of
the actual integral cusp coefficient.  The previously proved native
Wang injection then kills the original fifth class.

The argument uses neither Poincaré duality nor a stipulated attachment
matrix, and does not assume that the cusp reference class has zero cap
image.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FifthDegree

open SingularMayerVietoris PeriodTorusHigherHomology FourthWang
open CategoryTheory.Limits

/-- The actual fifth-degree Wang integer vanishes by the signed integral attachment equations. -/
theorem fifthWangCoordinate_vanishes (a : SingularHomology Space 5) :
    fifthWangCoordinate a = 0 := by
  obtain ⟨b, hb⟩ := exists_fifth_boundary_fibres a
  have hthree := threeFibre_coordinate_of_decomposition a (b (some .three)) (hb (some .three))
  have hfour := fourFibre_coordinate_of_decomposition a (b (some .four)) (hb (some .four))
  have hcusp := cuspFibre_coordinate_of_decomposition a (b none) (hb none)
  have hsum := fifth_boundary_fibre_coordinates_sum_zero a b hb
  have hregular : realTorusH4Equiv (b (some .three)) + realTorusH4Equiv (b (some .four)) =
      cuspResidualCoefficient * fifthWangCoordinate a := by
    linear_combination hsum - hcusp
  exact signed_residual_coordinate_zero (fifthWangCoordinate a)
    (realTorusH4Equiv (b (some .three))) (realTorusH4Equiv (b (some .four)))
    cuspResidualCoefficient hthree hfour hregular

/-- Every class in the genuine fifth integral singular homology is zero. -/
theorem homologyFive_eq_zero (a : SingularHomology Space 5) : a = 0 :=
  fifthWangCoordinate_eq_zero a (fifthWangCoordinate_vanishes a)

theorem homologyFive_subsingleton : Subsingleton (SingularHomology Space 5) :=
  ⟨fun a b => (homologyFive_eq_zero a).trans (homologyFive_eq_zero b).symm⟩

/-- Categorical vanishing of the original integral singular homology object. -/
theorem homologyFive_isZero : IsZero (SingularHomology Space 5) := by
  have := homologyFive_subsingleton
  exact ModuleCat.isZero_of_subsingleton _

theorem homologyFive_finrank : Module.finrank ℤ (SingularHomology Space 5) = 0 := by
  have := homologyFive_subsingleton
  exact Module.finrank_zero_of_subsingleton

theorem rationalBetti_five : Finiteness.rationalBetti 5 = 0 := by
  have := homologyFive_subsingleton
  exact Module.finrank_zero_of_subsingleton

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FifthDegree
