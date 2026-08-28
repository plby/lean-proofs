import Wikipedia.HopfProblem.ThreefoldHomologySecondCyclic
import Wikipedia.HopfProblem.ThreefoldHomologyCentralFibreCompatibility
import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepCentralCoordinates
import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessGlobal

/-!
# Vanishing of the actual second integral homology

The actual central circle sweep supplies a global-kernel class whose
second coordinate is one in each unchanged surface marking.  The
original covering image of the positive twist-circle crossed with the
`w` circle is the norm index times this class, including its genuine
shear.  Its original fibre coordinates evaluate to two and minus three
in the already proved cyclic presentation of global second homology.
These two actual relations kill the primitive generator integrally.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.SecondDegree

open SingularMayerVietoris PeriodTorusHigherHomology TrianglePeriodFamily
open Elliptic Elliptic.HigherHomology SpecialPeriods.EllipticFilling
open TrianglePeriodFamily.Boundary.EllipticCapKernelWang
open CapElimination DeltaSweep CategoryTheory.Limits

/-- The actual marked finite-cover class has zero image under the original central inclusion. -/
theorem centralCover_splitCircle_global_eq_zero (j : Kind) :
    singularHomologyMap (centralInclusionMap j) 2
      (singularHomologyMap (surfaceCover j) 2 (splitCircleClassTwo j)) = 0 := by
  obtain ⟨a, ha, hz⟩ := exists_centralKernelClass_unit_secondCoordinate j
  have hclass : singularHomologyMap (surfaceCover j) 2 (splitCircleClassTwo j) =
      (fibreNormIndex j : ℤ) • a := by
    apply (surfaceH2Equiv j (specialLocalData j).centralPeriod).injective
    rw [surfaceCover_splitCircleClassTwo]
    have hm := map_zsmul (surfaceH2Equiv j (specialLocalData j).centralPeriod)
      (fibreNormIndex j : ℤ) a
    rw [ha] at hm
    rw [hm]
    ext i
    fin_cases i
    · simpa using (fibreNormIndex_mul_centralSweepShearCorrection j).symm
    · simp
  rw [hclass]
  have hm := map_zsmul (singularHomologyMap (centralInclusionMap j) 2)
    (fibreNormIndex j : ℤ) a
  rw [hz] at hm
  exact hm.trans (@zsmul_zero (SingularHomology Space 2) _ (fibreNormIndex j : ℤ))

/-- The same vanishing for the actual normalized regular fibre, through original map agreement. -/
theorem regularFibre_splitCircle_global_eq_zero (j : Kind) :
    singularHomologyMap regularFibreIntoSpace 2 (splitCircleClassTwo j) = 0 := by
  rw [CentralFibreCompatibility.regularFibreIntoSpace_homology_eq_central_apply,
    centralFlatPeriodCover_eq_surfaceCover]
  exact centralCover_splitCircle_global_eq_zero j

/-- The original fibre marking evaluates the relation at the actual twist's `u` coefficient. -/
theorem homologyTwoCyclicMap_twist_u_eq_zero (j : Kind) :
    homologyTwoCyclicMap (j.twist 1) = 0 := by
  have h := (regularFibre_homologyTwo_coordinates (splitCircleClassTwo j)).symm.trans
    (regularFibre_splitCircle_global_eq_zero j)
  have hc : 6 * FlatTorus.singularH2Coordinates (splitCircleClassTwo j) 2 +
      FlatTorus.singularH2Coordinates (splitCircleClassTwo j) 3 = j.twist 1 := by
    rw [splitCircleClassTwo_coordinates]
    simp
  exact (congrArg homologyTwoCyclicMap hc).symm.trans h

/-- The actual order-three filling kills twice the genuine cyclic generator. -/
theorem homologyTwoCyclicMap_two_eq_zero : homologyTwoCyclicMap 2 = 0 := by
  simpa [Kind.twist, ε] using homologyTwoCyclicMap_twist_u_eq_zero Kind.three

/-- The original negative order-four twist kills minus three times the same generator. -/
theorem homologyTwoCyclicMap_neg_three_eq_zero : homologyTwoCyclicMap (-3) = 0 := by
  simpa [Kind.twist, ε'] using homologyTwoCyclicMap_twist_u_eq_zero Kind.four

/-- The two actual signed relations kill the primitive integral generator. -/
theorem homologyTwoGenerator_eq_zero : homologyTwoGenerator = 0 := by
  change homologyTwoCyclicMap 1 = 0
  rw [show (1 : ℤ) = 2 + 2 + -3 by decide, map_add, map_add,
    homologyTwoCyclicMap_two_eq_zero, homologyTwoCyclicMap_neg_three_eq_zero]
  simp only [add_zero]

/-- Vanishing of the original native integral second-homology group. -/
theorem homologyTwo_subsingleton : Subsingleton (SingularHomology Space 2) :=
  homologyTwo_subsingleton_iff_generator_eq_zero.mpr homologyTwoGenerator_eq_zero

theorem homologyTwo_eq_zero (a : SingularHomology Space 2) : a = 0 :=
  homologyTwo_subsingleton.elim _ _

theorem homologyTwo_isZero : IsZero (SingularHomology Space 2) := by
  have := homologyTwo_subsingleton
  exact ModuleCat.isZero_of_subsingleton _

theorem homologyTwo_finrank : Module.finrank ℤ (SingularHomology Space 2) = 0 := by
  have := homologyTwo_subsingleton
  exact Module.finrank_zero_of_subsingleton

theorem rationalBetti_two : Finiteness.rationalBetti 2 = 0 := by
  have := homologyTwo_subsingleton
  exact Module.finrank_zero_of_subsingleton

/-- The corresponding original native relation map is consequently surjective. -/
theorem nativeCapKernelRegularMap_two_surjective :
    Function.Surjective (nativeCapKernelRegularMap 2) :=
  homologyTwo_subsingleton_iff_nativeCapKernel_surjective.mp homologyTwo_subsingleton

/-- The full original signed second attachment map is onto. -/
theorem starLeft_two_surjective : Function.Surjective (starLeftHomologyMap 2) :=
  starLeft_surjective_of_nativeCapKernel 2 nativeCapKernelRegularMap_two_surjective

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.SecondDegree
