import Wikipedia.HopfProblem.ThreefoldHomologyThirdAttachment

/-!
# Vanishing of the actual third and fourth integral homology

The genuine full positive reference relation has coefficient one.
The original native third-homology cokernel and fourth-homology kernel
therefore both vanish over the integers.  No duality, sphere-recognition
theorem, or hypothetical attachment map is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.ThirdDegree

open SingularMayerVietoris CategoryTheory.Limits

/-- The original positive third-fibre generator vanishes in actual global homology. -/
theorem homologyThreeGenerator_eq_zero : homologyThreeGenerator = 0 := by
  have h := homologyThreeCyclicMap_referenceFibreCoefficient
  rw [referenceFibreCoefficient_eq_one] at h
  exact h

/-- Unconditional vanishing of actual native integral third homology. -/
theorem homologyThree_subsingleton : Subsingleton (SingularHomology Space 3) :=
  homologyThree_subsingleton_iff_referenceFibreCoefficient_isUnit.mpr
    referenceFibreCoefficient_isUnit

theorem homologyThree_eq_zero (a : SingularHomology Space 3) : a = 0 :=
  homologyThree_subsingleton.elim _ _

theorem homologyThree_isZero : IsZero (SingularHomology Space 3) := by
  have := homologyThree_subsingleton
  exact ModuleCat.isZero_of_subsingleton _

theorem homologyThree_finrank : Module.finrank ℤ (SingularHomology Space 3) = 0 := by
  have := homologyThree_subsingleton
  exact Module.finrank_zero_of_subsingleton

theorem rationalBetti_three : Finiteness.rationalBetti 3 = 0 := by
  have := homologyThree_subsingleton
  exact Module.finrank_zero_of_subsingleton

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.ThirdDegree

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FourthDegree

open SingularMayerVietoris CategoryTheory.Limits

/-- Unconditional vanishing of actual native integral fourth homology. -/
theorem homologyFour_subsingleton : Subsingleton (SingularHomology Space 4) :=
  ThirdDegree.homologyFour_subsingleton_iff_referenceFibreCoefficient_ne_zero.mpr
    ThirdDegree.referenceFibreCoefficient_isUnit.ne_zero

theorem homologyFour_eq_zero (a : SingularHomology Space 4) : a = 0 :=
  homologyFour_subsingleton.elim _ _

theorem homologyFour_isZero : IsZero (SingularHomology Space 4) := by
  have := homologyFour_subsingleton
  exact ModuleCat.isZero_of_subsingleton _

theorem homologyFour_finrank : Module.finrank ℤ (SingularHomology Space 4) = 0 := by
  have := homologyFour_subsingleton
  exact Module.finrank_zero_of_subsingleton

theorem rationalBetti_four : Finiteness.rationalBetti 4 = 0 := by
  have := homologyFour_subsingleton
  exact Module.finrank_zero_of_subsingleton

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FourthDegree
