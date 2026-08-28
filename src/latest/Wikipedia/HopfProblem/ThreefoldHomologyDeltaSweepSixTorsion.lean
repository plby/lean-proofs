import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepCoordinates
import Wikipedia.HopfProblem.ThreefoldHomologySecondCyclic

/-!
# The actual global second homology is killed by six

The original regular delta sweep gives the relation minus six in the
proved primitive cyclic marking. Its genuine global vanishing therefore
annihilates six times the actual generator. The already established
surjectivity from that marked fibre extends this relation to every
native singular second-homology class. This makes no torsion-freeness
or Poincare-duality assumption and does not yet claim this group is zero.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep

open TrianglePeriodFamily SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomologyPontryagin

/-- The actual delta-first gamma sweep kills six in the original
primitive integral cyclic map to global second homology. -/
theorem homologyTwoCyclicMap_six_eq_zero : SecondDegree.homologyTwoCyclicMap 6 = 0 := by
  have h := normalizedFibre_delta_product_eq_zero
    (FlatTorus.singularH1Equiv.symm ![1, 0, 0, 0])
  change singularHomologyMap CapElimination.regularFibreIntoSpace 2
    (product11 RealTorus₄ (FlatTorus.singularH1Equiv.symm deltaLattice)
      (FlatTorus.singularH1Equiv.symm ![1, 0, 0, 0])) = 0 at h
  rw [SecondDegree.regularFibre_homologyTwo_coordinates, deltaLattice,
    flat_delta_product11_coordinates] at h
  have hn : SecondDegree.homologyTwoCyclicMap (-6) = 0 := by simpa using h
  simpa only [map_neg, neg_eq_zero] using hn

/-- Six times the original positive `u ∧ w` generator vanishes. -/
theorem six_zsmul_homologyTwoGenerator : (6 : ℤ) • SecondDegree.homologyTwoGenerator = 0 := by
  rw [← SecondDegree.homologyTwoCyclicMap_eq_smul]
  exact homologyTwoCyclicMap_six_eq_zero

/-- Every native singular second-homology class is annihilated by six,
using actual cyclic surjectivity and the actual global sweep relation. -/
theorem six_zsmul_homologyTwo (a : SingularHomology Space 2) : (6 : ℤ) • a = 0 := by
  obtain ⟨z, rfl⟩ := SecondDegree.homologyTwoCyclicMap_surjective a
  rw [SecondDegree.homologyTwoCyclicMap_eq_smul, smul_comm,
    six_zsmul_homologyTwoGenerator]
  exact @zsmul_zero (SingularHomology Space 2) _ z

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep
