import Wikipedia.HopfProblem.DegreeCollapseRankSixComponents
import Wikipedia.HopfProblem.DegreeCollapseFirstStemGroup

/-!
# The actual fifth homotopy group of the three-sphere

The original quaternionic fiber inclusion identifies pi5(S3) with
pi5(Sp2). Three actual Bott comparisons and the balanced-frame
connecting map reduce the latter to pi1(O6). The degree-zero first
Bott comparison and the proved Pfaffian component calculation give
exactly two classes. No eta-square generator is identified here.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.SecondStemReduction

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.HomotopyGroupsOfSpheres QuaternionicColumns QuaternionicSymmetricMatrices

def firstBott (n : ℕ) (hn : 5 < n) :
    π_ 5 QuaternionicFibration.SpTwo 1 ≃*
      π_ 4 (ComplexStructures.Space n) (ComplexStructures.standard n) := by
  have e := stabilizationInRangeIterate 2 5 (by decide) (n - 1)
  have hdim : 2 + (n - 1) = n + 1 := by omega
  rw [hdim] at e
  exact e.trans (Polygon.bottMatrixDegreeShiftMulEquiv 4
    (ComplexStructures.standard n) hn).symm

def secondBott (n : ℕ) (hn : 5 < n) :
    π_ 5 QuaternionicFibration.SpTwo 1 ≃*
      π_ 3 (AnticommutingStructures.Space (ComplexStructures.standard n))
        (AnticommutingStructures.standard n) :=
  (firstBott n hn).trans
    (SecondPaths.bottDegreeShiftMulEquiv 3 (AnticommutingStructures.standard n) (by omega)).symm

def symmetricCoordinates (n : ℕ) (hn : 5 < n) :
    π_ 5 QuaternionicFibration.SpTwo 1 ≃*
      π_ 3 (SpecialSpace (Fin (n + 1))) specialIdentity :=
  ((secondBott n hn).trans (symmetricUnitaryCoordinatesMulEquiv n 3)).trans
    (specialInclusionMulEquiv n 1).symm

def thirdBott (n : ℕ) (hn : 3 < n) :
    π_ 5 QuaternionicFibration.SpTwo 1 ≃*
      π_ 2 (BalancedRealInvolutions.Space n) (BalancedRealInvolutions.standard n) :=
  ((symmetricCoordinates (2 * n - 1) (by omega)).trans
    (specialReindexHomotopyMulEquiv (balancedIndexEquiv n (by omega)) 3)).trans
      (BalancedRealInvolutions.bottDegreeShiftMulEquiv n 2 hn).symm

def orthogonalComparison : π_ 5 QuaternionicFibration.SpTwo 1 ≃*
    π_ 1 (OrthogonalOperators 6) 1 :=
  (thirdBott 6 (by decide)).trans
    (BalancedRealInvolutions.FrameProjection.balancedOrthogonalMulEquiv 6 1 (by decide))

def fiberInclusionEquiv :
    π_ 5 QuaternionicFibration.northSubgroup 1 ≃* π_ 5 QuaternionicFibration.SpTwo 1 := by
  let := unitColumn_homotopy_subsingleton 1 5 (by decide) (axisColumn 0)
  let := unitColumn_homotopy_subsingleton 1 6 (by decide) (axisColumn 0)
  exact (pointedHomeomorphMulEquiv FirstStemReduction.northAxisHomeomorph 1 1
    FirstStemReduction.northAxisHomeomorph_one).trans (inclusionMulEquiv (0 : Fin 2) 5)

def threeSphereComparison : π_ 5 (NoExoticSixSphere.Sphere 3) (spherePole 3) ≃*
    π_ 5 QuaternionicFibration.SpTwo 1 :=
  (pointedHomeomorphMulEquiv QuaternionicFibration.fiberSphereHomeomorph 1 (spherePole 3)
    QuaternionicClutching.fiberSphereHomeomorph_one).symm.trans fiberInclusionEquiv

def threeSphereClasses : π_ 5 (NoExoticSixSphere.Sphere 3) (spherePole 3) ≃ Bool :=
  (threeSphereComparison.toEquiv.trans orthogonalComparison.toEquiv).trans
    RankSixComponents.orthogonalSixLoops

theorem card : Nat.card (π_ 5 (NoExoticSixSphere.Sphere 3) (spherePole 3)) = 2 := by
  simpa only [Nat.card_eq_fintype_card, Fintype.card_bool] using Nat.card_congr threeSphereClasses

def groupEquiv : π_ 5 (NoExoticSixSphere.Sphere 3) (spherePole 3) ≃* Multiplicative (ZMod 2) :=
  mulEquivOfPrimeCardEq (p := 2) card (by simp)

theorem pow_two (c : π_ 5 (NoExoticSixSphere.Sphere 3) (spherePole 3)) : c ^ 2 = 1 := by
  apply groupEquiv.injective
  rw [map_pow, map_one]
  exact (show ∀ z : Multiplicative (ZMod 2), z ^ 2 = 1 from by decide) _

end Wikipedia.HopfProblem.DegreeCollapse.SecondStemReduction
