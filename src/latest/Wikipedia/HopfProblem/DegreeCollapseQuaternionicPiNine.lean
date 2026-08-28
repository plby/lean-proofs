import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicOrthogonalReduction
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicExactness
import Wikipedia.NoExoticSixSphere.NormalFraming
import Wikipedia.HopfProblem.OrbitPairSphereNullhomotopyCriterion

/-!
# The ninth native homotopy group of Sp(2) is zero

The original stable matrix inclusions, three Bott comparisons, and the
balanced-frame connecting isomorphism reduce pi9(Sp(2)) to pi5(O(16)).
The already constructed five-sphere contractions prove the latter
vanishing through the actual disk and cube comparison.

Consequently the connecting map pi10(S7) -> pi9(S3) in the original
quaternionic two-frame fibration is surjective. This supplies a finite
source for the remaining unstable contribution in the sixth-stem
calculation, without assuming a numerical value for pi9(S3).
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicPiNine

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.HomotopyGroupsOfSpheres QuaternionicColumns
open QuaternionicSymmetricMatrices

def firstBott (n : ℕ) (hn : 9 < n) :
    π_ 9 QuaternionicFibration.SpTwo 1 ≃*
      π_ 8 (ComplexStructures.Space n) (ComplexStructures.standard n) := by
  have e := stabilizationInRangeIterate 2 9 (by decide) (n - 1)
  have hdim : 2 + (n - 1) = n + 1 := by omega
  rw [hdim] at e
  exact e.trans (Polygon.bottMatrixDegreeShiftMulEquiv 8
    (ComplexStructures.standard n) hn).symm

def secondBott (n : ℕ) (hn : 9 < n) :
    π_ 9 QuaternionicFibration.SpTwo 1 ≃*
      π_ 7 (AnticommutingStructures.Space (ComplexStructures.standard n))
        (AnticommutingStructures.standard n) :=
  (firstBott n hn).trans
    (SecondPaths.bottDegreeShiftMulEquiv 7 (AnticommutingStructures.standard n) (by omega)).symm

def symmetricCoordinates (n : ℕ) (hn : 9 < n) :
    π_ 9 QuaternionicFibration.SpTwo 1 ≃*
      π_ 7 (SpecialSpace (Fin (n + 1))) specialIdentity :=
  ((secondBott n hn).trans (symmetricUnitaryCoordinatesMulEquiv n 7)).trans
    (specialInclusionMulEquiv n 5).symm

def thirdBott (n : ℕ) (hn : 7 < n) :
    π_ 9 QuaternionicFibration.SpTwo 1 ≃*
      π_ 6 (BalancedRealInvolutions.Space n) (BalancedRealInvolutions.standard n) :=
  ((symmetricCoordinates (2 * n - 1) (by omega)).trans
    (specialReindexHomotopyMulEquiv (balancedIndexEquiv n (by omega)) 7)).trans
      (BalancedRealInvolutions.bottDegreeShiftMulEquiv n 6 (by omega)).symm

def orthogonalComparison (n : ℕ) (hn : 7 < n) :
    π_ 9 QuaternionicFibration.SpTwo 1 ≃* π_ 5 (OrthogonalOperators n) 1 :=
  (thirdBott n hn).trans
    (BalancedRealInvolutions.FrameProjection.balancedOrthogonalMulEquiv n 5 (by omega))

theorem fifthOrthogonalSixteen_subsingleton :
    Subsingleton (π_ 5 (OrthogonalOperators 16) 1) :=
  OrbitPair.SphereNullhomotopy.pi_subsingleton_of_sphere_nullhomotopies
    (by decide : 0 < 5) fiveSphereOrthogonalSixteenVanishing 1

theorem piNineSpTwo_subsingleton : Subsingleton (π_ 9 QuaternionicFibration.SpTwo 1) := by
  let := fifthOrthogonalSixteen_subsingleton
  exact (orthogonalComparison 16 (by decide)).injective.subsingleton

theorem connecting_nine_surjective :
    Function.Surjective (QuaternionicFibration.connecting 9) := by
  let := piNineSpTwo_subsingleton
  intro a
  exact (QuaternionicFibration.connecting_range_eq_kernel a).mpr (Subsingleton.elim _ _)

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicPiNine

