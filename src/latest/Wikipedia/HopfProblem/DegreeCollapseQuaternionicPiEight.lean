import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicOrthogonalReduction
import Wikipedia.HopfProblem.DegreeCollapseRankSixThirdVanishing

/-!
# The eighth native homotopy group of Sp(2) is zero

Use the original matrix stabilizations, three Bott comparisons, and the
balanced-frame connecting isomorphism to reach pi4(O(16)). Its vanishing
comes from the actual rank-six spinor contraction on the three-sphere.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicPiEight

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.HomotopyGroupsOfSpheres QuaternionicColumns
open QuaternionicSymmetricMatrices

def firstBott (n : ℕ) (hn : 8 < n) :
    π_ 8 QuaternionicFibration.SpTwo 1 ≃*
      π_ 7 (ComplexStructures.Space n) (ComplexStructures.standard n) := by
  have e := stabilizationInRangeIterate 2 8 (by decide) (n - 1)
  have hdim : 2 + (n - 1) = n + 1 := by omega
  rw [hdim] at e
  exact e.trans (Polygon.bottMatrixDegreeShiftMulEquiv 7
    (ComplexStructures.standard n) hn).symm

def secondBott (n : ℕ) (hn : 8 < n) :
    π_ 8 QuaternionicFibration.SpTwo 1 ≃*
      π_ 6 (AnticommutingStructures.Space (ComplexStructures.standard n))
        (AnticommutingStructures.standard n) :=
  (firstBott n hn).trans
    (SecondPaths.bottDegreeShiftMulEquiv 6 (AnticommutingStructures.standard n) (by omega)).symm

def symmetricCoordinates (n : ℕ) (hn : 8 < n) :
    π_ 8 QuaternionicFibration.SpTwo 1 ≃*
      π_ 6 (SpecialSpace (Fin (n + 1))) specialIdentity :=
  ((secondBott n hn).trans (symmetricUnitaryCoordinatesMulEquiv n 6)).trans
    (specialInclusionMulEquiv n 4).symm

def thirdBott (n : ℕ) (hn : 6 < n) :
    π_ 8 QuaternionicFibration.SpTwo 1 ≃*
      π_ 5 (BalancedRealInvolutions.Space n) (BalancedRealInvolutions.standard n) :=
  ((symmetricCoordinates (2 * n - 1) (by omega)).trans
    (specialReindexHomotopyMulEquiv (balancedIndexEquiv n (by omega)) 6)).trans
      (BalancedRealInvolutions.bottDegreeShiftMulEquiv n 5 (by omega)).symm

def orthogonalComparison (n : ℕ) (hn : 6 < n) :
    π_ 8 QuaternionicFibration.SpTwo 1 ≃* π_ 4 (OrthogonalOperators n) 1 :=
  (thirdBott n hn).trans
    (BalancedRealInvolutions.FrameProjection.balancedOrthogonalMulEquiv n 4 (by omega))

theorem piEightSpTwo_subsingleton : Subsingleton (π_ 8 QuaternionicFibration.SpTwo 1) := by
  let := RankSixThirdVanishing.piFourOrthogonalSixteen_subsingleton
  exact (orthogonalComparison 16 (by decide)).injective.subsingleton

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicPiEight
