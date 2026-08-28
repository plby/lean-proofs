import Wikipedia.NoExoticSixSphere.JamesComparisonRelativeHomology
import Wikipedia.NoExoticSixSphere.JamesSphereSimplyConnected
import Wikipedia.NoExoticSixSphere.HomologyEquivalencePiTwo
import Wikipedia.HopfProblem.SphereHomologySimplyConnectedPiTwo
import Wikipedia.HopfProblem.OrbitPairLoopSpaceConnectivity

/-!
# Connectivity and the native second-homotopy James comparison

Both the actual James space and the native loop space are simply
connected for sphere dimension at least two. These facts also hold for
the genuine mapping cylinder and its source image. Naturality of the
proved second Hurewicz isomorphism gives an isomorphism on the actual
second homotopy groups, at every source basepoint. Higher homotopy
comparison is not asserted here.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem OrbitPair

namespace NoExoticSixSphere.JamesSphere.ComparisonCylinder

theorem loops_simplyConnected (n : ℕ) : SimplyConnectedSpace (CoverMaps.Loops (n + 2)) :=
  loopSpace_simplyConnected (spherePole (n + 3))
    (SphereHomology.unitSphere_piTwo_subsingleton n (spherePole (n + 3)))

theorem cylinder_simplyConnected (n : ℕ) : SimplyConnectedSpace (Cylinder (n + 2)) := by
  let := loops_simplyConnected n
  exact (MappingCylinder.projectionEquiv (comparison (n + 2))).simplyConnectedSpace

theorem sourceImage_simplyConnected (n : ℕ) : SimplyConnectedSpace (sourceImage (n + 2)) := by
  let := JamesSphere.simplyConnectedSpace n
  exact (MappingCylinderHomology.sourceHomeomorph (comparison (n + 2))).symm.toHomotopyEquiv
    |>.simplyConnectedSpace

theorem comparison_piTwo_bijective (n : ℕ) (x : WordHomology.Words (n + 2)) :
    Function.Bijective (SecondHurewicz.homotopyMap (loopComparison (n + 2)) x) := by
  let := JamesSphere.simplyConnectedSpace n
  let := loops_simplyConnected n
  exact HomologyEquivalence.piTwo_bijective (loopComparison (n + 2))
    (HomologyComparison.comparison_homology_bijective_of_pos (n + 2) 2 (by omega)) x

def comparisonPiTwoEquiv (n : ℕ) (x : WordHomology.Words (n + 2)) :
    π_ 2 (WordHomology.Words (n + 2)) x ≃*
      π_ 2 (CoverMaps.Loops (n + 2)) (loopComparison (n + 2) x) :=
  MulEquiv.ofBijective (SecondHurewicz.homotopyMap (loopComparison (n + 2)) x)
    (comparison_piTwo_bijective n x)

theorem comparisonPiTwoEquiv_apply (n : ℕ) (x : WordHomology.Words (n + 2))
    (a : π_ 2 (WordHomology.Words (n + 2)) x) :
    comparisonPiTwoEquiv n x a = SecondHurewicz.homotopyMap (loopComparison (n + 2)) x a := rfl

end NoExoticSixSphere.JamesSphere.ComparisonCylinder
