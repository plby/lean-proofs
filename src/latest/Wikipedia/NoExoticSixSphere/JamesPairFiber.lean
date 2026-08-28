import Wikipedia.NoExoticSixSphere.JamesComparisonConnectivity
import Wikipedia.NoExoticSixSphere.HomotopyFiberConnectivity
import Wikipedia.NoExoticSixSphere.RelativeFiberConnecting

/-!
# The fiber and evaluation-prism map for the original James cylinder pair

The subspace inclusion's own homotopy fiber is simply connected, using
the original inclusion homology map and the checked second Hurewicz
isomorphism. Composing that fiber's native second Hurewicz map with
the actual evaluation prism gives the degree-three obstruction map.
The later `JamesPairFiberDetection` module proves injectivity of this map.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.JamesSphere.ComparisonCylinder

abbrev SourceFiber (n : ℕ) (a : sourceImage n) := RelativeFiberHomology.Fiber (sourceImage n) a

def sourceFiberBasepoint (n : ℕ) (a : sourceImage n) : SourceFiber n a :=
  HomotopyFiber.basepoint (subtypeInclusion (sourceImage n)) a

theorem sourceFiber_simplyConnected (n : ℕ) (a : sourceImage (n + 2)) :
    SimplyConnectedSpace (SourceFiber (n + 2) a) := by
  let := sourceImage_simplyConnected n
  let := cylinder_simplyConnected n
  let f := subtypeInclusion (sourceImage (n + 2))
  apply HomotopyFiberConnectivity.simplyConnectedSpace f a
  have he : HigherHomotopy.map (N := Fin 2) f (y := a) rfl =
      SecondHurewicz.homotopyMap f a := by
    funext c
    refine Quotient.inductionOn c fun p ↦ ?_
    rfl
  rw [he]
  exact (HomologyEquivalence.piTwo_bijective f
    (source_inclusion_homology_bijective (n + 2) 2 (by omega)) a).surjective

def prismHurewiczThree (n : ℕ) (a : sourceImage n) :
    Additive (π_ 2 (SourceFiber n a) (sourceFiberBasepoint n a)) →ₗ[ℤ]
        RelativeSingularHomology.Homology (sourceImage n) 3 :=
  (RelativeFiberHomology.transgression (sourceImage n) a 2).comp
    (SecondHurewicz.hurewiczMap (sourceFiberBasepoint n a))

theorem prismHurewiczThree_mk (n : ℕ) (a : sourceImage n)
    (p : GenLoop (Fin 2) (SourceFiber n a) (sourceFiberBasepoint n a)) :
    prismHurewiczThree n a (Additive.ofMul (⟦p⟧ : π_ 2 (SourceFiber n a)
      (sourceFiberBasepoint n a))) =
        RelativeFiberHomology.transgression (sourceImage n) a 2
          (SecondHurewicz.squareHomologyClass p) := rfl

end NoExoticSixSphere.JamesSphere.ComparisonCylinder
