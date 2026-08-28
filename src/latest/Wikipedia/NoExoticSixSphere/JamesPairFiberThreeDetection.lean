import Wikipedia.NoExoticSixSphere.JamesPairFiberThreeDescent
import Wikipedia.NoExoticSixSphere.RelativeNormalizationFiberDetection

/-!
# The actual James inclusion fiber has trivial third homology and homotopy

All assumptions of the ending-path detection argument are discharged.
The original fourth relative homology is zero and surjects onto the
original third fiber homology. The actual third Hurewicz isomorphism
then annihilates native third homotopy at every point. The actual source
inclusion is surjective on fourth homotopy by the original fiber sequence.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.JamesSphere.ThreeSkeletonNormalization

open ComparisonCylinder

attribute [local instance] PairNormalization.cylinderSimplyConnected
attribute [local instance] PairNormalization.sourceSimplyConnected
attribute [local instance] fiberSimplyConnected fiberPiTwo

theorem fiberHomologyMap_surjective (n : ℕ) (a : sourceImage (n + 2)) :
    Function.Surjective (fiberHomologyMap n a) :=
  (normalizationData n a).fiberHomologyMap_surjective_three

theorem fiber_homologyThree_eq_zero (n : ℕ) (a : sourceImage (n + 2))
    (z : SingularHomology (SourceFiber (n + 2) a) 3) : z = 0 := by
  obtain ⟨c, rfl⟩ := fiberHomologyMap_surjective n a z
  exact fiberHomologyMap_apply_eq_zero n a c

theorem fiber_homologyThree_subsingleton (n : ℕ) (a : sourceImage (n + 2)) :
    Subsingleton (SingularHomology (SourceFiber (n + 2) a) 3) :=
  ⟨fun z w ↦ (fiber_homologyThree_eq_zero n a z).trans (fiber_homologyThree_eq_zero n a w).symm⟩

theorem fiber_piThree_subsingleton (n : ℕ) (a : sourceImage (n + 2))
    (p : SourceFiber (n + 2) a) : Subsingleton (π_ 3 (SourceFiber (n + 2) a) p) := by
  let := sourceFiber_simplyConnected n a
  let := PairNormalization.fiber_piTwo_subsingleton n a p
  let := fiber_homologyThree_subsingleton n a
  exact (ThirdHurewicz.hurewiczPi3Equiv p).injective.subsingleton

theorem inclusion_piFour_surjective (n : ℕ) (a : sourceImage (n + 2)) :
    Function.Surjective
      (HigherHomotopy.map (N := Fin 4) (subtypeInclusion (sourceImage (n + 2)))
        (y := a) rfl) := by
  let : Subsingleton (π_ 3
      (HomotopyFiber.Space (subtypeInclusion (sourceImage (n + 2)))
        ((subtypeInclusion (sourceImage (n + 2))) a))
      (HomotopyFiber.basepoint (subtypeInclusion (sourceImage (n + 2))) a)) :=
    fiber_piThree_subsingleton n a (sourceFiberBasepoint (n + 2) a)
  intro z
  exact (HomotopyFiber.boundary_eq_const_iff_exists_source_class 3
    (subtypeInclusion (sourceImage (n + 2))) a z).mp (Subsingleton.elim _ _)

theorem inclusion_piThree_bijective (n : ℕ) (a : sourceImage (n + 2)) :
    Function.Bijective
      (HigherHomotopy.map (N := Fin 3) (subtypeInclusion (sourceImage (n + 2)))
        (y := a) rfl) := by
  let : Subsingleton (π_ 3
      (HomotopyFiber.Space (subtypeInclusion (sourceImage (n + 2)))
        ((subtypeInclusion (sourceImage (n + 2))) a))
      (HomotopyFiber.basepoint (subtypeInclusion (sourceImage (n + 2))) a)) :=
    fiber_piThree_subsingleton n a (sourceFiberBasepoint (n + 2) a)
  exact ⟨HomotopyFiberConnectivity.map_injective_of_fiber_subsingleton 3
    (subtypeInclusion (sourceImage (n + 2))) a, PairNormalization.inclusion_piThree_surjective n a⟩

theorem transgression_three_injective (n : ℕ) (a : sourceImage (n + 2)) :
    Function.Injective (RelativeFiberHomology.transgression (sourceImage (n + 2)) a 3) := by
  let := fiber_homologyThree_subsingleton n a
  exact Function.injective_of_subsingleton _

end NoExoticSixSphere.JamesSphere.ThreeSkeletonNormalization
