import Wikipedia.NoExoticSixSphere.JamesPairFiberDescent
import Wikipedia.NoExoticSixSphere.RelativeFiberDetection

/-!
# The James source-inclusion fiber has trivial second homology and homotopy

The constructed right inverse to the descended map proves that the
original fiber's second homology is a quotient of the already vanishing
relative third homology. The actual second Hurewicz isomorphism then
annihilates its native second homotopy group. The original inclusion's
third-homotopy map is consequently surjective by the actual fiber sequence.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.JamesSphere.PairNormalization

open ComparisonCylinder

attribute [local instance] cylinderSimplyConnected sourceSimplyConnected

theorem fiberHomologyMap_surjective (n : ℕ) (a : sourceImage (n + 2)) :
    Function.Surjective (fiberHomologyMap n a) :=
  RelativeNormalizedFiberClasses.homologyMap_surjective (sourceImage (n + 2)) a
    (inclusion_piTwo_surjective n a)

theorem fiber_homologyTwo_eq_zero (n : ℕ) (a : sourceImage (n + 2))
    (z : SingularHomology (SourceFiber (n + 2) a) 2) : z = 0 := by
  obtain ⟨c, rfl⟩ := fiberHomologyMap_surjective n a z
  exact fiberHomologyMap_apply_eq_zero n a c

theorem fiber_homologyTwo_subsingleton (n : ℕ) (a : sourceImage (n + 2)) :
    Subsingleton (SingularHomology (SourceFiber (n + 2) a) 2) :=
  ⟨fun z w ↦ (fiber_homologyTwo_eq_zero n a z).trans (fiber_homologyTwo_eq_zero n a w).symm⟩

theorem fiber_piTwo_subsingleton (n : ℕ) (a : sourceImage (n + 2))
    (p : SourceFiber (n + 2) a) : Subsingleton (π_ 2 (SourceFiber (n + 2) a) p) := by
  let := sourceFiber_simplyConnected n a
  let := fiber_homologyTwo_subsingleton n a
  exact (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv p).injective.subsingleton

theorem inclusion_piThree_surjective (n : ℕ) (a : sourceImage (n + 2)) :
    Function.Surjective
      (HigherHomotopy.map (N := Fin 3) (subtypeInclusion (sourceImage (n + 2)))
        (y := a) rfl) := by
  let : Subsingleton (π_ 2
      (HomotopyFiber.Space (subtypeInclusion (sourceImage (n + 2)))
        ((subtypeInclusion (sourceImage (n + 2))) a))
      (HomotopyFiber.basepoint (subtypeInclusion (sourceImage (n + 2))) a)) :=
    fiber_piTwo_subsingleton n a (sourceFiberBasepoint (n + 2) a)
  intro z
  exact (HomotopyFiber.boundary_eq_const_iff_exists_source_class 2
    (subtypeInclusion (sourceImage (n + 2))) a z).mp (Subsingleton.elim _ _)

theorem transgression_injective (n : ℕ) (a : sourceImage (n + 2)) :
    Function.Injective (RelativeFiberHomology.transgression (sourceImage (n + 2)) a 2) := by
  let := fiber_homologyTwo_subsingleton n a
  exact Function.injective_of_subsingleton _

theorem prismHurewiczThree_injective (n : ℕ) (a : sourceImage (n + 2)) :
    Function.Injective (prismHurewiczThree (n + 2) a) := by
  let := fiber_piTwo_subsingleton n a (sourceFiberBasepoint (n + 2) a)
  exact Function.injective_of_subsingleton _

end NoExoticSixSphere.JamesSphere.PairNormalization
