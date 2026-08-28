import Wikipedia.NoExoticSixSphere.JamesSphereAttachingSphereLoopHomotopy
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# The corrected attaching family and actual commutator induce the same homology map

Normalize the original Moore meridians, retaining the target coordinate
reordering, and compose with the descended source-correction homotopy.
The resulting equality concerns the actual singular-homology maps on
the product of spheres, in every degree. The previously constructed
smash commutator has the same map there. No native smash-class equality
or numerical attaching coefficient is asserted by this comparison.
-/

noncomputable section

open scoped Topology unitInterval
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

def normalizedSphereCommutator (n : ℕ) :
    C(SphereMooreCommutator.Parameter n, Path (spherePole (n + 1)) (spherePole (n + 1))) :=
  (reorderPaths n).comp (Moore.Loop.normalizationMap.comp
    (SphereMooreCommutator.commutator n (MeridianCommutator.meridians n)
      (MeridianCommutator.meridians n)))

theorem sphereLoopPair_point (n : ℕ) :
    SphereMooreCommutator.pairMap n (MeridianCommutator.meridians n)
      (MeridianCommutator.meridians n) (SphereMooreCommutator.point n) = (1, 1) :=
  Prod.ext (mooreGenerator_pole n) (mooreGenerator_pole n)

def normalizationSphereHomotopy (n : ℕ) :
    (normalizedSphereCommutator n).HomotopyRel (originalSphereLoops n)
      {SphereMooreCommutator.point n} where
  toFun u := reorderPaths n (Moore.Loop.commutatorNormalizationHomotopy
    (u.1, SphereMooreCommutator.pairMap n (MeridianCommutator.meridians n)
      (MeridianCommutator.meridians n) u.2))
  continuous_toFun := (reorderPaths n).continuous.comp
    (Moore.Loop.commutatorNormalizationHomotopy.continuous.comp
      (continuous_fst.prodMk ((SphereMooreCommutator.pairMap n
        (MeridianCommutator.meridians n) (MeridianCommutator.meridians n)).continuous.comp
          continuous_snd)))
  map_zero_left v := congrArg (reorderPaths n)
    (Moore.Loop.commutatorNormalizationHomotopy.map_zero_left _)
  map_one_left v := congrArg (reorderPaths n)
    (Moore.Loop.commutatorNormalizationHomotopy.map_one_left _)
  prop' := by
    intro s v hv
    rcases Set.mem_singleton_iff.mp hv with rfl
    change reorderPaths n (Moore.Loop.commutatorNormalizationHomotopy
      (s, SphereMooreCommutator.pairMap n (MeridianCommutator.meridians n)
        (MeridianCommutator.meridians n) (SphereMooreCommutator.point n))) =
      reorderPaths n (Moore.Loop.toPath (Moore.Loop.commutatorMap
        (SphereMooreCommutator.pairMap n (MeridianCommutator.meridians n)
          (MeridianCommutator.meridians n) (SphereMooreCommutator.point n))))
    rw [sphereLoopPair_point]
    exact congrArg (reorderPaths n)
      (Moore.Loop.commutatorNormalizationHomotopy.prop s (1, 1) (Set.mem_singleton _))

def normalizedToCorrectedHomotopy (n : ℕ) (hn : 0 < n) :
    (normalizedSphereCommutator n).HomotopyRel (correctedSphereLoops n hn)
      {SphereMooreCommutator.point n} :=
  (normalizationSphereHomotopy n).trans (sphereLoopHomotopy n hn)

def normalizedSmashSphere (n : ℕ) :
    C(Sphere (n + n), Path (spherePole (n + 1)) (spherePole (n + 1))) :=
  (reorderPaths n).comp (Moore.Loop.normalizationMap.comp (MeridianCommutator.sphereMap n))

def smashSphereLoops (n : ℕ) :
    C(SphereMooreCommutator.Parameter n, Path (spherePole (n + 1)) (spherePole (n + 1))) :=
  (normalizedSmashSphere n).comp (SecondStage.arrayPairing n)

def normalizedToSmashHomotopy (n : ℕ) :
    (normalizedSphereCommutator n).HomotopyRel (smashSphereLoops n)
      {SphereMooreCommutator.point n} :=
  ((MeridianCommutator.factorHomotopy n).compContinuousMap
    Moore.Loop.normalizationMap).compContinuousMap (reorderPaths n)

theorem corrected_homology_eq_commutator (n : ℕ) (hn : 0 < n) (d : ℕ) :
    singularHomologyMap (correctedSphereLoops n hn) d =
      singularHomologyMap (normalizedSphereCommutator n) d :=
  (homotopy_homologyMap (normalizedToCorrectedHomotopy n hn).toHomotopy d).symm

theorem corrected_homology_eq_smash (n : ℕ) (hn : 0 < n) (d : ℕ) :
    singularHomologyMap (correctedSphereLoops n hn) d =
      singularHomologyMap (smashSphereLoops n) d :=
  (corrected_homology_eq_commutator n hn d).trans
    (homotopy_homologyMap (normalizedToSmashHomotopy n).toHomotopy d)

end NoExoticSixSphere.JamesSphere.AttachingSquare
