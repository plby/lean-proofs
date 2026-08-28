import Wikipedia.NoExoticSixSphere.JamesSphereFirstStageFiberConnectivity
import Wikipedia.NoExoticSixSphere.HomotopyFiberSourceHomeomorph
import Wikipedia.NoExoticSixSphere.RelativeFiberHomologyConnectivity

/-!
# The original fiber-to-quotient map on its first potentially nonzero homology

The genuine pair quotient induces relative-homology isomorphisms in all
degrees. Both pairs have the required lower fiber connectivity at every
basepoint. The checked transgression comparison therefore gives fiber
homology isomorphisms through degree `2n - 1`. Actual source and point
fiber homeomorphisms identify the resulting map with the original
path-composition map `toLoops`, not an independently chosen isomorphism.

This reaches the first potentially nonzero homology degree. It does not
prove the full metastable homology or native homotopy comparison.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology OrbitPair

namespace NoExoticSixSphere.JamesSphere.FiberQuotient

def pairSourcePoint (n : ℕ) : James.stage (spherePole n) 1 :=
  FirstStage.homeomorph n (spherePole n)

def pairTargetPoint (n : ℕ) : ({FirstStageQuotient.basepoint n} :
    Set (FirstStageQuotient.Space n)) := ⟨FirstStageQuotient.basepoint n, rfl⟩

def pairMap (n : ℕ) :
    C(RelativeFiberHomology.Fiber (James.stage (spherePole n) 1) (pairSourcePoint n),
      RelativeFiberHomology.Fiber ({FirstStageQuotient.basepoint n} :
        Set (FirstStageQuotient.Space n)) (pairTargetPoint n)) :=
  RelativeFiberMap.map (FirstStageQuotient.quotientMap n)
    (FirstStageQuotient.quotientMap_mapsTo_point n) (pairSourcePoint n) (pairTargetPoint n)
    (quotient_inclusion n (spherePole n))

theorem pairMap_homology_bijective (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d)
    (hdn : d + 1 ≤ 2 * n) : Function.Bijective (singularHomologyMap (pairMap n) d) := by
  let : SimplyConnectedSpace (James.Space (Sphere n) (spherePole n)) := by
    have he : n = (n - 2) + 2 := by omega
    rw [he]
    exact JamesSphere.simplyConnectedSpace (n - 2)
  let : SimplyConnectedSpace (James.stage (spherePole n) 1) := by
    have he : n = (n - 2) + 2 := by omega
    rw [he]
    exact JamesSphere.stage_simplyConnected (n - 2) 1
  let := FirstStageQuotient.simplyConnected_of_two_le n hn
  have hb := RelativeNormalization.fiber_homology_bijective_of_connectivity
    (James.stage (spherePole n) 1)
    ({FirstStageQuotient.basepoint n} : Set (FirstStageQuotient.Space n))
    (pairSourcePoint n) (pairTargetPoint n) (FirstStageQuotient.quotientMap n)
    (FirstStageQuotient.quotientMap_mapsTo_point n) (quotient_inclusion n (spherePole n))
    (d - 2)
    (fun k hk hkd a p ↦ FirstStage.fiber_pi n k hn hk (by omega) a p)
    (fun k hk hkd a p ↦ FirstStageQuotient.point_fiber_pi n k hn hk (by omega) a p)
    (FirstStageQuotient.quotient_relative_homology_bijective n (d - 2 + 3))
  change Function.Bijective (singularHomologyMap (pairMap n) (d - 2 + 2)) at hb
  rwa [Nat.sub_add_cancel hd] at hb

def sourceHomeomorph (n : ℕ) : Fiber n ≃ₜ
    RelativeFiberHomology.Fiber (James.stage (spherePole n) 1) (pairSourcePoint n) :=
  HomotopyFiberSourceHomeomorph.equiv (subtypeInclusion (James.stage (spherePole n) 1))
    (FirstStage.homeomorph n) (inclusion n (spherePole n))

def targetHomeomorph (n : ℕ) :
    RelativeFiberHomology.Fiber ({FirstStageQuotient.basepoint n} :
      Set (FirstStageQuotient.Space n)) (pairTargetPoint n) ≃ₜ
        Path (FirstStageQuotient.basepoint n) (FirstStageQuotient.basepoint n) :=
  PointInclusionFiber.loopsHomeomorph (FirstStageQuotient.basepoint n) (pairTargetPoint n)

theorem toLoops_pair_factor (n : ℕ) :
    ((targetHomeomorph n : C(_, _)).comp (pairMap n)).comp
      (sourceHomeomorph n : C(_, _)) = toLoops n := by
  apply ContinuousMap.ext
  intro p
  apply Path.ext
  rfl

theorem toLoops_homology_bijective_first_range (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d)
    (hdn : d + 1 ≤ 2 * n) : Function.Bijective (singularHomologyMap (toLoops n) d) := by
  rw [← toLoops_pair_factor, singularHomologyMap_comp, singularHomologyMap_comp]
  exact ((homeomorphHomologyEquiv (targetHomeomorph n) d).bijective.comp
      (pairMap_homology_bijective n d hn hd hdn)).comp
        (homeomorphHomologyEquiv (sourceHomeomorph n) d).bijective

end NoExoticSixSphere.JamesSphere.FiberQuotient
