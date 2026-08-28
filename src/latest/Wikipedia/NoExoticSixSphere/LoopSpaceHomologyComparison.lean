import Wikipedia.NoExoticSixSphere.LoopSpaceMapNaturality
import Wikipedia.NoExoticSixSphere.RelativeFiberHomologyConnectivity
import Wikipedia.NoExoticSixSphere.RelativeContractibleSubspace
import Wikipedia.NoExoticSixSphere.PointInclusionFiber

/-!
# First-degree homology comparison descends to the actual loop map

The natural absolute-to-relative maps are isomorphisms for singleton
pairs. The original fiber-homology comparison and actual point-fiber
homeomorphisms then give the stated map on loop homology one degree lower.
All lower-connectivity assumptions are explicit.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.LoopSpaceMap

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem point_mapsTo (f : C(X, Y)) (x : X) : Set.MapsTo f {x} {f x} := by
  intro y hy
  exact congrArg f hy

def pointFiberMap (f : C(X, Y)) (x : X) :
    C(RelativeFiberHomology.Fiber ({x} : Set X) ⟨x, rfl⟩,
      RelativeFiberHomology.Fiber ({f x} : Set Y) ⟨f x, rfl⟩) :=
  RelativeFiberMap.map f (point_mapsTo f x) ⟨x, rfl⟩ ⟨f x, rfl⟩ rfl

theorem point_relative_homology_bijective (f : C(X, Y)) (x : X) (n : ℕ)
    (h : Function.Bijective (singularHomologyMap f (n + 2))) :
    Function.Bijective (RelativeSingularHomology.map f (point_mapsTo f x) (n + 2)) := by
  have hs := RelativeSingularHomology.toRelative_naturality f (point_mapsTo f x) (n + 2)
  have hb := (RelativeSingularHomology.contractibleSubspace_toRelative_bijective
    ({f x} : Set Y) n).comp h
  change Function.Bijective ((RelativeSingularHomology.toRelative ({f x} : Set Y) (n + 2)).comp
    (singularHomologyMap f (n + 2))) at hb
  rw [← hs] at hb
  exact (Function.Bijective.of_comp_iff _
    (RelativeSingularHomology.contractibleSubspace_toRelative_bijective ({x} : Set X) n)).mp hb

theorem map_pointFiber_factor (f : C(X, Y)) (x : X) :
    ((PointInclusionFiber.loopsHomeomorph (f x) ⟨f x, rfl⟩ : C(_, _)).comp
      (pointFiberMap f x)).comp
        ((PointInclusionFiber.loopsHomeomorph x ⟨x, rfl⟩).symm : C(_, _)) = map f x := by
  apply ContinuousMap.ext
  intro p
  apply Path.ext
  rfl

theorem homology_bijective [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
    (f : C(X, Y)) (x : X) (n : ℕ)
    (hX : ∀ k, 0 < k → k < n + 3 → ∀ y : X, Subsingleton (π_ k X y))
    (hY : ∀ k, 0 < k → k < n + 3 → ∀ y : Y, Subsingleton (π_ k Y y))
    (hH : Function.Bijective (singularHomologyMap f (n + 3))) :
    Function.Bijective (singularHomologyMap (map f x) (n + 2)) := by
  have hF : Function.Bijective (singularHomologyMap (pointFiberMap f x) (n + 2)) := by
    apply RelativeNormalization.fiber_homology_bijective_of_connectivity
      ({x} : Set X) ({f x} : Set Y) ⟨x, rfl⟩ ⟨f x, rfl⟩ f (point_mapsTo f x) rfl n
    · intro k hk hkn a p
      let := hX (k + 1) (by omega) (by omega) a.val
      exact PointInclusionFiber.pi_subsingleton x a k hk p
    · intro k hk hkn a p
      let := hY (k + 1) (by omega) (by omega) a.val
      exact PointInclusionFiber.pi_subsingleton (f x) a k hk p
    · exact point_relative_homology_bijective f x (n + 1) hH
  rw [← map_pointFiber_factor, singularHomologyMap_comp, singularHomologyMap_comp]
  exact ((homeomorphHomologyEquiv
    (PointInclusionFiber.loopsHomeomorph (f x) ⟨f x, rfl⟩) (n + 2)).bijective.comp hF).comp
      (homeomorphHomologyEquiv (PointInclusionFiber.loopsHomeomorph x ⟨x, rfl⟩).symm
        (n + 2)).bijective

end NoExoticSixSphere.LoopSpaceMap
