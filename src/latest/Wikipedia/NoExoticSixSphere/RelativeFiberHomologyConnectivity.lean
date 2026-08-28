import Wikipedia.NoExoticSixSphere.RelativeNormalizationFiberComparison

/-!
# Fiber homology comparison from actual bounded connectivity

The original pair connectivity constructs every normalization used in
the fiber-homology comparison. Thus no normalization structure remains
an extra input: only native vanishing in the stated lower degrees and
the actual map on relative homology are needed.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.RelativeNormalization

open RelativeFiberHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
  (U : Set X) (V : Set Y) [SimplyConnectedSpace U] [SimplyConnectedSpace V]
  (a : U) (b : V) (f : C(X, Y)) (hf : Set.MapsTo f U V) (hab : f a.val = b.val)

theorem fiber_homology_bijective_of_connectivity (n : ℕ)
    (hU : ∀ k, 0 < k → k < n + 2 → ∀ c : U, ∀ p : Fiber U c,
      Subsingleton (π_ k (Fiber U c) p))
    (hV : ∀ k, 0 < k → k < n + 2 → ∀ c : V, ∀ p : Fiber V c,
      Subsingleton (π_ k (Fiber V c) p))
    (hH : Function.Bijective (RelativeSingularHomology.map f hf (n + 3))) :
    Function.Bijective (singularHomologyMap (RelativeFiberMap.map f hf a b hab) (n + 2)) := by
  let : SimplyConnectedSpace (Fiber U a) :=
    HomotopyFiberConnectivity.simplyConnectedSpace (subtypeInclusion U) a
      (inclusion_surjective_of_fiberConnectivity U n hU 2 (by omega) (by omega) a)
  let : SimplyConnectedSpace (Fiber V b) :=
    HomotopyFiberConnectivity.simplyConnectedSpace (subtypeInclusion V) b
      (inclusion_surjective_of_fiberConnectivity V n hV 2 (by omega) (by omega) b)
  exact fiber_homology_bijective
    (ofFiberConnectivity U a n hU)
    (EndingPathPair.normalizationData U a n (fun k hk hkn p ↦ hU k hk hkn a p))
    (ofFiberConnectivity V b n hV)
    (EndingPathPair.normalizationData V b n (fun k hk hkn p ↦ hV k hk hkn b p))
    f hf hab hH

end NoExoticSixSphere.RelativeNormalization
