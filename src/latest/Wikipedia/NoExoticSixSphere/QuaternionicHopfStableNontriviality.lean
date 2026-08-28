import Wikipedia.NoExoticSixSphere.FramedCollapseStableArfObstruction
import Wikipedia.NoExoticSixSphere.QuaternionicHopfArfInvariant
import Wikipedia.NoExoticSixSphere.SixthStemSmashSquareOrder

/-!
# The original Hopf-product sixth-stem class is nontrivial and has order two

The prescribed Hopf-product frame has its proved original Arf invariant
one. The actual compactification comparison now obstructs nullhomotopy
after every finite suspension of its original collapse. Its retained
native-class identity proves nontriviality of the original smash square.
Together with the prior square relation this gives exact order two,
without yet asserting that this class generates the entire sixth stem.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.QuaternionicHopf

local instance : ChartedSpace (V 6) (Sphere 3 × Sphere 3) := southPairEuclideanAtlas
local instance : IsManifold (𝓡 6) ∞ (Sphere 3 × Sphere 3) := southPairEuclideanIsManifold

local instance stableArfSpherePiTwo (s : Sphere 3) :
    Subsingleton (HomotopyGroup (Fin 2) (Sphere 3) s) :=
  subsingleton_sphereHomotopyGroup (by decide) s

local instance stableArfProductSimplyConnected : SimplyConnectedSpace (Sphere 3 × Sphere 3) :=
  HigherHomotopy.simplyConnected_product

local instance stableArfProductPiTwo (p : Sphere 3 × Sphere 3) :
    Subsingleton (HomotopyGroup (Fin 2) (Sphere 3 × Sphere 3) p) :=
  HigherHomotopy.subsingleton_product p.1 p.2

theorem southPairCollapse_not_finitely_nullhomotopic :
    ¬ ∃ j : ℕ,
      (SphereMapSuspension.iterate southPairSmoothCollapseData.sphereMap j).Nullhomotopic :=
  southPairSmoothCollapseData.not_finitely_stably_nullhomotopic_of_geometricArf_ne_zero
    (by decide) southPairTubularRetraction (spherePole 3, spherePole 3)
    (by rw [geometricArf_southPair]; exact one_ne_zero)

end NoExoticSixSphere.QuaternionicHopf

namespace NoExoticSixSphere.SixthStemSmashSquare

open SmoothCube QuaternionicHopf

theorem nativeClass_ne_one : nativeClass ≠ 1 := by
  intro h
  have hc : sphereClass southPairSmoothCollapseBasedMap = 1 :=
    southPairSmoothCollapse_nativeClass.trans h
  have hnull := (sphereClass_eq_one_iff_nullhomotopic (by decide)
    southPairSmoothCollapseBasedMap).mp hc
  exact southPairCollapse_not_finitely_nullhomotopic ⟨0, hnull⟩

theorem stableClass_ne_one : stableClass ≠ 1 :=
  fun h ↦ nativeClass_ne_one (stableClass_eq_one_iff.mp h)

theorem orderOf_nativeClass : orderOf nativeClass = 2 :=
  orderOf_eq_prime nativeClass_pow_two nativeClass_ne_one

theorem orderOf_stableClass : orderOf stableClass = 2 :=
  orderOf_eq_prime stableClass_pow_two stableClass_ne_one

end NoExoticSixSphere.SixthStemSmashSquare
