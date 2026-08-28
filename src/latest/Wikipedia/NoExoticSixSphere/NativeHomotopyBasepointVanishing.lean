import Wikipedia.NoExoticSixSphere.SmoothSphereBasepointAdjustment
import Wikipedia.HopfProblem.OrbitPairSphereNullhomotopyCriterion
import Wikipedia.HopfProblem.OrbitPairLoopSpaceConnectivity

/-!
# Native homotopy vanishing at every point of a path-connected space

The actual sphere-basepoint adjustment moves a sphere map to a selected
point. Native vanishing there contracts the adjusted map. The disk
criterion makes the resulting ordinary contraction based at any original
point. Applied after native currying, this handles every loop-space
basepoint, not only the constant loop.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.NativeHomotopyBasepointVanishing

variable {X : Type*} [TopologicalSpace X]

theorem subsingleton [PathConnectedSpace X] (n : ℕ) (hn : 0 < n)
    (x : X) [Subsingleton (π_ n X x)] (y : X) : Subsingleton (π_ n X y) := by
  apply SphereNullhomotopy.pi_subsingleton_of_sphere_nullhomotopies hn ?_ y
  intro f
  obtain ⟨g, hg⟩ := SmoothCube.exists_based_map_homotopic hn f x
  let K : SmoothCube.BasedMap n X x := ⟨ContinuousMap.const _ x, rfl⟩
  obtain ⟨H⟩ := (SmoothCube.sphereClass_eq_iff hn g K).mp (Subsingleton.elim _ _)
  exact ⟨x, hg.trans ⟨H.toHomotopy⟩⟩

theorem loops_subsingleton [SimplyConnectedSpace X] (n : ℕ) (hn : 0 < n)
    (x : X) [Subsingleton (π_ (n + 1) X x)] (p : Path x x) :
    Subsingleton (π_ n (Path x x) p) := by
  let := loopSpace_pathConnected x
  let : Subsingleton (π_ n (Path x x) (Path.refl x)) :=
    (GeneralizedLoopCurrying.homotopyEquiv n x).injective.subsingleton
  exact subsingleton n hn (Path.refl x) p

end NoExoticSixSphere.NativeHomotopyBasepointVanishing
