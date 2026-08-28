import Wikipedia.NoExoticSixSphere.CircleCylinderClopenEndpoints
import Wikipedia.NoExoticSixSphere.RegularSphereFiberEmbedding
import Wikipedia.NoExoticSixSphere.IteratedSphereSuspensionArf

/-!
# Connectivity of the actual native clopen endpoint pieces

Compactness, simple connectivity, and vanishing second homotopy are
transported along the constructed endpoint diffeomorphisms. Smoothness
comes from the inherited time-zero open-submanifold atlases. No extra
connectivity assumptions are imposed on the image pieces or whole double.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CircleCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hd : m = n + 6)

theorem leftZeroOpen_compact : CompactSpace (leftZeroOpen d 6 hd) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := timeZeroAtlas d 6 hd
  let := RegularSphereFiber.fiber_compact d.leftMap b
  exact (leftZeroDiffeomorph d 6 hd).toHomeomorph.compactSpace

theorem rightZeroOpen_compact : CompactSpace (rightZeroOpen d 6 hd) := by
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd)
  let := timeZeroAtlas d 6 hd
  let := RegularSphereFiber.fiber_compact d.rightMap b
  exact (rightZeroDiffeomorph d 6 hd).toHomeomorph.compactSpace

theorem leftZeroOpen_isManifold : letI := timeZeroAtlas d 6 hd;
    IsManifold (𝓡 6) ∞ (leftZeroOpen d 6 hd) := by
  let := timeZeroAtlas d 6 hd
  let := timeZero_isManifold d 6 hd
  infer_instance

theorem rightZeroOpen_isManifold : letI := timeZeroAtlas d 6 hd;
    IsManifold (𝓡 6) ∞ (rightZeroOpen d 6 hd) := by
  let := timeZeroAtlas d 6 hd
  let := timeZero_isManifold d 6 hd
  infer_instance

theorem leftZeroOpen_simplyConnected [SimplyConnectedSpace {x : Sphere m // d.leftMap x = b}] :
    SimplyConnectedSpace (leftZeroOpen d 6 hd) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := timeZeroAtlas d 6 hd
  exact (leftZeroDiffeomorph d 6 hd).symm.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace

theorem rightZeroOpen_simplyConnected [SimplyConnectedSpace {x : Sphere m // d.rightMap x = b}] :
    SimplyConnectedSpace (rightZeroOpen d 6 hd) := by
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd)
  let := timeZeroAtlas d 6 hd
  exact (rightZeroDiffeomorph d 6 hd).symm.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace

theorem leftZeroOpen_piTwo_subsingleton [SimplyConnectedSpace {x : Sphere m // d.leftMap x = b}]
    (x : {x : Sphere m // d.leftMap x = b})
    [Subsingleton (π_ 2 {x : Sphere m // d.leftMap x = b} x)]
    (z : leftZeroOpen d 6 hd) : Subsingleton (π_ 2 (leftZeroOpen d 6 hd) z) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := timeZeroAtlas d 6 hd
  exact SphereMapSuspension.piTwo_subsingleton_of_homeomorph
    (leftZeroDiffeomorph d 6 hd).toHomeomorph x z

theorem rightZeroOpen_piTwo_subsingleton [SimplyConnectedSpace {x : Sphere m // d.rightMap x = b}]
    (x : {x : Sphere m // d.rightMap x = b})
    [Subsingleton (π_ 2 {x : Sphere m // d.rightMap x = b} x)]
    (z : rightZeroOpen d 6 hd) : Subsingleton (π_ 2 (rightZeroOpen d 6 hd) z) := by
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd)
  let := timeZeroAtlas d 6 hd
  exact SphereMapSuspension.piTwo_subsingleton_of_homeomorph
    (rightZeroDiffeomorph d 6 hd).toHomeomorph x z

end NoExoticSixSphere.CircleCylinder
