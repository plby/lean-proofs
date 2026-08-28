import Wikipedia.NoExoticSixSphere.CircleCylinderEndpointAffineComparison
import Wikipedia.NoExoticSixSphere.CircleCylinderClopenEndpointConnectivity
import Wikipedia.NoExoticSixSphere.AffineStabilizedQuadraticTransport
import Wikipedia.NoExoticSixSphere.GeometricArfNormalCoordinates

/-!
# Both original endpoint Arf invariants agree with their actual clopen seam invariants

The original, unnormalized defining-equation frames are retained on the
source fibers. Normalization invariance and the genuine affine framed
comparisons identify their Arf invariants with the restricted induced
frames on the native clopen seam pieces. Tubular choices and basepoints
are independent. Connectivity of each image piece is derived, not assumed.
This is endpoint transport; it does not yet assert two-ended Arf equality.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CircleCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hd : m = n + 6) (a : Sphere 1 × Sphere m) (y : Fiber d)

theorem leftEndpointArf_eq_clopen
    [SimplyConnectedSpace {x : Sphere m // d.leftMap x = b}]
    (x : {x : Sphere m // d.leftMap x = b})
    [Subsingleton (π_ 2 {x : Sphere m // d.leftMap x = b} x)] (z : leftZeroOpen d 6 hd) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    letI := regularFiber_isManifold d.leftMap d.smooth_left b d.regular_left 6 _;
    letI := RegularSphereFiber.fiber_compact d.leftMap b;
    letI := timeZeroAtlas d 6 hd;
    letI := leftZeroOpen_isManifold d hd;
    letI := leftZeroOpen_compact d hd;
    letI := leftZeroOpen_simplyConnected d hd;
    letI := leftZeroOpen_piTwo_subsingleton d hd x z;
    ∀ r : (RegularSphereFiber.embedding d.leftMap d.smooth_left b d.regular_left 6 hd
        ).TubularRetraction,
      ∀ rZ : (leftZeroEmbedding d hd a).TubularRetraction,
        GeometricArf.invariant
          (RegularSphereFiber.embedding d.leftMap d.smooth_left b d.regular_left 6 hd)
          (RegularSphereFiber.frame d.leftMap d.smooth_left b d.regular_left 6 hd a.2) r x =
        GeometricArf.invariant (leftZeroEmbedding d hd a) (leftZeroFrame d hd a y) rZ z := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := regularFiber_isManifold d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := RegularSphereFiber.fiber_compact d.leftMap b
  let := timeZeroAtlas d 6 hd
  let := leftZeroOpen_isManifold d hd
  let := leftZeroOpen_compact d hd
  let := leftZeroOpen_simplyConnected d hd
  let := leftZeroOpen_piTwo_subsingleton d hd x z
  intro r rZ
  exact (GeometricArf.invariant_normalized
    (RegularSphereFiber.embedding d.leftMap d.smooth_left b d.regular_left 6 hd)
    (RegularSphereFiber.frame d.leftMap d.smooth_left b d.regular_left 6 hd a.2) r r x x).symm.trans
      ((leftEndpointAffineComparison d hd a y).geometricArf_eq r rZ x z)

theorem rightEndpointArf_eq_clopen
    [SimplyConnectedSpace {x : Sphere m // d.rightMap x = b}]
    (x : {x : Sphere m // d.rightMap x = b})
    [Subsingleton (π_ 2 {x : Sphere m // d.rightMap x = b} x)] (z : rightZeroOpen d 6 hd) :
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd);
    letI := regularFiber_isManifold d.rightMap d.smooth_right b d.regular_right 6 _;
    letI := RegularSphereFiber.fiber_compact d.rightMap b;
    letI := timeZeroAtlas d 6 hd;
    letI := rightZeroOpen_isManifold d hd;
    letI := rightZeroOpen_compact d hd;
    letI := rightZeroOpen_simplyConnected d hd;
    letI := rightZeroOpen_piTwo_subsingleton d hd x z;
    ∀ r : (RegularSphereFiber.embedding d.rightMap d.smooth_right b d.regular_right 6 hd
        ).TubularRetraction,
      ∀ rZ : (rightZeroEmbedding d hd a).TubularRetraction,
        GeometricArf.invariant
          (RegularSphereFiber.embedding d.rightMap d.smooth_right b d.regular_right 6 hd)
          (RegularSphereFiber.frame d.rightMap d.smooth_right b d.regular_right 6 hd a.2) r x =
        GeometricArf.invariant (rightZeroEmbedding d hd a) (rightZeroFrame d hd a y) rZ z := by
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd)
  let := regularFiber_isManifold d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd)
  let := RegularSphereFiber.fiber_compact d.rightMap b
  let := timeZeroAtlas d 6 hd
  let := rightZeroOpen_isManifold d hd
  let := rightZeroOpen_compact d hd
  let := rightZeroOpen_simplyConnected d hd
  let := rightZeroOpen_piTwo_subsingleton d hd x z
  intro r rZ
  exact (GeometricArf.invariant_normalized
    (RegularSphereFiber.embedding d.rightMap d.smooth_right b d.regular_right 6 hd)
    (RegularSphereFiber.frame d.rightMap d.smooth_right b d.regular_right 6 hd a.2)
      r r x x).symm.trans
      ((rightEndpointAffineComparison d hd a y).geometricArf_eq r rZ x z)

end NoExoticSixSphere.CircleCylinder
