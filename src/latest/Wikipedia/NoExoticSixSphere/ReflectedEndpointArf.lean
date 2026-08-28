import Wikipedia.NoExoticSixSphere.ReflectedEndpointComparison
import Wikipedia.NoExoticSixSphere.GeometricArfNormalCoordinates

/-!
# The canonical reflected endpoint frame has the original geometric Arf invariant

The native endpoint embedding and regular-fiber atlas remain unchanged.
The actual reflected source-coordinate change is followed by ordered
normalization. The previously proved coordinate and normalization invariance
identifies the resulting quadratic form and Arf invariant with the original
defining-equation frame, for independent tubular choices and basepoints.
This does not assert general framed-bordism invariance.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.ReflectedSeam

open GLOrthonormalization Stiefel Wikipedia.HopfProblem
open DegreeCollapse ReflectedCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hmiss : ∀ x, d.rightMap x ≠ b) (hd : m = n + 6) (a : Sphere m)
  [SimplyConnectedSpace (EndpointFiber d)] (x x' : EndpointFiber d)
  [Subsingleton (π_ 2 (EndpointFiber d) x)] [Subsingleton (π_ 2 (EndpointFiber d) x')]

theorem canonicalEndpointFrame_quadraticForm :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    letI := regularFiber_isManifold d.leftMap d.smooth_left b d.regular_left 6 _;
    letI := RegularSphereFiber.fiber_compact d.leftMap b;
    ∀ r r' : (RegularSphereFiber.embedding d.leftMap d.smooth_left b d.regular_left 6 hd
      ).TubularRetraction,
      (RegularSphereFiber.embedding d.leftMap d.smooth_left b d.regular_left 6 hd
        ).modTwoHomologyQuadraticForm (canonicalEndpointFrame d hmiss 6 hd a).normalized r' x' =
      (RegularSphereFiber.embedding d.leftMap d.smooth_left b d.regular_left 6 hd
        ).modTwoHomologyQuadraticForm
          (RegularSphereFiber.frame d.leftMap d.smooth_left b d.regular_left 6 hd a) r x := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := regularFiber_isManifold d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := RegularSphereFiber.fiber_compact d.leftMap b
  intro r r'
  exact EuclideanEmbedding.modTwoHomologyQuadraticForm_normalized_recoordinateModel
    (RegularSphereFiber.embedding d.leftMap d.smooth_left b d.regular_left 6 hd)
    (RegularSphereFiber.frame d.leftMap d.smooth_left b d.regular_left 6 hd a)
    r r' x x' (canonicalEndpointChange d hmiss 6 hd)

theorem canonicalEndpointFrame_arf :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    letI := regularFiber_isManifold d.leftMap d.smooth_left b d.regular_left 6 _;
    letI := RegularSphereFiber.fiber_compact d.leftMap b;
    ∀ r r' : (RegularSphereFiber.embedding d.leftMap d.smooth_left b d.regular_left 6 hd
      ).TubularRetraction,
      GeometricArf.invariant
        (RegularSphereFiber.embedding d.leftMap d.smooth_left b d.regular_left 6 hd)
        (canonicalEndpointFrame d hmiss 6 hd a).normalized r' x' =
      GeometricArf.invariant
        (RegularSphereFiber.embedding d.leftMap d.smooth_left b d.regular_left 6 hd)
        (RegularSphereFiber.frame d.leftMap d.smooth_left b d.regular_left 6 hd a) r x := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := regularFiber_isManifold d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := RegularSphereFiber.fiber_compact d.leftMap b
  intro r r'
  exact GeometricArf.invariant_normalized_recoordinateModel
    (RegularSphereFiber.embedding d.leftMap d.smooth_left b d.regular_left 6 hd)
    (RegularSphereFiber.frame d.leftMap d.smooth_left b d.regular_left 6 hd a)
    r r' x x' (canonicalEndpointChange d hmiss 6 hd)

end NoExoticSixSphere.ReflectedSeam
