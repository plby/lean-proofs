import Wikipedia.NoExoticSixSphere.CollaredZeroLowSurgeryArf
import Wikipedia.NoExoticSixSphere.ReflectedEndpointArf

/-!
# A genuine regular cylinder to an omitted fiber forces zero endpoint Arf

Reflection constructs the actual collared state. Its canonical endpoint
comparison preserves the original native fiber atlas and the original
defining-equation frame up to the already proved coordinate and frame
normalization invariance. Native low surgery and Arf transport therefore
give zero for that original endpoint invariant. No filling or stabilized
frame comparison is assumed as an additional input.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.ReflectedSeam

open GLOrthonormalization EuclideanEmbedding Wikipedia.HopfProblem
open DegreeCollapse ReflectedCylinder SingularMayerVietoris PeriodTorusHigherHomology

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hmiss : ∀ x, d.rightMap x ≠ b) (hd : m = n + 6) (a : Sphere m)
  [SimplyConnectedSpace (EndpointFiber d)] (x : EndpointFiber d)
  [Subsingleton (π_ 2 (EndpointFiber d) x)]

include hmiss in
theorem endpointGeometricArf_eq_zero :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    letI := regularFiber_isManifold d.leftMap d.smooth_left b d.regular_left 6 _;
    letI := RegularSphereFiber.fiber_compact d.leftMap b;
    ∀ r : (RegularSphereFiber.embedding d.leftMap d.smooth_left b d.regular_left 6 hd
      ).TubularRetraction,
      GeometricArf.invariant
        (RegularSphereFiber.embedding d.leftMap d.smooth_left b d.regular_left 6 hd)
        (RegularSphereFiber.frame d.leftMap d.smooth_left b d.regular_left 6 hd a) r x = 0 := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := regularFiber_isManifold d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := RegularSphereFiber.fiber_compact d.leftMap b
  let S := referenceLowCollaredState d hmiss hd a
  let := S.zeroAtlas
  let := S.zero_isManifold
  let := CollaredZero.zeroCompactSpace S
  let y : S.Space := CollaredZero.referencePoint S x
  let G := canonicalEndpointComparison d hmiss hd a y
  let z : S.Zero := G.diffeomorph x
  let : SimplyConnectedSpace S.Zero :=
    G.diffeomorph.symm.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  let : Subsingleton (SingularHomology (EndpointFiber d) 2) :=
    TwoConnectedCoefficients.secondHomology_subsingleton x
  let : Subsingleton (SingularHomology S.Zero 2) :=
    (homeomorphHomologyEquiv G.diffeomorph.symm.toHomeomorph 2).injective.subsingleton
  let : Subsingleton (π_ 2 S.Zero z) :=
    (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv z).injective.subsingleton
  let : Nonempty S.Zero := ⟨z⟩
  obtain ⟨rS⟩ := (CollaredZero.embedding S).nonempty_tubularRetraction
    (CollaredZero.normalFrame S y)
  intro r
  have hc := canonicalEndpointFrame_arf d hmiss hd a x x r r
  exact hc.symm.trans ((G.geometricArf_eq r rS x z).trans
    (CollaredZero.geometricArf_eq_zero_of_twoConnected_boundary S y z rS))

end NoExoticSixSphere.ReflectedSeam
