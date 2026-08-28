import Wikipedia.NoExoticSixSphere.CircleCylinderComponentZeroCases
import Wikipedia.NoExoticSixSphere.CircleCylinderEndpointArfTransport
import Wikipedia.NoExoticSixSphere.CollaredZeroClopenRestrictionArfVanishing

/-!
# A genuine regular collared cylinder with a six-sphere end forces endpoint Arf vanishing

Choose the connected component through the original left endpoint. Its
boundary is either the left endpoint alone or both original endpoints.
In the latter case the literal fold makes its positive half path connected.
The two native boundary-vanishing theorems therefore cover both cases.
The conclusion retains the original unnormalized left defining-equation
frame, its original regular-fiber atlas, and arbitrary tubular data.

The regular collared cylinder is input data, not inferred from an equality
of stable classes. No diffeomorphism or framing of the right six-sphere is
assumed: its given homeomorphism is used only for boundary topology.
-/

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CircleCylinder

open GLOrthonormalization EuclideanEmbedding Wikipedia.HopfProblem.DegreeCollapse

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hd : m = n + 6) (a : Sphere 1 × Sphere m)
  [SimplyConnectedSpace {x : Sphere m // d.leftMap x = b}]
  (x : {x : Sphere m // d.leftMap x = b})
  [Subsingleton (π_ 2 {x : Sphere m // d.leftMap x = b} x)]

theorem leftClopenArf_eq_zero_of_right_sixSphere (y : Fiber d) (z : leftZeroOpen d 6 hd)
    (hX : {x : Sphere m // d.rightMap x = b} ≃ₜ Sphere 6) :
    letI := timeZeroAtlas d 6 hd;
    letI := leftZeroOpen_isManifold d hd; letI := leftZeroOpen_compact d hd;
    letI := leftZeroOpen_simplyConnected d hd;
    letI := leftZeroOpen_piTwo_subsingleton d hd x z;
    ∀ rZ : (leftZeroEmbedding d hd a).TubularRetraction,
      GeometricArf.invariant (leftZeroEmbedding d hd a) (leftZeroFrame d hd a y) rZ z = 0 := by
  let S := lowCollaredState d hd a
  let := S.zeroAtlas
  let := S.zero_isManifold
  let := timeZeroAtlas d 6 hd
  let := leftZeroOpen_isManifold d hd
  let := leftZeroOpen_compact d hd
  let := leftZeroOpen_simplyConnected d hd
  let := leftZeroOpen_piTwo_subsingleton d hd x z
  let V : Opens S.Zero := leftZeroOpen d 6 hd
  have hV : IsClosed (V : Set S.Zero) := leftZeroOpen_closed d 6 hd
  let z' : V := z
  let : SimplyConnectedSpace V := leftZeroOpen_simplyConnected d hd
  let : Subsingleton (π_ 2 V z') := leftZeroOpen_piTwo_subsingleton d hd x z
  let U : Opens S.Space := componentOpen d 6 hd (leftInclusion d x)
  have hU : IsClosed (U : Set S.Space) := componentOpen_closed d 6 hd (leftInclusion d x)
  let y' : (S.restrictClopen U hU).Space :=
    ⟨leftInclusion d x, mem_connectedComponent⟩
  by_cases h : ∃ w, rightInclusion d w ∈ connectedComponent (leftInclusion d x)
  · obtain ⟨w, hw⟩ := h
    let : PathConnectedSpace {x : Sphere m // d.rightMap x = b} :=
      hX.symm.surjective.pathConnectedSpace hX.symm.continuous
    let : PathConnectedSpace (S.restrictClopen U hU).PositiveHalf :=
      componentState_positiveHalf_pathConnected d hd a (leftInclusion d x)
        (by rw [time_leftInclusion])
    exact CollaredZero.ClopenRestriction.clopenGeometricArf_eq_zero_of_full_restriction
      S U hU V hV y y' z'
      (componentZeroOpen_eq_top_of_right_mem d hd a x w hw)
      ((leftZeroComplementHomeomorph d 6 hd).trans hX)
  · exact CollaredZero.ClopenRestriction.clopenGeometricArf_eq_zero_of_zeroOpen_eq
      S U hU V hV y y' z'
      (componentZeroOpen_eq_left_of_right_not_mem d hd a x (not_exists.mp h))

theorem leftEndpointArf_eq_zero_of_right_sixSphere
    (hX : {x : Sphere m // d.rightMap x = b} ≃ₜ Sphere 6) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    letI := regularFiber_isManifold d.leftMap d.smooth_left b d.regular_left 6 _;
    letI := RegularSphereFiber.fiber_compact d.leftMap b;
    ∀ r : (RegularSphereFiber.embedding d.leftMap d.smooth_left b d.regular_left 6 hd
        ).TubularRetraction,
      GeometricArf.invariant
        (RegularSphereFiber.embedding d.leftMap d.smooth_left b d.regular_left 6 hd)
        (RegularSphereFiber.frame d.leftMap d.smooth_left b d.regular_left 6 hd a.2) r x = 0 := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := regularFiber_isManifold d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := RegularSphereFiber.fiber_compact d.leftMap b
  let := timeZeroAtlas d 6 hd
  let := leftZeroOpen_isManifold d hd
  let := leftZeroOpen_compact d hd
  let := leftZeroOpen_simplyConnected d hd
  let z := leftZeroDiffeomorph d 6 hd x
  let := leftZeroOpen_piTwo_subsingleton d hd x z
  let : Nonempty (leftZeroOpen d 6 hd) := ⟨z⟩
  obtain ⟨rZ⟩ := (leftZeroEmbedding d hd a).nonempty_tubularRetraction
    (leftZeroFrame d hd a (leftInclusion d x))
  intro r
  exact (leftEndpointArf_eq_clopen d hd a (leftInclusion d x) x z r rZ).trans
    (leftClopenArf_eq_zero_of_right_sixSphere d hd a x (leftInclusion d x) z hX rZ)

end NoExoticSixSphere.CircleCylinder
