import Wikipedia.NoExoticSixSphere.FramedSlabModTwoBoundarySum
import Wikipedia.NoExoticSixSphere.TwoComponentGeometricPairing
import Wikipedia.NoExoticSixSphere.IntegralKernelEndpointQuadraticValue

/-!
# The full two-ended boundary kernel for the original quadratic polar forms

The retained native boundary cap pairing equals the sum of the original
endpoint quadratic polar forms under the actual inclusion-sum map.
Every native mod-two boundary class has such coordinates. Consequently
the full kernel, including cancellation between the two endpoints, is
self-orthogonal for those original geometric forms.

This proves self-orthogonality of the polar pairing, not vanishing of
the quadratic form on the kernel. The latter still needs the geometric
and coefficient arguments, and the filling's two-connectivity remains
an explicit hypothesis rather than a constructed surgery result.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RegularCollaredCylinder.FramedSlabData

open GLOrthonormalization CylinderFiberSlab RegularSlabDiskCollar

attribute [local instance] modHomologyModule

variable {m n : ℕ} {z : Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) z s t}
  {hd : m = n + 6} {a : Sphere m} (A : d.FramedSlabData 6 hd a)

theorem nativeBoundaryInl_slabMap :
    (subtypeInclusion A.nativeBoundary).comp A.nativeBoundaryInl =
      constantEndpointSlabMap d.leftMap s (Or.inl rfl) (d.left_eq s d.left_mem) := by
  apply ContinuousMap.ext
  intro x
  exact A.nativeBoundaryInl_value x

theorem nativeBoundaryInr_slabMap :
    (subtypeInclusion A.nativeBoundary).comp A.nativeBoundaryInr =
      constantEndpointSlabMap d.rightMap t (Or.inr rfl) (d.right_eq t d.right_mem) := by
  apply ContinuousMap.ext
  intro x
  exact A.nativeBoundaryInr_value x

variable [SimplyConnectedSpace {x : Sphere m // d.leftMap x = z}]
  [SimplyConnectedSpace {x : Sphere m // d.rightMap x = z}]
  (l₀ : {x : Sphere m // d.leftMap x = z}) (r₀ : {x : Sphere m // d.rightMap x = z})
  [Subsingleton (π_ 2 {x : Sphere m // d.leftMap x = z} l₀)]
  [Subsingleton (π_ 2 {x : Sphere m // d.rightMap x = z} r₀)]

theorem disconnectedBoundaryPairing_sum
    (u v : ModHomology 2 {x : Sphere m // d.leftMap x = z} 3 ×
      ModHomology 2 {x : Sphere m // d.rightMap x = z} 3) :
    letI := regularFiberAtlas d.leftMap d.smooth_left z d.regular_left 6
      (endpointFiber_dimension_eq hd)
    letI := regularFiber_isManifold d.leftMap d.smooth_left z d.regular_left 6
      (endpointFiber_dimension_eq hd)
    letI := RegularSphereFiber.fiber_compact d.leftMap z
    letI := regularFiberAtlas d.rightMap d.smooth_right z d.regular_right 6
      (endpointFiber_dimension_eq hd)
    letI := regularFiber_isManifold d.rightMap d.smooth_right z d.regular_right 6
      (endpointFiber_dimension_eq hd)
    letI := RegularSphereFiber.fiber_compact d.rightMap z
    let eL := RegularSphereFiber.embedding d.leftMap d.smooth_left z d.regular_left 6 hd
    let eR := RegularSphereFiber.embedding d.rightMap d.smooth_right z d.regular_right 6 hd
    ∀ (rL : EuclideanEmbedding.TubularRetraction eL) (rR : EuclideanEmbedding.TubularRetraction eR),
      A.disconnectedBoundaryPairing l₀ r₀ (A.modTwoBoundarySum u) (A.modTwoBoundarySum v) =
        (eL.modTwoHomologyQuadraticForm
          (RegularSphereFiber.frame d.leftMap d.smooth_left z d.regular_left 6 hd a)
          rL l₀).polarBilin u.1 v.1 +
        (eR.modTwoHomologyQuadraticForm
          (RegularSphereFiber.frame d.rightMap d.smooth_right z d.regular_right 6 hd a)
          rR r₀).polarBilin u.2 v.2 := by
  let := regularFiberAtlas d.leftMap d.smooth_left z d.regular_left 6
    (endpointFiber_dimension_eq hd)
  let := regularFiber_isManifold d.leftMap d.smooth_left z d.regular_left 6
    (endpointFiber_dimension_eq hd)
  let := RegularSphereFiber.fiber_compact d.leftMap z
  let := regularFiberAtlas d.rightMap d.smooth_right z d.regular_right 6
    (endpointFiber_dimension_eq hd)
  let := regularFiber_isManifold d.rightMap d.smooth_right z d.regular_right 6
    (endpointFiber_dimension_eq hd)
  let := RegularSphereFiber.fiber_compact d.rightMap z
  dsimp only
  intro rL rR
  let := A.atlas
  let : ChartedSpace (Vector 6) A.nativeBoundary := A.boundaryAtlas
  let := A.nativeBoundaryCompactSpace
  let : Fact (Module.finrank ℝ (Vector 6) = (3 + 2) + 1) := ⟨finrank_euclideanSpace_fin⟩
  let := A.nativeBoundary_secondHomology_subsingleton l₀ r₀
  exact ZeroSecondHomologyCap.pairing_sum_eq_quadratic_polar l₀ r₀
    (RegularSphereFiber.embedding d.leftMap d.smooth_left z d.regular_left 6 hd)
    (RegularSphereFiber.embedding d.rightMap d.smooth_right z d.regular_right 6 hd)
    (RegularSphereFiber.frame d.leftMap d.smooth_left z d.regular_left 6 hd a)
    (RegularSphereFiber.frame d.rightMap d.smooth_right z d.regular_right 6 hd a)
    rL rR A.nativeBoundaryInl A.nativeBoundaryInr A.isOpenEmbedding_nativeBoundaryInl
    A.isOpenEmbedding_nativeBoundaryInr A.disjoint_nativeBoundaryInclusions u.1 v.1 u.2 v.2

variable [SimplyConnectedSpace (slab d.map z s t)] (w₀ : slab d.map z s t)
  [hW₂ : Subsingleton (π_ 2 (slab d.map z s t) w₀)]

include w₀ hW₂ in
theorem originalEndpointPolarKernel_selfOrthogonal
    (u : ModHomology 2 {x : Sphere m // d.leftMap x = z} 3 ×
      ModHomology 2 {x : Sphere m // d.rightMap x = z} 3) :
    letI := regularFiberAtlas d.leftMap d.smooth_left z d.regular_left 6
      (endpointFiber_dimension_eq hd)
    letI := regularFiber_isManifold d.leftMap d.smooth_left z d.regular_left 6
      (endpointFiber_dimension_eq hd)
    letI := RegularSphereFiber.fiber_compact d.leftMap z
    letI := regularFiberAtlas d.rightMap d.smooth_right z d.regular_right 6
      (endpointFiber_dimension_eq hd)
    letI := regularFiber_isManifold d.rightMap d.smooth_right z d.regular_right 6
      (endpointFiber_dimension_eq hd)
    letI := RegularSphereFiber.fiber_compact d.rightMap z
    let eL := RegularSphereFiber.embedding d.leftMap d.smooth_left z d.regular_left 6 hd
    let eR := RegularSphereFiber.embedding d.rightMap d.smooth_right z d.regular_right 6 hd
    ∀ (rL : EuclideanEmbedding.TubularRetraction eL) (rR : EuclideanEmbedding.TubularRetraction eR),
      (∀ v : ModHomology 2 {x : Sphere m // d.leftMap x = z} 3 ×
          ModHomology 2 {x : Sphere m // d.rightMap x = z} 3,
        modHomologyMap 2 (subtypeInclusion A.nativeBoundary) 3 (A.modTwoBoundarySum v) = 0 →
          (eL.modTwoHomologyQuadraticForm
            (RegularSphereFiber.frame d.leftMap d.smooth_left z d.regular_left 6 hd a)
            rL l₀).polarBilin v.1 u.1 +
          (eR.modTwoHomologyQuadraticForm
            (RegularSphereFiber.frame d.rightMap d.smooth_right z d.regular_right 6 hd a)
            rR r₀).polarBilin v.2 u.2 = 0) ↔
        modHomologyMap 2 (subtypeInclusion A.nativeBoundary) 3 (A.modTwoBoundarySum u) = 0 := by
  let := regularFiberAtlas d.leftMap d.smooth_left z d.regular_left 6
    (endpointFiber_dimension_eq hd)
  let := regularFiber_isManifold d.leftMap d.smooth_left z d.regular_left 6
    (endpointFiber_dimension_eq hd)
  let := RegularSphereFiber.fiber_compact d.leftMap z
  let := regularFiberAtlas d.rightMap d.smooth_right z d.regular_right 6
    (endpointFiber_dimension_eq hd)
  let := regularFiber_isManifold d.rightMap d.smooth_right z d.regular_right 6
    (endpointFiber_dimension_eq hd)
  let := RegularSphereFiber.fiber_compact d.rightMap z
  dsimp only
  intro rL rR
  constructor
  · intro hu
    apply (A.disconnectedBoundaryKernel_selfOrthogonal l₀ r₀ w₀ (A.modTwoBoundarySum u)).mp
    intro b hb
    obtain ⟨v, rfl⟩ := A.modTwoBoundarySum_surjective l₀ r₀ b
    exact (A.disconnectedBoundaryPairing_sum l₀ r₀ v u rL rR).trans (hu v hb)
  · intro hu v hv
    exact (A.disconnectedBoundaryPairing_sum l₀ r₀ v u rL rR).symm.trans
      ((A.disconnectedBoundaryKernel_selfOrthogonal l₀ r₀ w₀ (A.modTwoBoundarySum u)).mpr hu
        (A.modTwoBoundarySum v) hv)

end NoExoticSixSphere.RegularCollaredCylinder.FramedSlabData
