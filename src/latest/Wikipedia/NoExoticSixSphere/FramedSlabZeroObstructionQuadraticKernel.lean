import Wikipedia.NoExoticSixSphere.CrossEndpointIntegralParity
import Wikipedia.NoExoticSixSphere.FramedSlabKernelObstruction
import Wikipedia.NoExoticSixSphere.FramedSlabBoundaryPairingComparison

/-!
# The original two-ended quadratic form vanishes on the zero-obstruction kernel

The actual integral boundary sum maps to the sum of the two original
endpoint images in the slab. On its kernel those images cancel, so the
proved cross-endpoint parity comparison gives zero sum of the original
quadratic values after reduction. The native coefficient obstruction
then supplies exactly the required integral kernel lift for every class
with zero obstruction. No assertion is made about nonzero obstruction,
or about existence of the required two-connected framed filling.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

namespace NoExoticSixSphere.RegularCollaredCylinder.FramedSlabData

open GLOrthonormalization CylinderFiberSlab RegularSlabDiskCollar

variable {m n : ℕ} {z : Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) z s t}
  {hd : m = n + 6} {a : Sphere m} (A : d.FramedSlabData 6 hd a)

theorem integralBoundarySum_slabMap
    (x : SingularHomology {x : Sphere m // d.leftMap x = z} 3 ×
      SingularHomology {x : Sphere m // d.rightMap x = z} 3) :
    singularHomologyMap (subtypeInclusion A.nativeBoundary) 3 (A.integralBoundarySumEquiv 3 x) =
      singularHomologyMap
        (constantEndpointSlabMap d.leftMap s (Or.inl rfl) (d.left_eq s d.left_mem)) 3 x.1 +
      singularHomologyMap
        (constantEndpointSlabMap d.rightMap t (Or.inr rfl) (d.right_eq t d.right_mem)) 3 x.2 := by
  rw [A.integralBoundarySumEquiv_apply, map_add, ← LinearMap.comp_apply,
    ← singularHomologyMap_comp, A.nativeBoundaryInl_slabMap, ← LinearMap.comp_apply,
    ← singularHomologyMap_comp, A.nativeBoundaryInr_slabMap]

variable [SimplyConnectedSpace {x : Sphere m // d.leftMap x = z}]
  [SimplyConnectedSpace {x : Sphere m // d.rightMap x = z}]
  (l₀ : {x : Sphere m // d.leftMap x = z}) (r₀ : {x : Sphere m // d.rightMap x = z})
  [Subsingleton (π_ 2 {x : Sphere m // d.leftMap x = z} l₀)]
  [Subsingleton (π_ 2 {x : Sphere m // d.rightMap x = z} r₀)]
  [SimplyConnectedSpace (slab d.map z s t)] (w₀ : slab d.map z s t)
  [hW₂ : Subsingleton (π_ 2 (slab d.map z s t) w₀)]

include w₀ hW₂ in
theorem originalEndpointQuadratic_sum_zero_on_reduced_integral_kernel
    (x : SingularHomology {x : Sphere m // d.leftMap x = z} 3 ×
      SingularHomology {x : Sphere m // d.rightMap x = z} 3) :
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
      singularHomologyMap (subtypeInclusion A.nativeBoundary) 3
        (A.integralBoundarySumEquiv 3 x) = 0 →
      eL.modTwoHomologyQuadraticForm
          (RegularSphereFiber.frame d.leftMap d.smooth_left z d.regular_left 6 hd a) rL l₀
          (reductionHomologyMap 2 {x : Sphere m // d.leftMap x = z} 3 x.1) +
        eR.modTwoHomologyQuadraticForm
          (RegularSphereFiber.frame d.rightMap d.smooth_right z d.regular_right 6 hd a) rR r₀
          (reductionHomologyMap 2 {x : Sphere m // d.rightMap x = z} 3 x.2) = 0 := by
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
  intro rL rR hx
  have he : singularHomologyMap
        (constantEndpointSlabMap d.leftMap s (Or.inl rfl) (d.left_eq s d.left_mem)) 3 x.1 =
      singularHomologyMap
        (constantEndpointSlabMap d.rightMap t (Or.inr rfl) (d.right_eq t d.right_mem)) 3
        (-x.2) := by
    rw [map_neg]
    apply eq_neg_iff_add_eq_zero.mpr
    exact (A.integralBoundarySum_slabMap x).symm.trans hx
  have h := d.integralHomologyParity_eq_of_endpoint_images w₀ l₀ r₀ hd a
    rL rR x.1 (-x.2) he
  rw [EuclideanEmbedding.integralHomologyParity_neg] at h
  rw [EuclideanEmbedding.modTwoHomologyQuadraticForm_apply,
    EuclideanEmbedding.modTwoHomologyQuadraticForm_apply,
    EuclideanEmbedding.modTwoHomologyParity_reduction,
    EuclideanEmbedding.modTwoHomologyParity_reduction, h, ← two_mul,
    show (2 : ZMod 2) = 0 from by decide, zero_mul]

include w₀ hW₂ in
theorem originalEndpointQuadratic_sum_zero_of_boundary_obstruction_zero
    (u : ModHomology 2 {x : Sphere m // d.leftMap x = z} 3 ×
      ModHomology 2 {x : Sphere m // d.rightMap x = z} 3)
    (hu : modHomologyMap 2 (subtypeInclusion A.nativeBoundary) 3 (A.modTwoBoundarySum u) = 0) :
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
      A.boundaryKernelObstruction l₀ r₀ ⟨A.modTwoBoundarySum u, hu⟩ = 0 →
      eL.modTwoHomologyQuadraticForm
          (RegularSphereFiber.frame d.leftMap d.smooth_left z d.regular_left 6 hd a) rL l₀ u.1 +
        eR.modTwoHomologyQuadraticForm
          (RegularSphereFiber.frame d.rightMap d.smooth_right z d.regular_right 6 hd a) rR r₀ u.2 =
          0 := by
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
  intro rL rR hzero
  obtain ⟨x, hx, hred⟩ :=
    (A.boundaryKernelObstruction_zero_iff_endpoint_lift l₀ r₀ u hu).mp hzero
  rw [← hred]
  exact A.originalEndpointQuadratic_sum_zero_on_reduced_integral_kernel l₀ r₀ w₀ x rL rR hx

end NoExoticSixSphere.RegularCollaredCylinder.FramedSlabData
