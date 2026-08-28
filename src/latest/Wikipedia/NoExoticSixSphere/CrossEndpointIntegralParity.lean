import Wikipedia.NoExoticSixSphere.CrossEndpointSphereParity

/-!
# Equality of the original quadratic values for equal integral endpoint images

Native sphere representatives identify the original integral homology
parities across the two endpoints whenever their actual images in the
two-connected slab agree. The original mod-two quadratic forms agree on
the corresponding reductions. This includes nonzero common images and
does not identify the integral kernel with the entire mod-two kernel.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization
open Wikipedia.HopfProblem.SingularMayerVietoris

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (r : TubularRetraction e) (p : M) [Subsingleton (π_ 2 M p)]

theorem integralHomologyParity_neg (u : SingularHomology M 3) :
    e.integralHomologyParity ν r p (-u) = e.integralHomologyParity ν r p u := by
  have h := e.integralHomologyParity_add_two_zsmul ν r p (-u) u
  simpa only [two_zsmul, neg_add_cancel_left] using h.symm

end NoExoticSixSphere.EuclideanEmbedding

namespace NoExoticSixSphere.RegularCollaredCylinder

open GLOrthonormalization CylinderFiberSlab RegularSlabDiskCollar
open Wikipedia.HopfProblem SingularMayerVietoris SphereHomologyCoefficients

variable {m n : ℕ} {z : Sphere n} {s t : ℝ}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) z s t)
  [SimplyConnectedSpace (slab d.map z s t)] (w : slab d.map z s t)
  [hW₂ : Subsingleton (π_ 2 (slab d.map z s t) w)]
  [SimplyConnectedSpace {x : Sphere m // d.leftMap x = z}]
  [SimplyConnectedSpace {x : Sphere m // d.rightMap x = z}]
  (l₀ : {x : Sphere m // d.leftMap x = z}) (r₀ : {x : Sphere m // d.rightMap x = z})
  [Subsingleton (π_ 2 {x : Sphere m // d.leftMap x = z} l₀)]
  [Subsingleton (π_ 2 {x : Sphere m // d.rightMap x = z} r₀)]

include w hW₂ in
theorem integralHomologyParity_eq_of_endpoint_images (hd : m = n + 6) (a : Sphere m) :
    letI := regularFiberAtlas d.leftMap d.smooth_left z d.regular_left 6
      (endpointFiber_dimension_eq hd)
    letI := regularFiberAtlas d.rightMap d.smooth_right z d.regular_right 6
      (endpointFiber_dimension_eq hd)
    letI := regularFiber_isManifold d.leftMap d.smooth_left z d.regular_left 6
      (endpointFiber_dimension_eq hd)
    letI := regularFiber_isManifold d.rightMap d.smooth_right z d.regular_right 6
      (endpointFiber_dimension_eq hd)
    letI := RegularSphereFiber.fiber_compact d.leftMap z
    letI := RegularSphereFiber.fiber_compact d.rightMap z
    ∀ (rL : EuclideanEmbedding.TubularRetraction
        (RegularSphereFiber.embedding d.leftMap d.smooth_left z d.regular_left 6 hd))
      (rR : EuclideanEmbedding.TubularRetraction
        (RegularSphereFiber.embedding d.rightMap d.smooth_right z d.regular_right 6 hd))
      (u : SingularHomology {x : Sphere m // d.leftMap x = z} 3)
      (v : SingularHomology {x : Sphere m // d.rightMap x = z} 3),
      singularHomologyMap
          (constantEndpointSlabMap d.leftMap s (Or.inl rfl) (d.left_eq s d.left_mem)) 3 u =
        singularHomologyMap
          (constantEndpointSlabMap d.rightMap t (Or.inr rfl) (d.right_eq t d.right_mem)) 3 v →
      EuclideanEmbedding.integralHomologyParity
        (RegularSphereFiber.embedding d.leftMap d.smooth_left z d.regular_left 6 hd)
        (RegularSphereFiber.frame d.leftMap d.smooth_left z d.regular_left 6 hd a) rL l₀ u =
      EuclideanEmbedding.integralHomologyParity
        (RegularSphereFiber.embedding d.rightMap d.smooth_right z d.regular_right 6 hd)
        (RegularSphereFiber.frame d.rightMap d.smooth_right z d.regular_right 6 hd a) rR r₀ v := by
  let := regularFiberAtlas d.leftMap d.smooth_left z d.regular_left 6
    (endpointFiber_dimension_eq hd)
  let := regularFiberAtlas d.rightMap d.smooth_right z d.regular_right 6
    (endpointFiber_dimension_eq hd)
  let := regularFiber_isManifold d.leftMap d.smooth_left z d.regular_left 6
    (endpointFiber_dimension_eq hd)
  let := regularFiber_isManifold d.rightMap d.smooth_right z d.regular_right 6
    (endpointFiber_dimension_eq hd)
  let := RegularSphereFiber.fiber_compact d.leftMap z
  let := RegularSphereFiber.fiber_compact d.rightMap z
  intro rL rR u v he
  apply d.geometricSphereParity_eq_of_integral_endpoint_images w hd a
    (SmoothCube.integralClassRepresentative l₀ u).val
    (SmoothCube.integralClassRepresentative r₀ v).val rL rR
  rw [SmoothCube.integralSphereClass_representative, SmoothCube.integralSphereClass_representative]
  exact he

include w hW₂ in
theorem quadraticForm_eq_on_reduced_endpoint_images (hd : m = n + 6) (a : Sphere m) :
    letI := regularFiberAtlas d.leftMap d.smooth_left z d.regular_left 6
      (endpointFiber_dimension_eq hd)
    letI := regularFiberAtlas d.rightMap d.smooth_right z d.regular_right 6
      (endpointFiber_dimension_eq hd)
    letI := regularFiber_isManifold d.leftMap d.smooth_left z d.regular_left 6
      (endpointFiber_dimension_eq hd)
    letI := regularFiber_isManifold d.rightMap d.smooth_right z d.regular_right 6
      (endpointFiber_dimension_eq hd)
    letI := RegularSphereFiber.fiber_compact d.leftMap z
    letI := RegularSphereFiber.fiber_compact d.rightMap z
    ∀ (rL : EuclideanEmbedding.TubularRetraction
        (RegularSphereFiber.embedding d.leftMap d.smooth_left z d.regular_left 6 hd))
      (rR : EuclideanEmbedding.TubularRetraction
        (RegularSphereFiber.embedding d.rightMap d.smooth_right z d.regular_right 6 hd))
      (u : SingularHomology {x : Sphere m // d.leftMap x = z} 3)
      (v : SingularHomology {x : Sphere m // d.rightMap x = z} 3),
      singularHomologyMap
          (constantEndpointSlabMap d.leftMap s (Or.inl rfl) (d.left_eq s d.left_mem)) 3 u =
        singularHomologyMap
          (constantEndpointSlabMap d.rightMap t (Or.inr rfl) (d.right_eq t d.right_mem)) 3 v →
      EuclideanEmbedding.modTwoHomologyQuadraticForm
        (RegularSphereFiber.embedding d.leftMap d.smooth_left z d.regular_left 6 hd)
        (RegularSphereFiber.frame d.leftMap d.smooth_left z d.regular_left 6 hd a) rL l₀
          (reductionHomologyMap 2 {x : Sphere m // d.leftMap x = z} 3 u) =
      EuclideanEmbedding.modTwoHomologyQuadraticForm
        (RegularSphereFiber.embedding d.rightMap d.smooth_right z d.regular_right 6 hd)
        (RegularSphereFiber.frame d.rightMap d.smooth_right z d.regular_right 6 hd a) rR r₀
          (reductionHomologyMap 2 {x : Sphere m // d.rightMap x = z} 3 v) := by
  let := regularFiberAtlas d.leftMap d.smooth_left z d.regular_left 6
    (endpointFiber_dimension_eq hd)
  let := regularFiberAtlas d.rightMap d.smooth_right z d.regular_right 6
    (endpointFiber_dimension_eq hd)
  let := regularFiber_isManifold d.leftMap d.smooth_left z d.regular_left 6
    (endpointFiber_dimension_eq hd)
  let := regularFiber_isManifold d.rightMap d.smooth_right z d.regular_right 6
    (endpointFiber_dimension_eq hd)
  let := RegularSphereFiber.fiber_compact d.leftMap z
  let := RegularSphereFiber.fiber_compact d.rightMap z
  intro rL rR u v he
  rw [EuclideanEmbedding.modTwoHomologyQuadraticForm_apply,
    EuclideanEmbedding.modTwoHomologyQuadraticForm_apply,
    EuclideanEmbedding.modTwoHomologyParity_reduction,
    EuclideanEmbedding.modTwoHomologyParity_reduction]
  exact d.integralHomologyParity_eq_of_endpoint_images w l₀ r₀ hd a rL rR u v he

end NoExoticSixSphere.RegularCollaredCylinder
