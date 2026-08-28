import Wikipedia.NoExoticSixSphere.CollaredCylinderEndpointParity
import Wikipedia.NoExoticSixSphere.IntegralKernelEndpointHomology

/-!
# Original endpoint parity agrees for equal integral images in the slab

Native Hurewicz theory constructs an actual collared cylinder from equal
integral sphere images in the original two-connected slab. The checked
two-ended frame comparison identifies the original endpoint parities.
Replacing either sphere by a smooth embedded representative preserves its
integral image and its original geometric parity. The common image need
not vanish. Connectivity of the slab is retained as a hypothesis here.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.RegularCollaredCylinder

open GLOrthonormalization CylinderFiberSlab RegularSlabDiskCollar
open Wikipedia.HopfProblem.SingularMayerVietoris

variable {m n : ℕ} {z : Sphere n} {s t : ℝ}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) z s t)
  [SimplyConnectedSpace (slab d.map z s t)] (w : slab d.map z s t)
  [hW₂ : Subsingleton (π_ 2 (slab d.map z s t) w)]

include w hW₂ in
theorem sphereParity_eq_of_integral_endpoint_images (hd : m = n + 6) (a : Sphere m)
    (u₀ : C(Sphere 3, {x : Sphere m // d.leftMap x = z}))
    (u₁ : C(Sphere 3, {x : Sphere m // d.rightMap x = z})) :
    letI := regularFiberAtlas d.leftMap d.smooth_left z d.regular_left 6 (by simpa using hd)
    letI := regularFiberAtlas d.rightMap d.smooth_right z d.regular_right 6 (by simpa using hd)
    ∀ (hu₀ : ContMDiff (𝓡 3) (𝓡 6) ∞ u₀) (hi₀ : Injective u₀)
      (hdu₀ : ∀ q, Injective (mfderiv (𝓡 3) (𝓡 6) u₀ q))
      (hu₁ : ContMDiff (𝓡 3) (𝓡 6) ∞ u₁) (hi₁ : Injective u₁)
      (hdu₁ : ∀ q, Injective (mfderiv (𝓡 3) (𝓡 6) u₁ q)),
      singularHomologyMap
          (constantEndpointSlabMap d.leftMap s (Or.inl rfl) (d.left_eq s d.left_mem)) 3
          (SmoothCube.integralSphereClass u₀) =
        singularHomologyMap
          (constantEndpointSlabMap d.rightMap t (Or.inr rfl) (d.right_eq t d.right_mem)) 3
          (SmoothCube.integralSphereClass u₁) →
      (RegularSphereFiber.embedding d.leftMap d.smooth_left z d.regular_left 6 hd).sphereParity
        (RegularSphereFiber.frame d.leftMap d.smooth_left z d.regular_left 6 hd a)
          u₀ hu₀ hi₀ hdu₀ =
      (RegularSphereFiber.embedding d.rightMap d.smooth_right z d.regular_right 6 hd).sphereParity
        (RegularSphereFiber.frame d.rightMap d.smooth_right z d.regular_right 6 hd a)
          u₁ hu₁ hi₁ hdu₁ := by
  let := regularFiberAtlas d.leftMap d.smooth_left z d.regular_left 6 (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right z d.regular_right 6 (by simpa using hd)
  intro hu₀ hi₀ hdu₀ hu₁ hi₁ hdu₁ he
  obtain ⟨D⟩ := d.nonempty_collaredCylinderExtension_of_integral_images w
    (constantEndpointSlabMap d.leftMap s (Or.inl rfl) (d.left_eq s d.left_mem))
    (constantEndpointSlabMap d.rightMap t (Or.inr rfl) (d.right_eq t d.right_mem)) u₀ u₁ he
  exact d.sphereParity_eq_of_collaredCylinder hd a u₀ u₁ D (spherePole 3)
    hu₀ hi₀ hdu₀ hu₁ hi₁ hdu₁

variable [SimplyConnectedSpace {x : Sphere m // d.leftMap x = z}]
  [SimplyConnectedSpace {x : Sphere m // d.rightMap x = z}]

include w hW₂ in
theorem geometricSphereParity_eq_of_integral_endpoint_images (hd : m = n + 6) (a : Sphere m)
    (u₀ : C(Sphere 3, {x : Sphere m // d.leftMap x = z}))
    (u₁ : C(Sphere 3, {x : Sphere m // d.rightMap x = z})) :
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
    ∀ (r₀ : EuclideanEmbedding.TubularRetraction
        (RegularSphereFiber.embedding d.leftMap d.smooth_left z d.regular_left 6 hd))
      (r₁ : EuclideanEmbedding.TubularRetraction
        (RegularSphereFiber.embedding d.rightMap d.smooth_right z d.regular_right 6 hd)),
      singularHomologyMap
          (constantEndpointSlabMap d.leftMap s (Or.inl rfl) (d.left_eq s d.left_mem)) 3
          (SmoothCube.integralSphereClass u₀) =
        singularHomologyMap
          (constantEndpointSlabMap d.rightMap t (Or.inr rfl) (d.right_eq t d.right_mem)) 3
          (SmoothCube.integralSphereClass u₁) →
      EuclideanEmbedding.geometricSphereParity
        (RegularSphereFiber.embedding d.leftMap d.smooth_left z d.regular_left 6 hd)
          (RegularSphereFiber.frame d.leftMap d.smooth_left z d.regular_left 6 hd a) r₀ u₀ =
      EuclideanEmbedding.geometricSphereParity
        (RegularSphereFiber.embedding d.rightMap d.smooth_right z d.regular_right 6 hd)
          (RegularSphereFiber.frame d.rightMap d.smooth_right z d.regular_right 6 hd a) r₁ u₁ := by
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
  intro r₀ r₁ he
  let e₀ := RegularSphereFiber.embedding d.leftMap d.smooth_left z d.regular_left 6 hd
  let e₁ := RegularSphereFiber.embedding d.rightMap d.smooth_right z d.regular_right 6 hd
  let a₀ := RegularSphereFiber.frame d.leftMap d.smooth_left z d.regular_left 6 hd a
  let a₁ := RegularSphereFiber.frame d.rightMap d.smooth_right z d.regular_right 6 hd a
  obtain ⟨v₀, hv₀, H₀, hdv₀, hev₀⟩ :=
    Wikipedia.HopfProblem.DegreeCollapse.TripleParameters.exists_embedded_sphere_representative
      e₀ r₀ u₀
  obtain ⟨v₁, hv₁, H₁, hdv₁, hev₁⟩ :=
    Wikipedia.HopfProblem.DegreeCollapse.TripleParameters.exists_embedded_sphere_representative
      e₁ r₁ u₁
  have he' : singularHomologyMap
        (constantEndpointSlabMap d.leftMap s (Or.inl rfl) (d.left_eq s d.left_mem)) 3
        (SmoothCube.integralSphereClass v₀) =
      singularHomologyMap
        (constantEndpointSlabMap d.rightMap t (Or.inr rfl) (d.right_eq t d.right_mem)) 3
        (SmoothCube.integralSphereClass v₁) := by
    rw [← SmoothCube.integralSphereClass_homotopic H₀,
      ← SmoothCube.integralSphereClass_homotopic H₁]
    exact he
  calc
    e₀.geometricSphereParity a₀ r₀ u₀ = e₀.geometricSphereParity a₀ r₀ v₀ :=
      e₀.geometricSphereParity_homotopic a₀ r₀ u₀ v₀ H₀
    _ = e₀.sphereParity a₀ v₀ hv₀ hev₀.injective hdv₀ :=
      e₀.geometricSphereParity_eq_of_embedding a₀ r₀ v₀ hv₀ hev₀.injective hdv₀
    _ = e₁.sphereParity a₁ v₁ hv₁ hev₁.injective hdv₁ :=
      d.sphereParity_eq_of_integral_endpoint_images w hd a v₀ v₁
        hv₀ hev₀.injective hdv₀ hv₁ hev₁.injective hdv₁ he'
    _ = e₁.geometricSphereParity a₁ r₁ v₁ :=
      (e₁.geometricSphereParity_eq_of_embedding a₁ r₁ v₁ hv₁ hev₁.injective hdv₁).symm
    _ = e₁.geometricSphereParity a₁ r₁ u₁ :=
      (e₁.geometricSphereParity_homotopic a₁ r₁ u₁ v₁ H₁).symm

end NoExoticSixSphere.RegularCollaredCylinder
