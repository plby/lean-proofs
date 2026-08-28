import Wikipedia.NoExoticSixSphere.IntegralKernelEndpointQuadraticValue
import Wikipedia.HopfProblem.DegreeCollapseEmbeddedSphereRepresentative

/-!
# Quadratic vanishing for every original integral endpoint-kernel class

Replace a continuous sphere by an actual embedded smooth representative
in its original homotopy class. The integral kernel condition is preserved
by that homotopy. Native Hurewicz representatives then give vanishing on
every integral class killed by the actual endpoint inclusion, and on its
mod-two reduction. No mod-two null class is declared integrally null.

This remains a statement about an actually two-connected slab. The
homological corollaries also require the original endpoint to be
two-connected. They do not construct those connectivity properties.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.RegularSlabDiskCollar

open GLOrthonormalization CylinderFiberSlab
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.SphereHomologyCoefficients

variable {m n : ℕ} {z : NoExoticSixSphere.Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := NoExoticSixSphere.Sphere m) (𝓡 m) (𝓡 n) z s t}
  [SimplyConnectedSpace (slab d.map z s t)] (w : slab d.map z s t)
  [hW₂ : Subsingleton (π_ 2 (slab d.map z s t) w)]

include w hW₂ in
theorem geometricSphereParity_zero_of_integral_endpoint_kernel (hd : m = n + 6)
    (f₀ : C(NoExoticSixSphere.Sphere m, NoExoticSixSphere.Sphere n))
    (hf₀ : ContMDiff (𝓡 m) (𝓡 n) ∞ f₀)
    (hreg₀ : ∀ x, f₀ x = z → Surjective (mfderiv (𝓡 m) (𝓡 n) f₀ x))
    [SimplyConnectedSpace {x : NoExoticSixSphere.Sphere m // f₀ x = z}]
    (U : Set ℝ) (hU : IsOpen U)
    (hconstant : ∀ c ∈ U, ∀ x, d.map (c, x) = f₀ x)
    (c : ℝ) (hc : c ∈ U) (hcend : c = s ∨ c = t) (a : NoExoticSixSphere.Sphere m)
    (f : C(NoExoticSixSphere.Sphere 3, {x : NoExoticSixSphere.Sphere m // f₀ x = z})) :
    letI := regularFiberAtlas f₀ hf₀ z hreg₀ 6 (endpointFiber_dimension_eq hd)
    letI := regularFiber_isManifold f₀ hf₀ z hreg₀ 6 (endpointFiber_dimension_eq hd)
    letI := RegularSphereFiber.fiber_compact f₀ z
    ∀ r : EuclideanEmbedding.TubularRetraction
        (RegularSphereFiber.embedding f₀ hf₀ z hreg₀ 6 hd),
      singularHomologyMap (constantEndpointSlabMap f₀ c hcend (hconstant c hc)) 3
        (SmoothCube.integralSphereClass f) = 0 →
      (RegularSphereFiber.embedding f₀ hf₀ z hreg₀ 6 hd).geometricSphereParity
        (RegularSphereFiber.frame f₀ hf₀ z hreg₀ 6 hd a) r f = 0 := by
  let := regularFiberAtlas f₀ hf₀ z hreg₀ 6 (endpointFiber_dimension_eq hd)
  let := regularFiber_isManifold f₀ hf₀ z hreg₀ 6 (endpointFiber_dimension_eq hd)
  let := RegularSphereFiber.fiber_compact f₀ z
  intro r hker
  let e := RegularSphereFiber.embedding f₀ hf₀ z hreg₀ 6 hd
  let a₀ := RegularSphereFiber.frame f₀ hf₀ z hreg₀ 6 hd a
  obtain ⟨g, hgs, H, hgd, hge⟩ :=
    Wikipedia.HopfProblem.DegreeCollapse.TripleParameters.exists_embedded_sphere_representative
      e r f
  have hkerG : singularHomologyMap (constantEndpointSlabMap f₀ c hcend (hconstant c hc)) 3
      (SmoothCube.integralSphereClass g) = 0 := by
    rw [← SmoothCube.integralSphereClass_homotopic H]
    exact hker
  calc
    e.geometricSphereParity a₀ r f = e.geometricSphereParity a₀ r g :=
      e.geometricSphereParity_homotopic a₀ r f g H
    _ = e.sphereParity a₀ g hgs hge.injective hgd :=
      e.geometricSphereParity_eq_of_embedding a₀ r g hgs hge.injective hgd
    _ = 0 := sphereParity_zero_of_integral_endpoint_kernel w hd f₀ hf₀ hreg₀ U hU hconstant
      c hc hcend a g hgs hge.injective hgd hkerG

include w hW₂ in
theorem integralHomologyParity_zero_of_endpoint_kernel (hd : m = n + 6)
    (f₀ : C(NoExoticSixSphere.Sphere m, NoExoticSixSphere.Sphere n))
    (hf₀ : ContMDiff (𝓡 m) (𝓡 n) ∞ f₀)
    (hreg₀ : ∀ x, f₀ x = z → Surjective (mfderiv (𝓡 m) (𝓡 n) f₀ x))
    [SimplyConnectedSpace {x : NoExoticSixSphere.Sphere m // f₀ x = z}]
    (x₀ : {x : NoExoticSixSphere.Sphere m // f₀ x = z})
    [Subsingleton (π_ 2 {x : NoExoticSixSphere.Sphere m // f₀ x = z} x₀)]
    (U : Set ℝ) (hU : IsOpen U)
    (hconstant : ∀ c ∈ U, ∀ x, d.map (c, x) = f₀ x)
    (c : ℝ) (hc : c ∈ U) (hcend : c = s ∨ c = t) (a : NoExoticSixSphere.Sphere m) :
    letI := regularFiberAtlas f₀ hf₀ z hreg₀ 6 (endpointFiber_dimension_eq hd)
    letI := regularFiber_isManifold f₀ hf₀ z hreg₀ 6 (endpointFiber_dimension_eq hd)
    letI := RegularSphereFiber.fiber_compact f₀ z
    ∀ (r : EuclideanEmbedding.TubularRetraction
        (RegularSphereFiber.embedding f₀ hf₀ z hreg₀ 6 hd))
      (u : SingularHomology {x : NoExoticSixSphere.Sphere m // f₀ x = z} 3),
      singularHomologyMap (constantEndpointSlabMap f₀ c hcend (hconstant c hc)) 3 u = 0 →
      (RegularSphereFiber.embedding f₀ hf₀ z hreg₀ 6 hd).integralHomologyParity
        (RegularSphereFiber.frame f₀ hf₀ z hreg₀ 6 hd a) r x₀ u = 0 := by
  let := regularFiberAtlas f₀ hf₀ z hreg₀ 6 (endpointFiber_dimension_eq hd)
  let := regularFiber_isManifold f₀ hf₀ z hreg₀ 6 (endpointFiber_dimension_eq hd)
  let := RegularSphereFiber.fiber_compact f₀ z
  intro r u hker
  exact geometricSphereParity_zero_of_integral_endpoint_kernel w hd f₀ hf₀ hreg₀ U hU
    hconstant c hc hcend a (SmoothCube.integralClassRepresentative x₀ u).val r
      (by rw [SmoothCube.integralSphereClass_representative]; exact hker)

include w hW₂ in
theorem quadraticForm_zero_on_reduced_integral_endpoint_kernel (hd : m = n + 6)
    (f₀ : C(NoExoticSixSphere.Sphere m, NoExoticSixSphere.Sphere n))
    (hf₀ : ContMDiff (𝓡 m) (𝓡 n) ∞ f₀)
    (hreg₀ : ∀ x, f₀ x = z → Surjective (mfderiv (𝓡 m) (𝓡 n) f₀ x))
    [SimplyConnectedSpace {x : NoExoticSixSphere.Sphere m // f₀ x = z}]
    (x₀ : {x : NoExoticSixSphere.Sphere m // f₀ x = z})
    [Subsingleton (π_ 2 {x : NoExoticSixSphere.Sphere m // f₀ x = z} x₀)]
    (U : Set ℝ) (hU : IsOpen U)
    (hconstant : ∀ c ∈ U, ∀ x, d.map (c, x) = f₀ x)
    (c : ℝ) (hc : c ∈ U) (hcend : c = s ∨ c = t) (a : NoExoticSixSphere.Sphere m) :
    letI := regularFiberAtlas f₀ hf₀ z hreg₀ 6 (endpointFiber_dimension_eq hd)
    letI := regularFiber_isManifold f₀ hf₀ z hreg₀ 6 (endpointFiber_dimension_eq hd)
    letI := RegularSphereFiber.fiber_compact f₀ z
    ∀ (r : EuclideanEmbedding.TubularRetraction
        (RegularSphereFiber.embedding f₀ hf₀ z hreg₀ 6 hd))
      (u : SingularHomology {x : NoExoticSixSphere.Sphere m // f₀ x = z} 3),
      singularHomologyMap (constantEndpointSlabMap f₀ c hcend (hconstant c hc)) 3 u = 0 →
      (RegularSphereFiber.embedding f₀ hf₀ z hreg₀ 6 hd).modTwoHomologyQuadraticForm
        (RegularSphereFiber.frame f₀ hf₀ z hreg₀ 6 hd a) r x₀
          (reductionHomologyMap 2 {x : NoExoticSixSphere.Sphere m // f₀ x = z} 3 u) = 0 := by
  let := regularFiberAtlas f₀ hf₀ z hreg₀ 6 (endpointFiber_dimension_eq hd)
  let := regularFiber_isManifold f₀ hf₀ z hreg₀ 6 (endpointFiber_dimension_eq hd)
  let := RegularSphereFiber.fiber_compact f₀ z
  intro r u hker
  let e := RegularSphereFiber.embedding f₀ hf₀ z hreg₀ 6 hd
  rw [e.modTwoHomologyQuadraticForm_apply, e.modTwoHomologyParity_reduction]
  exact integralHomologyParity_zero_of_endpoint_kernel w hd f₀ hf₀ hreg₀ x₀ U hU hconstant
    c hc hcend a r u hker

end NoExoticSixSphere.RegularSlabDiskCollar
