import Wikipedia.NoExoticSixSphere.IntegralKernelEndpointHomology
import Wikipedia.NoExoticSixSphere.MiddleHomologyKernelObstruction

/-!
# The original endpoint quadratic form on the zero-obstruction kernel

The exact native coefficient obstruction identifies which mod-two kernel
classes have integral kernel representatives. On precisely this subgroup,
the already constructed geometric disk argument proves vanishing of the
original endpoint quadratic form. Integral representatives and their
kernel property are obtained from the proved obstruction criterion.

This does not prove that every obstruction is zero, or settle quadratic
values on classes with nonzero coefficient obstruction. Actual endpoint
and filling two-connectivity remain explicit hypotheses.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology
open Wikipedia.HopfProblem SingularMayerVietoris SphereHomologyCoefficients

namespace NoExoticSixSphere.RegularSlabDiskCollar

open GLOrthonormalization CylinderFiberSlab

variable {m n : ℕ} {z : NoExoticSixSphere.Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := NoExoticSixSphere.Sphere m) (𝓡 m) (𝓡 n) z s t}
  [SimplyConnectedSpace (slab d.map z s t)] (w : slab d.map z s t)
  [hW₂ : Subsingleton (π_ 2 (slab d.map z s t) w)]

include w hW₂ in
theorem quadraticForm_zero_of_endpoint_obstruction_zero (hd : m = n + 6)
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
    letI := TwoConnectedCoefficients.secondHomology_subsingleton x₀
    ∀ (r : EuclideanEmbedding.TubularRetraction
        (RegularSphereFiber.embedding f₀ hf₀ z hreg₀ 6 hd))
      (v : LinearMap.ker (modHomologyMap 2
        (constantEndpointSlabMap f₀ c hcend (hconstant c hc)) 3)),
      MiddleKernelCoefficients.obstruction
        (constantEndpointSlabMap f₀ c hcend (hconstant c hc)) v = 0 →
      (RegularSphereFiber.embedding f₀ hf₀ z hreg₀ 6 hd).modTwoHomologyQuadraticForm
        (RegularSphereFiber.frame f₀ hf₀ z hreg₀ 6 hd a) r x₀ v.val = 0 := by
  let := regularFiberAtlas f₀ hf₀ z hreg₀ 6 (endpointFiber_dimension_eq hd)
  let := regularFiber_isManifold f₀ hf₀ z hreg₀ 6 (endpointFiber_dimension_eq hd)
  let := RegularSphereFiber.fiber_compact f₀ z
  let := TwoConnectedCoefficients.secondHomology_subsingleton x₀
  intro r v hv
  obtain ⟨u, hu, hred⟩ :=
    (MiddleKernelCoefficients.obstruction_zero_iff
      (constantEndpointSlabMap f₀ c hcend (hconstant c hc)) v).mp hv
  rw [← hred]
  exact quadraticForm_zero_on_reduced_integral_endpoint_kernel w hd f₀ hf₀ hreg₀ x₀ U hU
    hconstant c hc hcend a r u hu

end NoExoticSixSphere.RegularSlabDiskCollar
