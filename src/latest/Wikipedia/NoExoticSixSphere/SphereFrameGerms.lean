import Wikipedia.NoExoticSixSphere.ManifoldSphereFrameOperator

/-!
# The actual sphere-frame operator depends only on the local map germ

The ambient extension agrees with radial retraction near the unit sphere.
Equality of sphere-map germs therefore gives equality of actual ambient
derivatives, quaternionic framed derivatives, and the original normal-plus-
derivative operator. No global smoothness of the comparison map is needed.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere

namespace SmoothSphereAmbient

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem extension_eventuallyEq_of_germ (b : Sphere n) {f g : Sphere n → F}
    {x : Sphere n} (h : f =ᶠ[𝓝 x] g) : extension b f =ᶠ[𝓝 x.val] extension b g := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hr : Tendsto (SphereRadialRetraction.retract b) (𝓝 x.val) (𝓝 x) := by
    have hcont := (SphereRadialRetraction.contMDiffAt_retract (n := n) b
      (ne_zero_of_mem_unit_sphere x)).continuousAt
    change Tendsto (SphereRadialRetraction.retract b) (𝓝 x.val)
      (𝓝 (SphereRadialRetraction.retract b x.val)) at hcont
    rwa [SphereRadialRetraction.retract_coe] at hcont
  exact (extension_eventuallyEq_radial b f x).trans
    ((h.comp_tendsto hr).trans (extension_eventuallyEq_radial b g x).symm)

theorem fderiv_extension_eq_of_germ (b : Sphere n) {f g : Sphere n → F}
    {x : Sphere n} (h : f =ᶠ[𝓝 x] g) :
    fderiv ℝ (extension b f) x.val = fderiv ℝ (extension b g) x.val :=
  (extension_eventuallyEq_of_germ b h).fderiv_eq

end SmoothSphereAmbient

namespace SphereThreeTangentFrame

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem framedDerivative_eq_of_germ {f g : Sphere 3 → F} {x : Sphere 3}
    (h : f =ᶠ[𝓝 x] g) : framedDerivative f x = framedDerivative g x := by
  unfold framedDerivative
  rw [SmoothSphereAmbient.fderiv_extension_eq_of_germ (Stiefel.pole 3) h]

end SphereThreeTangentFrame

namespace EuclideanEmbedding

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem sphereFrameOperator_eq_of_germ {f g : Sphere 3 → M} {x : Sphere 3}
    (h : f =ᶠ[𝓝 x] g) : e.sphereFrameOperator a f x = e.sphereFrameOperator a g x := by
  have hv : f x = g x := h.eq_of_nhds
  have he : e.toFun ∘ f =ᶠ[𝓝 x] e.toFun ∘ g := h.mono (fun _ hx ↦ congrArg e.toFun hx)
  unfold sphereFrameOperator
  rw [SphereThreeTangentFrame.framedDerivative_eq_of_germ he]
  change OperatorSum.operator (a.orthonormal (f x)).val _ =
    OperatorSum.operator (a.orthonormal (g x)).val _
  rw [hv]

end EuclideanEmbedding
end NoExoticSixSphere
