import Wikipedia.SmoothSixDPoincare.HomotopySphereTopology
import Wikipedia.SmoothSixDPoincare.Hemisphere
import Wikipedia.NoExoticSixSphere.SphereConnectivity

/-!
# Low-dimensional nullhomotopies in the original homotopy six-sphere

Smooth approximation and point avoidance contract maps into the standard
six-sphere. The given native homotopy equivalence transfers the contraction
back into the original manifold, without assuming a sphere homeomorphism.
-/

noncomputable section

open ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare

variable {X M : Type*} [TopologicalSpace X] [TopologicalSpace M]

/-- Transfer an actual nullhomotopy through the original homotopy equivalence. -/
theorem nullhomotopic_of_homotopySixSphere_comp (e : M ≃ₕ SixSphere) (g : C(X, M))
    (h : ∃ c, (e.toFun.comp g).Homotopic (ContinuousMap.const X c)) :
    ∃ c, g.Homotopic (ContinuousMap.const X c) := by
  obtain ⟨c, hnull⟩ := h
  have h₀ : (e.invFun.comp (e.toFun.comp g)).Homotopic g :=
    e.left_inv.comp (Homotopic.refl g)
  have h₁ : (e.invFun.comp (e.toFun.comp g)).Homotopic
      (ContinuousMap.const X (e.invFun c)) := (Homotopic.refl e.invFun).comp hnull
  exact ⟨e.invFun c, h₀.symm.trans h₁⟩

/-- Maps from spheres of dimension below six into the homotopy six-sphere contract. -/
theorem sphereMap_nullhomotopic_of_homotopySixSphere (e : M ≃ₕ SixSphere)
    {m : ℕ} (hm : m < 6) (g : C(Hemisphere.Sphere m, M)) :
    ∃ c, g.Homotopic (ContinuousMap.const _ c) :=
  nullhomotopic_of_homotopySixSphere_comp e g
    (NoExoticSixSphere.sphere_sphere_nullhomotopic hm (e.toFun.comp g))

variable {B H : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] (I : ModelWithCorners ℝ B H)
  [I.Boundaryless] [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X] [T2Space X]

include I in
/-- More generally, all continuous maps from compact smooth manifolds of dimension below six
into the original homotopy six-sphere are nullhomotopic. -/
theorem manifoldMap_nullhomotopic_of_homotopySixSphere (e : M ≃ₕ SixSphere)
    (hdim : Module.finrank ℝ B < 6) (g : C(X, M)) :
    ∃ c, g.Homotopic (ContinuousMap.const _ c) :=
  nullhomotopic_of_homotopySixSphere_comp e g
    (NoExoticSixSphere.sphereMap_nullhomotopic_of_dim_lt (I := I) 6 (e.toFun.comp g) hdim)

end Wikipedia.SmoothSixDPoincare
