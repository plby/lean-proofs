import Wikipedia.HopfProblem.RiemannSphere
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Holomorphic tangent coordinates on the Riemann sphere

Tangent-bundle trivializations are holomorphic over their chart sources, and
holomorphicity of a vector-field section can be tested in any such chart.
-/

open Bundle Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.RiemannSphere.HolomorphicVectorFields

/-- The fiber component of an analytic tangent trivialization is holomorphic
where its base point belongs to the corresponding sphere chart. -/
theorem tangent_coordinate_contMDiffAt (x₀ : RiemannSphere)
    {p : TangentBundle 𝓘(ℂ) RiemannSphere}
    (hp : p.1 ∈ (chartAt ℂ x₀).source) :
    ContMDiffAt 𝓘(ℂ).tangent 𝓘(ℂ) ω
      (fun q : TangentBundle 𝓘(ℂ) RiemannSphere =>
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ)) x₀ q).2) p := by
  have hp' : p ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ)) x₀).source := by
    simpa only [TangentBundle.trivializationAt_source, mem_preimage] using hp
  exact (((trivializationAt ℂ (TangentSpace 𝓘(ℂ)) x₀).contMDiffAt_iff
    (IB := 𝓘(ℂ)) (IM := 𝓘(ℂ).tangent) (n := ω) (f := id) hp').mp
      contMDiffAt_id).2

/-- A tangent coordinate is holomorphic on the preimage of its sphere chart. -/
theorem tangent_coordinate_contMDiffOn (x₀ : RiemannSphere) :
    ContMDiffOn 𝓘(ℂ).tangent 𝓘(ℂ) ω
      (fun q : TangentBundle 𝓘(ℂ) RiemannSphere =>
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ)) x₀ q).2)
      ((fun q : TangentBundle 𝓘(ℂ) RiemannSphere => q.1) ⁻¹'
        (chartAt ℂ x₀).source) := by
  intro p hp
  exact (tangent_coordinate_contMDiffAt x₀ hp).contMDiffWithinAt

/-- A section is holomorphic at a point if and only if its coordinate in any
chart containing that point is holomorphic there. -/
theorem tangent_section_contMDiffAt_iff (x₀ : RiemannSphere)
    {V : ∀ x : RiemannSphere, TangentSpace 𝓘(ℂ) x} {x : RiemannSphere}
    (hx : x ∈ (chartAt ℂ x₀).source) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ).tangent ω
      (fun y => TotalSpace.mk' ℂ y (V y)) x ↔
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun y => (trivializationAt ℂ (TangentSpace 𝓘(ℂ)) x₀ ⟨y, V y⟩).2) x := by
  apply (trivializationAt ℂ (TangentSpace 𝓘(ℂ)) x₀).contMDiffAt_section_iff
    (IB := 𝓘(ℂ)) (n := ω)
  simpa only [TangentBundle.trivializationAt_baseSet] using hx

/-- A section is holomorphic throughout a chart source if and only if its
fiber coordinate in that chart is holomorphic throughout that source. -/
theorem tangent_section_contMDiffOn_iff (x₀ : RiemannSphere)
    {V : ∀ x : RiemannSphere, TangentSpace 𝓘(ℂ) x} :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ).tangent ω
      (fun y => TotalSpace.mk' ℂ y (V y)) (chartAt ℂ x₀).source ↔
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω
      (fun y => (trivializationAt ℂ (TangentSpace 𝓘(ℂ)) x₀ ⟨y, V y⟩).2)
      (chartAt ℂ x₀).source := by
  simpa only [TangentBundle.trivializationAt_baseSet] using
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ)) x₀).contMDiffOn_section_baseSet_iff
      (IB := 𝓘(ℂ)) (n := ω) (s := V)

end Wikipedia.HopfProblem.RiemannSphere.HolomorphicVectorFields
