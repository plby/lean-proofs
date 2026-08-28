import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySphereDolbeaultBasic
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Charts

/-!
# The genuine holomorphic kernel of the sphere differential

The actual differential kills actual holomorphic sections. Conversely,
its vanishing forces the Cauchy–Riemann equation in each of the original
sphere charts. The proved chart criterion then supplies an actual
holomorphic section with exactly the original values. These are global
section statements on every actual open set, not assumed stalk data.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.SphereDolbeault

open HolomorphicCousin DolbeaultLocal

/-- The coefficient of an included holomorphic section is genuinely
analytic at each point of its actual coordinate domain. -/
theorem smoothCoefficient_inclusion_analyticAt (U : Opens RiemannSphere)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U)
    (b : Bool) (z : ℂ) (hz : z ∈ SphereForms.coordinateOpen U b) :
    AnalyticAt ℂ (smoothCoefficient U (inclusionSection RiemannSphere U f) b) z := by
  have hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (smoothExtend U (inclusionSection RiemannSphere U f))
      (RiemannSphere.standardCharts.affineMap b z) := by
    apply (contMDiffAt_subtype_iff
      (x := (⟨RiemannSphere.standardCharts.affineMap b z, hz⟩ : U))).mp
    rw [smoothExtend_comp_val]
    exact f.contMDiff _
  exact (hf.comp z (RiemannSphere.standardCharts.affineMap_holomorphic b z)).contDiffAt.analyticAt

/-- The actual antiholomorphic differential of an actual holomorphic
section is the actual zero form. -/
theorem differentialSection_inclusion (U : Opens RiemannSphere)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) :
    differentialSection U (inclusionSection RiemannSphere U f) = 0 := by
  apply SphereForms.section_ext
  intro b z
  change dbar (smoothCoefficient U (inclusionSection RiemannSphere U f) b) z = 0
  exact dbar_eq_zero_of_differentiableAt
    (smoothCoefficient_inclusion_analyticAt U f b z z.property).differentiableAt

/-- Vanishing of the actual differential gives genuine analyticity of
each actual coordinate function on its whole open domain. -/
theorem smoothCoefficient_analytic_of_differential_zero (U : Opens RiemannSphere)
    (s : SmoothSection U) (hs : differentialSection U s = 0) (b : Bool) :
    AnalyticOnNhd ℂ (smoothCoefficient U s b) (SphereForms.coordinateOpen U b) := by
  apply (analyticOnNhd_iff_dbar_zero (SphereForms.coordinateOpen U b).isOpen
    (smoothCoefficient_smooth U s b)).mpr
  intro z hz
  exact congrArg (fun a : SphereForms.Section U => SphereForms.coefficient a b ⟨z, hz⟩) hs

/-- A smooth sphere section with zero actual antiholomorphic
differential has an actual holomorphic preimage on the same open set. -/
theorem exists_holomorphic_preimage (U : Opens RiemannSphere)
    (s : SmoothSection U) (hs : differentialSection U s = 0) :
    ∃ f : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U,
      inclusionSection RiemannSphere U f = s := by
  have hp : ∀ p ∈ U, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (smoothExtend U s) p := by
    intro p hp
    rcases RiemannSphere.standardCharts.covered p with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · exact HolomorphicFunctionSheaf.SphereH1.contMDiffAt_of_comp_affineMap
        (smoothExtend U s) false z
        ((smoothCoefficient_analytic_of_differential_zero U s hs false z hp).contDiffAt)
    · exact HolomorphicFunctionSheaf.SphereH1.contMDiffAt_of_comp_affineMap
        (smoothExtend U s) true z
        ((smoothCoefficient_analytic_of_differential_zero U s hs true z hp).contDiffAt)
  let f : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U :=
    ⟨fun p => smoothExtend U s p,
      fun p => contMDiffAt_subtype_iff.mpr (hp p p.property)⟩
  refine ⟨f, ?_⟩
  apply ContMDiffMap.ext
  intro p
  exact smoothExtend_apply U s p p.property

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.SphereDolbeault
