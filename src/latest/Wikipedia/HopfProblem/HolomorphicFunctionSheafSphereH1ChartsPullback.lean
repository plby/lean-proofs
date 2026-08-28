import Wikipedia.HopfProblem.RiemannSphere
import Wikipedia.HopfProblem.HolomorphicFunctionSheafBasic
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Cover

/-!
# Actual holomorphic section coefficients in both sphere charts

A section on a sphere open set pulls back to an analytic function on
each actual affine-coordinate preimage.  The same extension by zero is
used in both coordinates, so on nonzero reciprocal coordinates the two
coefficient functions agree by the sphere's actual inversion formula.
No stalk or analytic-germ constructions are used here.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

/-- The actual section extended by zero outside its open domain. -/
def sectionExtend (U : Opens RiemannSphere)
    (s : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) (p : RiemannSphere) : ℂ := by
  classical
  exact if hp : p ∈ U then s ⟨p, hp⟩ else 0

@[simp] theorem sectionExtend_apply (U : Opens RiemannSphere)
    (s : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U)
    (p : RiemannSphere) (hp : p ∈ U) :
    sectionExtend U s p = s ⟨p, hp⟩ := by
  classical
  simp only [sectionExtend, dif_pos hp]

theorem sectionExtend_comp_val (U : Opens RiemannSphere)
    (s : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) :
    (fun p : U => sectionExtend U s p) = (s : U → ℂ) :=
  funext fun p => sectionExtend_apply U s p p.property

/-- The extension is holomorphic at every point of the original domain. -/
theorem sectionExtend_contMDiffAt (U : Opens RiemannSphere)
    (s : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U)
    (p : RiemannSphere) (hp : p ∈ U) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (sectionExtend U s) p := by
  apply (contMDiffAt_subtype_iff (x := (⟨p, hp⟩ : U))).mp
  rw [sectionExtend_comp_val U s]
  exact s.contMDiff _

/-- The section's actual finite-coordinate coefficient. -/
def finiteCoefficient (U : Opens RiemannSphere)
    (s : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) (z : ℂ) : ℂ :=
  sectionExtend U s (z : RiemannSphere)

/-- The section's actual reciprocal-coordinate coefficient, including
the coordinate origin corresponding to infinity. -/
def infinityCoefficient (U : Opens RiemannSphere)
    (s : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) (u : ℂ) : ℂ :=
  sectionExtend U s (RiemannSphere.infinityParametrization u)

@[simp] theorem finiteCoefficient_apply (U : Opens RiemannSphere)
    (s : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U)
    (z : ℂ) (hz : (z : RiemannSphere) ∈ U) :
    finiteCoefficient U s z = s ⟨(z : RiemannSphere), hz⟩ :=
  sectionExtend_apply U s _ hz

@[simp] theorem infinityCoefficient_apply (U : Opens RiemannSphere)
    (s : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U)
    (u : ℂ) (hu : RiemannSphere.infinityParametrization u ∈ U) :
    infinityCoefficient U s u = s ⟨RiemannSphere.infinityParametrization u, hu⟩ :=
  sectionExtend_apply U s _ hu

theorem finiteCoefficient_analyticAt (U : Opens RiemannSphere)
    (s : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U)
    (z : ℂ) (hz : (z : RiemannSphere) ∈ U) :
    AnalyticAt ℂ (finiteCoefficient U s) z := by
  have hc : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ((↑) : ℂ → RiemannSphere) :=
    RiemannSphere.standardCharts.affineMap_holomorphic false
  exact ((sectionExtend_contMDiffAt U s _ hz).comp z (hc z)).contDiffAt.analyticAt

theorem infinityCoefficient_analyticAt (U : Opens RiemannSphere)
    (s : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U)
    (u : ℂ) (hu : RiemannSphere.infinityParametrization u ∈ U) :
    AnalyticAt ℂ (infinityCoefficient U s) u := by
  have hc : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω RiemannSphere.infinityParametrization :=
    RiemannSphere.standardCharts.affineMap_holomorphic true
  exact ((sectionExtend_contMDiffAt U s _ hu).comp u (hc u)).contDiffAt.analyticAt

/-- Analyticity on the actual finite-coordinate preimage of the open set. -/
theorem finiteCoefficient_analytic (U : Opens RiemannSphere)
    (s : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) :
    AnalyticOnNhd ℂ (finiteCoefficient U s) (finiteOpen U) :=
  fun z hz => finiteCoefficient_analyticAt U s z hz

/-- Analyticity on the actual reciprocal-coordinate preimage of the open set. -/
theorem infinityCoefficient_analytic (U : Opens RiemannSphere)
    (s : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) :
    AnalyticOnNhd ℂ (infinityCoefficient U s) (infinityOpen U) :=
  fun u hu => infinityCoefficient_analyticAt U s u hu

@[simp] theorem infinityCoefficient_zero (U : Opens RiemannSphere)
    (s : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U)
    (hU : (∞ : RiemannSphere) ∈ U) :
    infinityCoefficient U s 0 = s ⟨(∞ : RiemannSphere), hU⟩ := by
  change sectionExtend U s (RiemannSphere.infinityParametrization 0) = _
  rw [RiemannSphere.infinityParametrization_zero, sectionExtend_apply U s _ hU]

/-- The two actual coefficients satisfy the reciprocal-coordinate
identity, even when the parametrized point lies outside the open set. -/
theorem infinityCoefficient_eq_finiteCoefficient (U : Opens RiemannSphere)
    (s : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U)
    (u : ℂ) (hu : u ≠ 0) :
    infinityCoefficient U s u = finiteCoefficient U s u⁻¹ := by
  change sectionExtend U s (RiemannSphere.infinityParametrization u) = _
  rw [RiemannSphere.infinityParametrization_of_ne hu]
  rfl

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
