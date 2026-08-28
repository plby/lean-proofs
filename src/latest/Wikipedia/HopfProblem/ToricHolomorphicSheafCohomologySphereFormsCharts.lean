import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySphereFormsBasic

/-!
# The underlying real smooth sphere and its actual affine charts

The real smooth atlas is the original sphere atlas: its actual complex
analytic inversion transitions are smooth after restricting scalars.
The same two actual parametrizations and their inverses are consequently
real smooth maps on their actual chart domains.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.SphereForms

/-- Complex analytic maps in one-dimensional complex charts are real
smooth maps in the same underlying charts. -/
theorem contMDiff_real_of_complex {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace ℂ M] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω M] [IsManifold 𝓘(ℂ) ω N]
    [IsManifold 𝓘(ℝ, ℂ) ∞ M] [IsManifold 𝓘(ℝ, ℂ) ∞ N] {f : M → N}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f := by
  rcases contMDiff_iff.mp hf with ⟨hc, hd⟩
  apply contMDiff_iff.mpr
  refine ⟨hc, fun x y => ?_⟩
  exact ((hd x y).restrict_scalars ℝ).of_le le_top

/-- The constructed analytic sphere has its genuine underlying real
smooth structure on exactly the original charted space. -/
instance realIsManifold : IsManifold 𝓘(ℝ, ℂ) ∞ RiemannSphere := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨b, rfl⟩ := he
  obtain ⟨c, rfl⟩ := he'
  have h := (RiemannSphere.standardCharts.transition_holomorphic b c).restrict_scalars ℝ
  simpa using h.of_le (show (∞ : ℕ∞ω) ≤ ω from le_top)

/-- The actual affine parametrizations are real smooth. -/
theorem affineMap_smooth (b : Bool) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (RiemannSphere.standardCharts.affineMap b) :=
  contMDiff_real_of_complex (RiemannSphere.standardCharts.affineMap_holomorphic b)

/-- Each of the original affine charts belongs to the real smooth atlas. -/
theorem chart_mem_realMaximalAtlas (b : Bool) :
    (RiemannSphere.standardCharts.parametrization b).symm ∈
      IsManifold.maximalAtlas 𝓘(ℝ, ℂ) ∞ RiemannSphere :=
  IsManifold.subset_maximalAtlas (mem_range_self b)

/-- The actual coordinate inverse is real smooth throughout its actual
chart image in the sphere. -/
theorem chartInverse_smoothOn (b : Bool) :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (RiemannSphere.standardCharts.parametrization b).symm
      (range (RiemannSphere.standardCharts.affineMap b)) := by
  have h := contMDiffOn_of_mem_maximalAtlas (chart_mem_realMaximalAtlas b)
  simpa only [OpenPartialHomeomorph.symm_source, TwoAffineCharts.parametrization_target] using h

/-- The genuine smooth coordinate function on an actual sphere open
subset lying in this chart image. -/
def chartInverseOn (b : Bool) (U : Opens RiemannSphere)
    (hU : (U : Set RiemannSphere) ⊆ range (RiemannSphere.standardCharts.affineMap b)) :
    SmoothFunctions.Section 𝓘(ℝ, ℂ) RiemannSphere U := by
  refine ⟨fun p => (RiemannSphere.standardCharts.parametrization b).symm p, ?_⟩
  intro p
  apply contMDiffAt_subtype_iff.mpr
  exact (chartInverse_smoothOn b).contMDiffAt
    ((RiemannSphere.standardCharts.affineMap_isOpenEmbedding b).isOpen_range.mem_nhds
      (hU p.property))

@[simp] theorem chartInverseOn_apply (b : Bool) (U : Opens RiemannSphere)
    (hU : (U : Set RiemannSphere) ⊆ range (RiemannSphere.standardCharts.affineMap b)) (p : U) :
    chartInverseOn b U hU p = (RiemannSphere.standardCharts.parametrization b).symm p := rfl

/-- The coordinate function really inverts the original affine parametrization. -/
theorem chartInverseOn_affineMap (b : Bool) (U : Opens RiemannSphere)
    (hU : (U : Set RiemannSphere) ⊆ range (RiemannSphere.standardCharts.affineMap b))
    (z : ℂ) (hz : z ∈ coordinateOpen U b) :
    chartInverseOn b U hU ⟨RiemannSphere.standardCharts.affineMap b z, hz⟩ = z :=
  RiemannSphere.standardCharts.parametrization_symm_apply b z

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.SphereForms
