import Wikipedia.SmoothSixDPoincare.RegularLevelCoordinates
import Wikipedia.SmoothSixDPoincare.ManifoldCriticalPoints

/-! # Native regular-height coordinates with a fixed codimension-one Euclidean model -/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.RegularLevel

abbrev Model (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E - 1))

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The original function is the first coordinate near every native regular point.
All such charts use the same Euclidean model of dimension `dim E - 1`. -/
theorem exists_native_height_chart {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {x : M}
    (hx : x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, ℝ × Model E) M (ℝ × Model E) ∞,
      x ∈ Φ.source ∧ (∀ y ∈ Φ.source, (Φ y).1 = f y) ∧ Φ x = (f x, 0) := by
  let e := chartAt E x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas x
  have hxe : x ∈ e.source := mem_chart_source E x
  let c : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M E ∞ :=
    { e.toPartialEquiv with
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he }
  have hreg : fderiv ℝ (f ∘ e.symm) (e x) ≠ 0 :=
    fun h => hx ((ManifoldMorse.mem_criticalPoints_iff hf he hxe).mpr h)
  obtain ⟨d, hd, -, hfirst, hcenter⟩ := exists_height_partialDiffeomorph
    e.open_target (e.map_source hxe) (ManifoldMorse.contDiffOn_chartExpression hf he) hreg
  let L := fderiv ℝ (f ∘ e.symm) (e x)
  have hdim : Module.finrank ℝ L.ker = Module.finrank ℝ (Model E) := by
    have hh := finrank_kernel_add_one hreg
    change Module.finrank ℝ L.ker + 1 = Module.finrank ℝ E at hh
    rw [finrank_euclideanSpace_fin]
    omega
  let j : L.ker ≃L[ℝ] Model E := ContinuousLinearEquiv.ofFinrankEq hdim
  let J : (ℝ × L.ker) ≃L[ℝ] (ℝ × Model E) :=
    (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr j
  let τ := J.toDiffeomorph.toPartialDiffeomorph
  refine ⟨(c.trans d).trans τ, ⟨⟨hxe, hd⟩, mem_univ _⟩, ?_, ?_⟩
  · intro y hy
    change (d (e y)).1 = f y
    rw [hfirst]
    exact congrArg f (e.left_inv hy.1.1)
  · change J (d (e x)) = (f x, 0)
    rw [hcenter]
    change (f (e.symm (e x)), j 0) = (f x, 0)
    rw [e.left_inv hxe, map_zero]

end Wikipedia.SmoothSixDPoincare.RegularLevel
