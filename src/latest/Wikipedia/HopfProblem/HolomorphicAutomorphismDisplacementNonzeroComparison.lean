import Wikipedia.HopfProblem.HolomorphicAutomorphismDisplacement
import Wikipedia.HopfProblem.HolomorphicAutomorphismTangentLimits
import Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamilyNormalization

/-!
# Changing charts at moving normalization points

Locally uniform convergence of genuine normalized displacements in one
chart controls their values at moving manifold points. The strict
derivative of the actual chart transition transports this limit to any
other native chart containing the limiting point.
-/

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicAutomorphism.Displacement

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [LocallyCompactSpace M] [IsManifold 𝓘(ℂ, E) ω M]

/-- The limit of the actual normalized coordinate displacement at moving
points changes by the genuine derivative of the native chart transition. -/
theorem normalized_moving_change_chart_tendsto (A : CompactAtlas E M)
    {f : ℕ → HolomorphicAutomorphism 𝓘(ℂ, E) M}
    (hf : Tendsto f atTop (𝓝 1)) (hgood : ∀ n, f n ∈ good A)
    (i j : A.Index) {h : E → E}
    (hlim : TendstoLocallyUniformlyOn (fun n => normalized A (f n) j) h atTop
      (A.outerCoordinates j : Set E))
    {x : ℕ → M} {x₀ : M} (hi : x₀ ∈ (A.chart i).source)
    (hj : x₀ ∈ A.outerOpen j) (hx : Tendsto x atTop (𝓝 x₀)) :
    Tendsto
      (fun n => (delta A (f n) : ℂ)⁻¹ •
        (A.chart i (f n (x n)) - A.chart i (x n))) atTop
      (𝓝 (fderiv ℂ ((A.chart i) ∘ (A.chart j).symm) (A.chart j x₀)
        (h (A.chart j x₀)))) := by
  have hxj : Tendsto (fun n => A.chart j (x n)) atTop (𝓝 (A.chart j x₀)) :=
    ((A.chart j).continuousAt hj.1).tendsto.comp hx
  have hnormalized : Tendsto
      (fun n => normalized A (f n) j (A.chart j (x n))) atTop
      (𝓝 (h (A.chart j x₀))) :=
    HolomorphicAutomorphismNormalFamily.tendsto_evaluation_moving
      (A.outerCoordinates j).isOpen hlim
      (Eventually.of_forall fun n => normalized_differentiableOn A (hgood n) j) hj.2 hxj
  have hfx : Tendsto (fun n => f n (x n)) atTop (𝓝 x₀) := by
    have he := (HolomorphicAutomorphism.continuous_eval 𝓘(ℂ, E) M).tendsto
      (1, x₀)
    simpa only [Function.comp_def, HolomorphicAutomorphism.one_apply] using
      he.comp (hf.prodMk_nhds hx)
  have hfxj : Tendsto (fun n => A.chart j (f n (x n))) atTop
      (𝓝 (A.chart j x₀)) :=
    ((A.chart j).continuousAt hj.1).tendsto.comp hfx
  have hmemx : ∀ᶠ n in atTop, x n ∈ (A.chart j).source :=
    hx.eventually ((A.chart j).open_source.mem_nhds hj.1)
  have hmemfx : ∀ᶠ n in atTop, f n (x n) ∈ (A.chart j).source :=
    hfx.eventually ((A.chart j).open_source.mem_nhds hj.1)
  have hscaled : Tendsto
      (fun n => (delta A (f n) : ℂ)⁻¹ •
        (A.chart j (f n (x n)) - A.chart j (x n))) atTop
      (𝓝 (h (A.chart j x₀))) := by
    apply hnormalized.congr'
    filter_upwards [hmemx] with n hn
    simp only [normalized, Coordinates.expression, (A.chart j).left_inv hn]
  have hlin := HolomorphicAutomorphismLinearization.tendsto_scaled_difference
    (HolomorphicAutomorphismTangentLimits.chartTransition_hasStrictFDerivAt
      (A.center j) (A.center i) hj.1 hi) hfxj hxj hscaled
  apply hlin.congr'
  filter_upwards [hmemx, hmemfx] with n hxn hfxn
  change
    (delta A (f n) : ℂ)⁻¹ •
        (A.chart i ((A.chart j).symm (A.chart j (f n (x n)))) -
          A.chart i ((A.chart j).symm (A.chart j (x n)))) =
      (delta A (f n) : ℂ)⁻¹ • (A.chart i (f n (x n)) - A.chart i (x n))
  rw [(A.chart j).left_inv hfxn, (A.chart j).left_inv hxn]

end Wikipedia.HopfProblem.HolomorphicAutomorphism.Displacement
