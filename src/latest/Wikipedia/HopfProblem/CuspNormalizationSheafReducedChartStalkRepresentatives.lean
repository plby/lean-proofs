import Wikipedia.HopfProblem.CuspNormalizationSheafReduced
import Wikipedia.HopfProblem.CuspNormalizationSheafReducedChartStalkTopology
import Wikipedia.HopfProblem.HolomorphicFunctionSheafStalkChartSections

/-!
# Actual analytic representatives in arbitrary genuine manifold charts

An actual reduced holomorphic section has an ambient holomorphic
representative locally. Its literal function, expressed in a genuine
ambient chart, therefore agrees along the chart image of the subset
with an analytic function. Conversely, every analytic function germ in
that chart restricts to an actual reduced holomorphic section.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafReduced

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The literal relative section function in an actual ambient chart,
extended by zero outside its relative domain before chart transport. -/
def chartReducedRepresentative (e : OpenPartialHomeomorph M E)
    (S : Set M) (U : Opens S) (f : Section 𝓘(ℂ, E) S U) : E → ℂ :=
  relativeExtension S U f.val ∘ e.symm

/-- The literal ambient section function in an actual ambient chart,
extended by zero outside its open domain before chart transport. -/
def chartAmbientRepresentative (e : OpenPartialHomeomorph M E)
    (V : Opens M) (g : HolomorphicFunctionSheaf.Section 𝓘(ℂ, E) M V) : E → ℂ :=
  HolomorphicFunctionSheaf.extendManifoldSection 𝓘(ℂ, E) V g ∘ e.symm

/-- Expressing an actual ambient holomorphic section in any genuine
holomorphic chart gives an analytic representative at its basepoint. -/
theorem chartAmbientRepresentative_analyticAt (e : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) ω M)
    (x : M) (hx : x ∈ e.source) (V : Opens M) (hxV : x ∈ V)
    (g : HolomorphicFunctionSheaf.Section 𝓘(ℂ, E) M V) :
    AnalyticAt ℂ (chartAmbientRepresentative e V g) (e x) := by
  have hg : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ) ω
      (HolomorphicFunctionSheaf.extendManifoldSection 𝓘(ℂ, E) V g)
      (e.symm (e x)) := by
    rw [e.left_inv hx]
    exact HolomorphicFunctionSheaf.extendManifoldSection_contMDiffAt
      𝓘(ℂ, E) V g x hxV
  exact (hg.comp (e x)
    (contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hx))).contDiffAt.analyticAt

/-- Actual ambient restriction agrees in the chart with the actual
ambient section, as a within-subset germ. -/
theorem chartReducedRepresentative_ambientRestriction_eventuallyEq
    (e : OpenPartialHomeomorph M E) (S : Set M) (x : S)
    (hx : x.val ∈ e.source) (V : Opens M) (hxV : x.val ∈ V)
    (g : HolomorphicFunctionSheaf.Section 𝓘(ℂ, E) M V) :
    chartReducedRepresentative e S (ambientOpen S V)
        (ambientRestriction 𝓘(ℂ, E) S V g)
      =ᶠ[𝓝[chartSubset e S] (e x.val)] chartAmbientRepresentative e V g := by
  have hlocal : relativeExtension S (ambientOpen S V)
      (ambientRestriction 𝓘(ℂ, E) S V g).val
      =ᶠ[𝓝[S] x.val]
        HolomorphicFunctionSheaf.extendManifoldSection 𝓘(ℂ, E) V g := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (V.isOpen.mem_nhds hxV)] with y hyS hyV
    rw [relativeExtension_apply S (ambientOpen S V) _ y hyS hyV,
      HolomorphicFunctionSheaf.extendManifoldSection_apply 𝓘(ℂ, E) V g y hyV]
    rfl
  exact hlocal.comp_tendsto (chart_symm_tendsto e S x hx)

/-- Every actual reduced section has an analytic representative in a
genuine chart, agreeing with its literal function along the chart subset. -/
theorem exists_chart_analytic_representative (e : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) ω M)
    (S : Set M) (x : S) (hx : x.val ∈ e.source)
    (U : Opens S) (hxU : x ∈ U) (f : Section 𝓘(ℂ, E) S U) :
    ∃ g : E → ℂ, AnalyticAt ℂ g (e x.val) ∧
      chartReducedRepresentative e S U f
        =ᶠ[𝓝[chartSubset e S] (e x.val)] g := by
  obtain ⟨V, hxV, g, hg⟩ := f.property ⟨x, hxU⟩
  refine ⟨chartAmbientRepresentative e V g,
    chartAmbientRepresentative_analyticAt e he x.val hx V hxV g, ?_⟩
  have hlocal : relativeExtension S U f.val =ᶠ[𝓝[S] x.val]
      HolomorphicFunctionSheaf.extendManifoldSection 𝓘(ℂ, E) V g := by
    filter_upwards [eventually_mem_openSubset S x U hxU,
      mem_nhdsWithin_of_mem_nhds (V.isOpen.mem_nhds hxV)] with y hy hyV
    obtain ⟨hyS, hyU⟩ := hy
    rw [relativeExtension_apply S U f.val y hyS hyU,
      HolomorphicFunctionSheaf.extendManifoldSection_apply 𝓘(ℂ, E) V g y hyV]
    exact hg ⟨⟨y, hyS⟩, hyU⟩ hyV
  exact hlocal.comp_tendsto (chart_symm_tendsto e S x hx)

variable [IsManifold 𝓘(ℂ, E) ω M]

/-- Every analytic germ in a genuine ambient chart restricts to an
actual local reduced holomorphic section on the original subset. -/
theorem exists_reduced_section_of_chart_analyticAt (e : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) ω M)
    (S : Set M) (x : S) (hx : x.val ∈ e.source) {F : E → ℂ}
    (hF : AnalyticAt ℂ F (e x.val)) :
    ∃ (U : Opens S) (_hxU : x ∈ U) (f : Section 𝓘(ℂ, E) S U),
      chartReducedRepresentative e S U f
        =ᶠ[𝓝[chartSubset e S] (e x.val)] F := by
  have hcomp : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ) ω (F ∘ e) x.val :=
    hF.contDiffAt.contMDiffAt.comp x.val (contMDiffAt_of_mem_maximalAtlas he hx)
  obtain ⟨V, hxV, g, hg⟩ :=
    HolomorphicFunctionSheaf.exists_manifold_section_of_contMDiffAt 𝓘(ℂ, E) hcomp
  refine ⟨ambientOpen S V, hxV, ambientRestriction 𝓘(ℂ, E) S V g,
    (chartReducedRepresentative_ambientRestriction_eventuallyEq
      e S x hx V hxV g).trans ?_⟩
  have hlocal := HolomorphicFunctionSheaf.extendManifoldSection_eventuallyEq
    𝓘(ℂ, E) V g x.val hxV (F ∘ e) hg
  have hchart : chartAmbientRepresentative e V g
      =ᶠ[𝓝[chartSubset e S] (e x.val)] (F ∘ e) ∘ e.symm :=
    hlocal.comp_tendsto ((e.tendsto_symm hx).mono_left nhdsWithin_le_nhds)
  filter_upwards [hchart, self_mem_nhdsWithin] with y hy hyS
  exact hy.trans (congrArg F (e.right_inv hyS.1))

end Wikipedia.HopfProblem.CuspNormalization.SheafReduced
