import Wikipedia.HopfProblem.CuspNormalizationSheafReducedStalkImage
import Wikipedia.HopfProblem.CuspNormalizationSheafReducedChartStalkRepresentatives

/-!
# Reduced sections give actual restricted analytic germs in genuine charts

The chart germ of a section is its actual function, extended by zero
outside its relative domain, composed with the actual inverse chart.
Local ambient holomorphic representatives put that within-subset germ
in the literal analytic restriction image. No chart-stalk isomorphism
is assumed in this construction.
-/

noncomputable section

open Set Filter Topology TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafReduced

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]
  (e : OpenPartialHomeomorph M E) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, E) ω M)
  (S : Set M) (x : S) (hx : x.val ∈ e.source)

/-- The actual chart-coordinate germ of a reduced holomorphic section. -/
def chartSectionGerm (U : Opens S) (hxU : x ∈ U) :
    Section 𝓘(ℂ, E) S U →+*
      RestrictedAnalyticGermImage (chartSubset e S) (chartPoint e S x hx) where
  toFun f := ⟨(chartReducedRepresentative e S U f :
      Filter.Germ (𝓝[chartSubset e S] (e x.val)) ℂ), by
    obtain ⟨g, hg, hfg⟩ := exists_chart_analytic_representative e he S x hx U hxU f
    exact ⟨Germs.ofAnalytic g hg, Filter.Germ.coe_eq.mpr hfg.symm⟩⟩
  map_zero' := by
    apply Subtype.ext
    change (chartReducedRepresentative e S U 0 :
      Filter.Germ (𝓝[chartSubset e S] (e x.val)) ℂ) =
        ((fun _ : E => (0 : ℂ)) : Filter.Germ (𝓝[chartSubset e S] (e x.val)) ℂ)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [(chart_symm_tendsto e S x hx).eventually
      (eventually_mem_openSubset S x U hxU)] with y hy
    obtain ⟨hyS, hyU⟩ := hy
    change relativeExtension S U (0 : Section 𝓘(ℂ, E) S U).val (e.symm y) = 0
    rw [relativeExtension_apply S U _ (e.symm y) hyS hyU]
    rfl
  map_one' := by
    apply Subtype.ext
    change (chartReducedRepresentative e S U 1 :
      Filter.Germ (𝓝[chartSubset e S] (e x.val)) ℂ) =
        ((fun _ : E => (1 : ℂ)) : Filter.Germ (𝓝[chartSubset e S] (e x.val)) ℂ)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [(chart_symm_tendsto e S x hx).eventually
      (eventually_mem_openSubset S x U hxU)] with y hy
    obtain ⟨hyS, hyU⟩ := hy
    change relativeExtension S U (1 : Section 𝓘(ℂ, E) S U).val (e.symm y) = 1
    rw [relativeExtension_apply S U _ (e.symm y) hyS hyU]
    rfl
  map_add' f g := by
    apply Subtype.ext
    change (chartReducedRepresentative e S U (f + g) :
      Filter.Germ (𝓝[chartSubset e S] (e x.val)) ℂ) =
        ((fun y => chartReducedRepresentative e S U f y +
          chartReducedRepresentative e S U g y) :
            Filter.Germ (𝓝[chartSubset e S] (e x.val)) ℂ)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [(chart_symm_tendsto e S x hx).eventually
      (eventually_mem_openSubset S x U hxU)] with y hy
    obtain ⟨hyS, hyU⟩ := hy
    change relativeExtension S U (f + g).val (e.symm y) =
      relativeExtension S U f.val (e.symm y) + relativeExtension S U g.val (e.symm y)
    rw [relativeExtension_apply S U (f + g).val (e.symm y) hyS hyU,
      relativeExtension_apply S U f.val (e.symm y) hyS hyU,
      relativeExtension_apply S U g.val (e.symm y) hyS hyU]
    rfl
  map_mul' f g := by
    apply Subtype.ext
    change (chartReducedRepresentative e S U (f * g) :
      Filter.Germ (𝓝[chartSubset e S] (e x.val)) ℂ) =
        ((fun y => chartReducedRepresentative e S U f y *
          chartReducedRepresentative e S U g y) :
            Filter.Germ (𝓝[chartSubset e S] (e x.val)) ℂ)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [(chart_symm_tendsto e S x hx).eventually
      (eventually_mem_openSubset S x U hxU)] with y hy
    obtain ⟨hyS, hyU⟩ := hy
    change relativeExtension S U (f * g).val (e.symm y) =
      relativeExtension S U f.val (e.symm y) * relativeExtension S U g.val (e.symm y)
    rw [relativeExtension_apply S U (f * g).val (e.symm y) hyS hyU,
      relativeExtension_apply S U f.val (e.symm y) hyS hyU,
      relativeExtension_apply S U g.val (e.symm y) hyS hyU]
    rfl

@[simp] theorem chartSectionGerm_coe (U : Opens S) (hxU : x ∈ U)
    (f : Section 𝓘(ℂ, E) S U) :
    (chartSectionGerm e he S x hx U hxU f).val =
        (chartReducedRepresentative e S U f :
          Filter.Germ (𝓝[chartSubset e S] (e x.val)) ℂ) := rfl

/-- Chart-germ equality detects equality of the original actual
within-subset function germs on the manifold. -/
theorem chartSectionGerm_eq_iff (U V : Opens S) (hxU : x ∈ U) (hxV : x ∈ V)
    (f : Section 𝓘(ℂ, E) S U) (g : Section 𝓘(ℂ, E) S V) :
    chartSectionGerm e he S x hx U hxU f = chartSectionGerm e he S x hx V hxV g ↔
      relativeExtension S U f.val =ᶠ[𝓝[S] x.val] relativeExtension S V g.val :=
  (Subtype.ext_iff.trans Filter.Germ.coe_eq).trans
    (chart_comp_symm_eventuallyEq_iff e S x hx
      (relativeExtension S U f.val) (relativeExtension S V g.val))

/-- Literal restriction does not change the actual chart-coordinate germ. -/
theorem chartSectionGerm_restrict (U V : Opens S) (h : U ≤ V) (hxU : x ∈ U)
    (f : Section 𝓘(ℂ, E) S V) :
    chartSectionGerm e he S x hx U hxU (restriction 𝓘(ℂ, E) S h f) =
      chartSectionGerm e he S x hx V (h hxU) f := by
  apply (chartSectionGerm_eq_iff e he S x hx U V hxU (h hxU) _ f).mpr
  filter_upwards [eventually_mem_openSubset S x U hxU] with y hy
  obtain ⟨hyS, hyU⟩ := hy
  rw [relativeExtension_apply S U _ y hyS hyU,
    relativeExtension_apply S V f.val y hyS (h hyU)]
  rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafReduced
