import Wikipedia.HopfProblem.CuspNormalizationSheafManifoldStalkCoordinates
import Wikipedia.HopfProblem.CuspNormalizationSheafManifoldStalkTranslation
import Wikipedia.HopfProblem.HolomorphicFunctionSheafStalkChart

/-!
# Genuine holomorphic stalks in arbitrary analytic manifold charts

The categorical stalk is identified with actual analytic germs by first
using its canonical chart comparison and then the genuine analytic
coordinate change to the supplied maximal-atlas chart. Translation gives
the centered version. Both comparison formulas use the literal section
extension composed with the actual chart inverse.
-/

noncomputable section

open Set Filter Topology TopologicalSpace IsManifold ChartedSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafManifoldStalk

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
  (e : OpenPartialHomeomorph M E) (he : e ∈ maximalAtlas 𝓘(ℂ, E) ω M)
  (x : M) (hx : x ∈ e.source)

/-- A genuine local section expressed through the supplied inverse chart. -/
def sectionRepresentative (U : Opens M)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, E) M U) : E → ℂ :=
  HolomorphicFunctionSheaf.extendManifoldSection 𝓘(ℂ, E) U f ∘ e.symm

include hx in
omit [IsManifold 𝓘(ℂ, E) ω M] in
@[simp] theorem sectionRepresentative_basepoint (U : Opens M)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, E) M U) (hxU : x ∈ U) :
    sectionRepresentative e U f (e x) = f ⟨x, hxU⟩ := by
  change HolomorphicFunctionSheaf.extendManifoldSection 𝓘(ℂ, E) U f
    (e.symm (e x)) = _
  rw [e.left_inv hx, HolomorphicFunctionSheaf.extendManifoldSection_apply]

include he hx in
omit [IsManifold 𝓘(ℂ, E) ω M] in
theorem sectionRepresentative_analyticAt (U : Opens M)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, E) M U) (hxU : x ∈ U) :
    AnalyticAt ℂ (sectionRepresentative e U f) (e x) := by
  have hf : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ) ω
      (HolomorphicFunctionSheaf.extendManifoldSection 𝓘(ℂ, E) U f)
      (e.symm (e x)) := by
    simpa only [e.left_inv hx] using
      HolomorphicFunctionSheaf.extendManifoldSection_contMDiffAt 𝓘(ℂ, E) U f x hxU
  exact (hf.comp (e x)
    (contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hx))).contDiffAt.analyticAt

/-- The actual commutative-ring stalk in any supplied genuine analytic
chart, not only the chart selected by the charted-space instance. -/
def chartEquiv : (HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, E) M).stalk x ≃+*
    Germs.AnalyticGerm (e x) :=
  (HolomorphicFunctionSheaf.chartStalkEquiv 𝓘(ℂ, E) x).trans
    (coordinateEquiv e (chartAt E x) he (chart_mem_maximalAtlas x)
      x hx (mem_chart_source E x))

/-- The comparison sends a literal categorical section germ to its
actual analytic representative composed with the supplied inverse chart. -/
@[simp] theorem chartEquiv_germ (U : Opens M) (hxU : x ∈ U)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, E) M U) :
    chartEquiv e he x hx
        ((HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, E) M).germ U x hxU f) =
      Germs.ofAnalytic (sectionRepresentative e U f)
        (sectionRepresentative_analyticAt e he x hx U f hxU) := by
  change coordinateEquiv e (chartAt E x) he (chart_mem_maximalAtlas x)
    x hx (mem_chart_source E x)
    (HolomorphicFunctionSheaf.chartStalkEquiv 𝓘(ℂ, E) x
      ((HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, E) M).germ U x hxU f)) = _
  rw [HolomorphicFunctionSheaf.chartStalkEquiv_germ]
  have hf0 : AnalyticAt ℂ
      (HolomorphicFunctionSheaf.chartSectionRepresentative 𝓘(ℂ, E) x U f)
      (chartAt E x x) :=
    HolomorphicFunctionSheaf.chartSectionRepresentative_analyticAt 𝓘(ℂ, E) x U f hxU
  change coordinateEquiv e (chartAt E x) he (chart_mem_maximalAtlas x)
    x hx (mem_chart_source E x)
    (Germs.ofAnalytic
      (HolomorphicFunctionSheaf.chartSectionRepresentative 𝓘(ℂ, E) x U f) hf0) = _
  rw [coordinateEquiv_ofAnalytic]
  apply (Germs.ofAnalytic_eq_iff _ _ _ _).mpr
  have ht : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := (e.symm_map_nhds_eq hx).le
  filter_upwards [ht.eventually
    ((chartAt E x).open_source.mem_nhds (mem_chart_source E x))] with z hz
  change HolomorphicFunctionSheaf.extendManifoldSection 𝓘(ℂ, E) U f
      ((chartAt E x).symm ((chartAt E x) (e.symm z))) =
    HolomorphicFunctionSheaf.extendManifoldSection 𝓘(ℂ, E) U f (e.symm z)
  rw [(chartAt E x).left_inv hz]

@[simp] theorem eval_chartEquiv
    (φ : (HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, E) M).stalk x) :
    Germs.eval (e x) (chartEquiv e he x hx φ) =
      HolomorphicFunctionSheaf.stalkEval 𝓘(ℂ, E) M x φ :=
  (eval_coordinateEquiv e (chartAt E x) he (chart_mem_maximalAtlas x)
    x hx (mem_chart_source E x)
    (HolomorphicFunctionSheaf.chartStalkEquiv 𝓘(ℂ, E) x φ)).trans
      (HolomorphicFunctionSheaf.eval_chartStalkEquiv 𝓘(ℂ, E) x φ)

/-- The actual inverse chart, centered at the coordinate of the point. -/
def centeredRepresentative (U : Opens M)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, E) M U) : E → ℂ :=
  fun z => HolomorphicFunctionSheaf.extendManifoldSection 𝓘(ℂ, E) U f
    (e.symm (e x + z))

include he hx in
omit [IsManifold 𝓘(ℂ, E) ω M] in
theorem centeredRepresentative_analyticAt (U : Opens M)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, E) M U) (hxU : x ∈ U) :
    AnalyticAt ℂ (centeredRepresentative e x U f) (0 : E) :=
  (sectionRepresentative_analyticAt e he x hx U f hxU).comp_of_eq
    (addTranslation_analyticAt (e x) 0) (add_zero (e x))

/-- Actual categorical holomorphic stalks expressed in centered coordinates. -/
def centeredChartEquiv : (HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, E) M).stalk x ≃+*
    Germs.AnalyticGerm (0 : E) :=
  (chartEquiv e he x hx).trans (translateToZero (e x))

@[simp] theorem centeredChartEquiv_apply
    (φ : (HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, E) M).stalk x) :
    centeredChartEquiv e he x hx φ = translateToZero (e x) (chartEquiv e he x hx φ) := rfl

/-- The literal centered section-germ formula used by normalization charts. -/
@[simp] theorem centeredChartEquiv_germ (U : Opens M) (hxU : x ∈ U)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, E) M U) :
    centeredChartEquiv e he x hx
        ((HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, E) M).germ U x hxU f) =
      Germs.ofAnalytic (centeredRepresentative e x U f)
        (centeredRepresentative_analyticAt e he x hx U f hxU) := by
  rw [centeredChartEquiv_apply, chartEquiv_germ, translateToZero_ofAnalytic]
  rfl

@[simp] theorem eval_centeredChartEquiv
    (φ : (HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, E) M).stalk x) :
    Germs.eval (0 : E) (centeredChartEquiv e he x hx φ) =
      HolomorphicFunctionSheaf.stalkEval 𝓘(ℂ, E) M x φ := by
  rw [centeredChartEquiv_apply, eval_translateToZero, eval_chartEquiv]

end Wikipedia.HopfProblem.CuspNormalization.SheafManifoldStalk
