import Wikipedia.HopfProblem.HolomorphicFunctionSheafStalkChartSections
import Wikipedia.HopfProblem.HolomorphicFunctionSheafLocalRingEvaluation
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Topology.Sheaves.Stalks

/-!
# Actual holomorphic stalks in boundaryless manifold charts

The ring stalk is the categorical colimit of holomorphic sections on
actual open neighbourhoods.  Pulling each section through the actual
inverse extended chart gives a compatible cocone of analytic germs in
the normed model.  The chart's genuine local inverse identifies equality
of these germs with equality of the original sections near the point.

This gives a ring isomorphism from the actual manifold stalk to actual
analytic germs at its chart coordinate.  Its evaluation agrees with the
independently constructed evaluation map on the categorical stalk.
-/

noncomputable section

open Set Filter Topology TopologicalSpace Opposite CategoryTheory Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf

open CuspNormalization

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H) [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]

/-- A section's actual analytic germ in the given manifold chart. -/
def chartSectionGerm (x : M) (U : Opens M) (hx : x ∈ U) :
    Section I M U →+* Germs.AnalyticGerm (extChartAt I x x) where
  toFun f := Germs.ofAnalytic (chartSectionRepresentative I x U f)
    (chartSectionRepresentative_analyticAt I x U f hx)
  map_zero' := by
    apply Germs.ext
    change (chartSectionRepresentative I x U 0 : Filter.Germ (𝓝 (extChartAt I x x)) ℂ) =
      ((fun _ : E => (0 : ℂ)) : Filter.Germ (𝓝 (extChartAt I x x)) ℂ)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [(chartInverse_tendsto I x).eventually (U.isOpen.mem_nhds hx)] with y hy
    change extendManifoldSection I U 0 ((extChartAt I x).symm y) = 0
    rw [extendManifoldSection_apply I U 0 _ hy]
    rfl
  map_one' := by
    apply Germs.ext
    change (chartSectionRepresentative I x U 1 : Filter.Germ (𝓝 (extChartAt I x x)) ℂ) =
      ((fun _ : E => (1 : ℂ)) : Filter.Germ (𝓝 (extChartAt I x x)) ℂ)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [(chartInverse_tendsto I x).eventually (U.isOpen.mem_nhds hx)] with y hy
    change extendManifoldSection I U 1 ((extChartAt I x).symm y) = 1
    rw [extendManifoldSection_apply I U 1 _ hy]
    rfl
  map_add' f g := by
    apply Germs.ext
    change (chartSectionRepresentative I x U (f + g) :
      Filter.Germ (𝓝 (extChartAt I x x)) ℂ) =
      ((fun y => chartSectionRepresentative I x U f y +
        chartSectionRepresentative I x U g y) : Filter.Germ (𝓝 (extChartAt I x x)) ℂ)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [(chartInverse_tendsto I x).eventually (U.isOpen.mem_nhds hx)] with y hy
    change extendManifoldSection I U (f + g) ((extChartAt I x).symm y) =
      extendManifoldSection I U f ((extChartAt I x).symm y) +
        extendManifoldSection I U g ((extChartAt I x).symm y)
    rw [extendManifoldSection_apply I U (f + g) _ hy,
      extendManifoldSection_apply I U f _ hy, extendManifoldSection_apply I U g _ hy]
    rfl
  map_mul' f g := by
    apply Germs.ext
    change (chartSectionRepresentative I x U (f * g) :
      Filter.Germ (𝓝 (extChartAt I x x)) ℂ) =
      ((fun y => chartSectionRepresentative I x U f y *
        chartSectionRepresentative I x U g y) : Filter.Germ (𝓝 (extChartAt I x x)) ℂ)
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [(chartInverse_tendsto I x).eventually (U.isOpen.mem_nhds hx)] with y hy
    change extendManifoldSection I U (f * g) ((extChartAt I x).symm y) =
      extendManifoldSection I U f ((extChartAt I x).symm y) *
        extendManifoldSection I U g ((extChartAt I x).symm y)
    rw [extendManifoldSection_apply I U (f * g) _ hy,
      extendManifoldSection_apply I U f _ hy, extendManifoldSection_apply I U g _ hy]
    rfl

@[simp] theorem chartSectionGerm_apply (x : M) (U : Opens M) (hx : x ∈ U)
    (f : Section I M U) :
    chartSectionGerm I x U hx f = Germs.ofAnalytic (chartSectionRepresentative I x U f)
      (chartSectionRepresentative_analyticAt I x U f hx) := rfl

/-- Equality in the chart is exactly equality of the original functions
on some neighbourhood in the original manifold. -/
theorem chartSectionGerm_eq_iff (x : M) (U V : Opens M) (hxU : x ∈ U) (hxV : x ∈ V)
    (f : Section I M U) (g : Section I M V) :
    chartSectionGerm I x U hxU f = chartSectionGerm I x V hxV g ↔
      extendManifoldSection I U f =ᶠ[𝓝 x] extendManifoldSection I V g :=
  (Germs.ofAnalytic_eq_iff _ _ (chartSectionRepresentative_analyticAt I x U f hxU)
    (chartSectionRepresentative_analyticAt I x V g hxV)).trans
      (chartSectionRepresentative_eventuallyEq_iff I x U V f g)

/-- The actual coordinate germ is unchanged by literal restriction. -/
theorem chartSectionGerm_restrict (x : M) (U V : Opens M) (h : U ≤ V) (hx : x ∈ U)
    (f : Section I M V) :
    chartSectionGerm I x U hx ((presheaf I M).map (homOfLE h).op f) =
      chartSectionGerm I x V (h hx) f := by
  apply (chartSectionGerm_eq_iff _ _ _ _ _ _ _ _).mpr
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  change extendManifoldSection I U (ContMDiffMap.restrictRingHom I 𝓘(ℂ) ℂ h f) y =
    extendManifoldSection I V f y
  rw [extendManifoldSection_apply I U _ y hy, extendManifoldSection_apply I V f y (h hy)]
  rfl

/-- The chart-coordinate maps form a cocone on the actual stalk diagram. -/
def chartStalkCocone (x : M) :
    Cocone ((OpenNhds.inclusion (X := TopCat.of M) x).op ⋙ presheaf I M) where
  pt := CommRingCat.of (Germs.AnalyticGerm (extChartAt I x x))
  ι :=
    { app := fun U => CommRingCat.ofHom (chartSectionGerm I x U.unop.1 U.unop.2)
      naturality := by
        intro U V i
        ext f
        exact chartSectionGerm_restrict I x V.unop.1 U.unop.1
          (leOfHom i.unop) V.unop.2 f }

/-- The actual colimit comparison morphism in commutative rings. -/
def chartStalkToAnalyticGermHom (x : M) :
    (presheaf I M).stalk x ⟶ CommRingCat.of (Germs.AnalyticGerm (extChartAt I x x)) :=
  colimit.desc _ (chartStalkCocone I x)

/-- The ring map underlying the genuine categorical chart comparison. -/
def chartStalkToAnalyticGerm (x : M) :
    (presheaf I M).stalk x →+* Germs.AnalyticGerm (extChartAt I x x) :=
  (chartStalkToAnalyticGermHom I x).hom

@[simp] theorem chartStalkToAnalyticGerm_germ (x : M) (U : Opens M) (hx : x ∈ U)
    (f : Section I M U) :
    chartStalkToAnalyticGerm I x ((presheaf I M).germ U x hx f) =
      chartSectionGerm I x U hx f := by
  exact congrArg (fun h => h f) (colimit.ι_desc (chartStalkCocone I x) (op ⟨U, hx⟩))

theorem chartStalkToAnalyticGerm_injective (x : M) :
    Function.Injective (chartStalkToAnalyticGerm I x) := by
  intro s t hst
  obtain ⟨U, hxU, f, rfl⟩ := (presheaf I M).exists_germ_eq s
  obtain ⟨V, hxV, g, rfl⟩ := (presheaf I M).exists_germ_eq t
  have hfg : chartSectionGerm I x U hxU f = chartSectionGerm I x V hxV g :=
    (chartStalkToAnalyticGerm_germ I x U hxU f).symm.trans
      (hst.trans (chartStalkToAnalyticGerm_germ I x V hxV g))
  have he := (chartSectionGerm_eq_iff I x U V hxU hxV f g).mp hfg
  have hnbhd : {y : M | y ∈ U ∧ y ∈ V ∧ extendManifoldSection I U f y =
      extendManifoldSection I V g y} ∈ 𝓝 x :=
    inter_mem (U.isOpen.mem_nhds hxU) (inter_mem (V.isOpen.mem_nhds hxV) he)
  obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.mp hnbhd
  let W' : Opens M := ⟨W, hWo⟩
  have hWU : W' ≤ U := fun y hy => (hW hy).1
  have hWV : W' ≤ V := fun y hy => (hW hy).2.1
  apply (presheaf I M).germ_ext W' hxW (homOfLE hWU) (homOfLE hWV)
  apply ContMDiffMap.ext
  intro y
  have hy := (hW y.property).2.2
  rw [extendManifoldSection_apply I U f y (hWU y.property),
    extendManifoldSection_apply I V g y (hWV y.property)] at hy
  exact hy

variable [IsManifold I ω M]

theorem chartStalkToAnalyticGerm_surjective (x : M) :
    Function.Surjective (chartStalkToAnalyticGerm I x) := by
  intro φ
  obtain ⟨U, hx, f, hf⟩ := exists_chart_section_representative I x φ
  refine ⟨(presheaf I M).germ U x hx f, ?_⟩
  exact (chartStalkToAnalyticGerm_germ I x U hx f).trans hf

/-- The genuine categorical stalk of holomorphic functions on a
boundaryless complex manifold is the actual analytic-germ ring in a
genuine chart of that manifold. -/
def chartStalkEquiv (x : M) :
    (presheaf I M).stalk x ≃+* Germs.AnalyticGerm (extChartAt I x x) :=
  RingEquiv.ofBijective (chartStalkToAnalyticGerm I x)
    ⟨chartStalkToAnalyticGerm_injective I x, chartStalkToAnalyticGerm_surjective I x⟩

@[simp] theorem chartStalkEquiv_germ (x : M) (U : Opens M) (hx : x ∈ U)
    (f : Section I M U) :
    chartStalkEquiv I x ((presheaf I M).germ U x hx f) =
      Germs.ofAnalytic (chartSectionRepresentative I x U f)
        (chartSectionRepresentative_analyticAt I x U f hx) :=
  chartStalkToAnalyticGerm_germ I x U hx f

@[simp] theorem eval_chartStalkEquiv_germ (x : M) (U : Opens M) (hx : x ∈ U)
    (f : Section I M U) :
    Germs.eval (extChartAt I x x) (chartStalkEquiv I x ((presheaf I M).germ U x hx f)) =
      f ⟨x, hx⟩ := by
  rw [chartStalkEquiv_germ, Germs.eval_ofAnalytic,
    chartSectionRepresentative_basepoint I x U f hx]

/-- The chart comparison preserves the actual categorical evaluation. -/
theorem eval_comp_chartStalkEquiv (x : M) :
    (Germs.eval (extChartAt I x x)).comp (chartStalkEquiv I x).toRingHom =
      stalkEval I M x := by
  apply RingHom.ext
  intro φ
  obtain ⟨U, hx, f, rfl⟩ := (presheaf I M).exists_germ_eq φ
  exact (eval_chartStalkEquiv_germ I x U hx f).trans (stalkEval_germ I M U x hx f).symm

@[simp] theorem eval_chartStalkEquiv (x : M) (φ : (presheaf I M).stalk x) :
    Germs.eval (extChartAt I x x) (chartStalkEquiv I x φ) = stalkEval I M x φ :=
  congrArg (fun f => f φ) (eval_comp_chartStalkEquiv I x)

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf
