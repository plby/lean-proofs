import Wikipedia.HopfProblem.HolomorphicFunctionSheafBasic
import Wikipedia.HopfProblem.CuspNormalizationGermsBasic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Holomorphic sections and analytic germs in actual manifold charts

The actual chart inverse identifies neighbourhood filters on a
boundaryless complex manifold and its model space.  Extending a local
section by zero and composing with that inverse therefore gives an
analytic representative whose germ detects precisely the original
section's neighbourhood germ.  Conversely, every analytic model germ
comes from a genuine local holomorphic section on the manifold.

All maps use the given manifold charts and topology.  No completeness
or finite-dimensionality assumption on the model space is needed.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf

open CuspNormalization

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  [TopologicalSpace M] [ChartedSpace H M]

/-- The literal extension by zero of a local holomorphic section on
the original manifold. -/
def extendManifoldSection (U : Opens M) (f : Section I M U) (x : M) : ℂ := by
  classical
  exact if hx : x ∈ U then f ⟨x, hx⟩ else 0

@[simp] theorem extendManifoldSection_apply (U : Opens M) (f : Section I M U)
    (x : M) (hx : x ∈ U) :
    extendManifoldSection I U f x = f ⟨x, hx⟩ := by
  classical
  simp only [extendManifoldSection, dif_pos hx]

theorem extendManifoldSection_comp_val (U : Opens M) (f : Section I M U) :
    (fun x : U => extendManifoldSection I U f x) = (f : U → ℂ) :=
  funext fun x => extendManifoldSection_apply I U f x x.property

/-- Extension by zero is holomorphic at each point of the original
section domain; no claim is made at the domain's boundary. -/
theorem extendManifoldSection_contMDiffAt (U : Opens M) (f : Section I M U)
    (x : M) (hx : x ∈ U) :
    ContMDiffAt I 𝓘(ℂ) ω (extendManifoldSection I U f) x := by
  apply (contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))).mp
  rw [extendManifoldSection_comp_val I U f]
  exact f.contMDiff _

theorem extendManifoldSection_eventuallyEq (U : Opens M) (s : Section I M U)
    (x : M) (hx : x ∈ U) (f : M → ℂ)
    (hs : ∀ y (hy : y ∈ U), s ⟨y, hy⟩ = f y) :
    extendManifoldSection I U s =ᶠ[𝓝 x] f := by
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  rw [extendManifoldSection_apply I U s y hy]
  exact hs y hy

/-- A local section expressed in the actual extended chart at `x`. -/
def chartSectionRepresentative (x : M) (U : Opens M) (f : Section I M U) : E → ℂ :=
  extendManifoldSection I U f ∘ (extChartAt I x).symm

@[simp] theorem chartSectionRepresentative_basepoint (x : M) (U : Opens M)
    (f : Section I M U) (hx : x ∈ U) :
    chartSectionRepresentative I x U f (extChartAt I x x) = f ⟨x, hx⟩ := by
  change extendManifoldSection I U f ((extChartAt I x).symm (extChartAt I x x)) = _
  rw [(extChartAt I x).left_inv (mem_extChartAt_source x),
    extendManifoldSection_apply I U f x hx]

variable [I.Boundaryless]

/-- In a boundaryless model the actual chart inverse maps the whole
model-space neighbourhood filter to the original manifold filter. -/
theorem chartInverse_map_nhds (x : M) :
    Filter.map (extChartAt I x).symm (𝓝 (extChartAt I x x)) = 𝓝 x := by
  simpa only [ModelWithCorners.Boundaryless.range_eq_univ, nhdsWithin_univ] using
    map_extChartAt_symm_nhdsWithin_range (I := I) x

theorem chartInverse_tendsto (x : M) :
    Tendsto (extChartAt I x).symm (𝓝 (extChartAt I x x)) (𝓝 x) :=
  (chartInverse_map_nhds I x).le

/-- The model-space representative of a holomorphic section is
analytic at the actual coordinate of its base point. -/
theorem chartSectionRepresentative_analyticAt (x : M) (U : Opens M)
    (f : Section I M U) (hx : x ∈ U) :
    AnalyticAt ℂ (chartSectionRepresentative I x U f) (extChartAt I x x) := by
  have h := contMDiffAt_iff_source.mp (extendManifoldSection_contMDiffAt I U f x hx)
  rw [ModelWithCorners.Boundaryless.range_eq_univ, contMDiffWithinAt_univ] at h
  exact h.contDiffAt.analyticAt

/-- Equality of the chart representatives is exactly equality of the
original section extensions as actual neighbourhood germs on the manifold. -/
theorem chartSectionRepresentative_eventuallyEq_iff (x : M) (U V : Opens M)
    (f : Section I M U) (g : Section I M V) :
    chartSectionRepresentative I x U f =ᶠ[𝓝 (extChartAt I x x)]
        chartSectionRepresentative I x V g ↔
      extendManifoldSection I U f =ᶠ[𝓝 x] extendManifoldSection I V g := by
  change extendManifoldSection I U f =ᶠ[Filter.map (extChartAt I x).symm
      (𝓝 (extChartAt I x x))] extendManifoldSection I V g ↔ _
  rw [chartInverse_map_nhds I x]

variable [IsManifold I ω M]

omit [I.Boundaryless] in
/-- A function holomorphic at one point restricts to an actual
holomorphic section on some open neighbourhood of that point. -/
theorem exists_manifold_section_of_contMDiffAt {x : M} {f : M → ℂ}
    (hf : ContMDiffAt I 𝓘(ℂ) ω f x) :
    ∃ (U : Opens M) (_hx : x ∈ U) (s : Section I M U),
      ∀ y (hy : y ∈ U), s ⟨y, hy⟩ = f y := by
  obtain ⟨V, hV, hfV⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp hf
  obtain ⟨U, hUV, hU, hxU⟩ := mem_nhds_iff.mp hV
  let U' : Opens M := ⟨U, hU⟩
  have hs : ContMDiff I 𝓘(ℂ) ω (fun y : U' => f y) := by
    intro y
    apply contMDiffAt_subtype_iff.mpr
    exact hfV.contMDiffAt (mem_of_superset (hU.mem_nhds y.property) hUV)
  exact ⟨U', hxU, ⟨fun y => f y, hs⟩, fun _ _ => rfl⟩

/-- Every analytic model representative is the chart representative
of an actual local holomorphic section, as a neighbourhood germ. -/
theorem exists_chart_section_of_analyticAt (x : M) {f : E → ℂ}
    (hf : AnalyticAt ℂ f (extChartAt I x x)) :
    ∃ (U : Opens M) (_hx : x ∈ U) (s : Section I M U),
      chartSectionRepresentative I x U s =ᶠ[𝓝 (extChartAt I x x)] f := by
  have hcomp : ContMDiffAt I 𝓘(ℂ) ω (f ∘ extChartAt I x) x :=
    hf.contDiffAt.contMDiffAt.comp x contMDiffAt_extChartAt
  obtain ⟨U, hx, s, hs⟩ := exists_manifold_section_of_contMDiffAt I hcomp
  refine ⟨U, hx, s, ?_⟩
  have he := extendManifoldSection_eventuallyEq I U s x hx (f ∘ extChartAt I x) hs
  have hlocal := he.comp_tendsto (chartInverse_tendsto I x)
  filter_upwards [hlocal, extChartAt_target_mem_nhds (I := I) x] with z hz hzt
  exact hz.trans (congrArg f ((extChartAt I x).right_inv hzt))

/-- Every actual analytic germ at the chart coordinate is represented
by a holomorphic section on an actual open manifold neighbourhood. -/
theorem exists_chart_section_representative (x : M)
    (φ : Germs.AnalyticGerm (extChartAt I x x)) :
    ∃ (U : Opens M) (hx : x ∈ U) (s : Section I M U),
      Germs.ofAnalytic (chartSectionRepresentative I x U s)
        (chartSectionRepresentative_analyticAt I x U s hx) = φ := by
  obtain ⟨f, hf, hφ⟩ := Germs.exists_representative φ
  obtain ⟨U, hx, s, hs⟩ := exists_chart_section_of_analyticAt I x hf
  refine ⟨U, hx, s, Eq.trans ?_ hφ⟩
  exact (Germs.ofAnalytic_eq_iff _ _ _ _).mpr hs

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf
