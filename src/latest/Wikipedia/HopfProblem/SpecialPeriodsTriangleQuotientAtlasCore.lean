import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Analytic quotient atlases from local inverse branches

This file constructs a complex atlas on a topological quotient from genuine
open partial homeomorphisms. Their pullbacks to the original complex charted
space are required to be holomorphic. At overlaps of distinct charts, a local
inverse branch of the first pulled-back coordinate proves compatibility.

The diagonal transition is the identity, so no inverse branch is required at
a ramification point covered by only one chart. The quotient is not given any
manifold structure in the input.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.BranchedQuotientAtlas

variable {E M Q : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q]

local notation "Iₑ" => modelWithCornersSelf ℂ E

/-- A local inverse of a pulled-back quotient coordinate gives the actual
inverse quotient chart after projecting, near the specified coordinate. -/
theorem project_localInverse_eventuallyEq {q : M → Q} (hq : Continuous q)
    (e : OpenPartialHomeomorph Q E) {z : E} (hz : z ∈ e.target)
    {a : M} (ha : q a = e.symm z)
    (hf : IsLocalDiffeomorphAt Iₑ Iₑ ω (e ∘ q) a) :
    q ∘ hf.localInverse =ᶠ[𝓝 z] e.symm := by
  have hcoord : (e ∘ q) a = z := by
    simp only [Function.comp_apply, ha, e.right_inv hz]
  have hinv : hf.localInverse z = a := by
    rw [← hcoord]
    exact hf.localInverse_left_inv hf.localInverse_mem_target
  have hcont : ContinuousAt (q ∘ hf.localInverse) z := by
    have h := hq.continuousAt.comp hf.localInverse_contMDiffAt.continuousAt
    simpa only [hcoord] using h
  have hsource : ∀ᶠ w in 𝓝 z, q (hf.localInverse w) ∈ e.source :=
    hcont (e.open_source.mem_nhds (by
      simpa only [Function.comp_apply, hinv, ha] using e.map_target hz))
  have hright : ∀ᶠ w in 𝓝 z, e (q (hf.localInverse w)) = w := by
    rw [← hcoord]
    exact hf.localInverse_eventuallyEq_right
  filter_upwards [hsource, hright] with w hw he
  change q (hf.localInverse w) = e.symm w
  exact (e.left_inv hw).symm.trans (congrArg e.symm he)

/-- A transition is holomorphic at a coordinate whenever the first coordinate
has a local inverse upstairs and the second coordinate is holomorphic upstairs. -/
theorem contDiffAt_transition_of_lift {q : M → Q} (hq : Continuous q)
    (e f : OpenPartialHomeomorph Q E)
    (hhol : ContMDiffOn Iₑ Iₑ ω (f ∘ q) (q ⁻¹' f.source))
    {z : E} (hz : z ∈ (e.symm.trans f).source)
    {a : M} (ha : q a = e.symm z)
    (hf : IsLocalDiffeomorphAt Iₑ Iₑ ω (e ∘ q) a) :
    ContDiffAt ℂ ω (e.symm.trans f) z := by
  have hcoord : (e ∘ q) a = z := by
    simp only [Function.comp_apply, ha, e.right_inv hz.1]
  have hinv : hf.localInverse z = a := by
    rw [← hcoord]
    exact hf.localInverse_left_inv hf.localInverse_mem_target
  have hfirst : ContMDiffAt Iₑ Iₑ ω hf.localInverse z := by
    simpa only [hcoord] using hf.localInverse_contMDiffAt
  have hsecond : ContMDiffAt Iₑ Iₑ ω (f ∘ q) a :=
    hhol.contMDiffAt ((f.open_source.preimage hq).mem_nhds (by
      change q a ∈ f.source
      rw [ha]
      exact hz.2))
  have hcomp : ContDiffAt ℂ ω ((f ∘ q) ∘ hf.localInverse) z :=
    (hsecond.comp_of_eq hfirst hinv).contDiffAt
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [project_localInverse_eventuallyEq hq e hz.1 ha hf] with w hw
  change f (e.symm w) = f (q (hf.localInverse w))
  exact congrArg f hw.symm

/-- The topological charts and local analytic data used to construct the
quotient's complex atlas. Surjectivity of the projection is not needed for
this construction: the overlap-lift field supplies every lift used in the proof. -/
structure Data (q : M → Q) (ι : Type*) where
  chart : ι → OpenPartialHomeomorph Q E
  cover : ∀ x : Q, ∃ i, x ∈ (chart i).source
  continuous_project : Continuous q
  pullback_contMDiff : ∀ i,
    ContMDiffOn Iₑ Iₑ ω (chart i ∘ q) (q ⁻¹' (chart i).source)
  overlap_lift : ∀ i j, i ≠ j → ∀ z ∈ ((chart i).symm.trans (chart j)).source,
    ∃ a : M, q a = (chart i).symm z ∧
      IsLocalDiffeomorphAt Iₑ Iₑ ω (chart i ∘ q) a

namespace Data

variable {q : M → Q} {ι : Type*} (D : Data (E := E) q ι)

/-- Select a chart from the given covering family. -/
def indexAt (x : Q) : ι := (D.cover x).choose

theorem mem_chart_source (x : Q) : x ∈ (D.chart (D.indexAt x)).source :=
  (D.cover x).choose_spec

/-- The actual charted-space structure has exactly the supplied chart family
as its atlas. It does not transport an unrelated manifold structure. -/
@[instance_reducible] def chartedSpace : ChartedSpace E Q where
  atlas := range D.chart
  chartAt x := D.chart (D.indexAt x)
  mem_chart_source := D.mem_chart_source
  chart_mem_atlas x := mem_range_self (D.indexAt x)

theorem chart_mem_atlas (i : ι) :
    letI := D.chartedSpace
    D.chart i ∈ atlas E Q :=
  mem_range_self i

theorem chartAt_eq (x : Q) :
    letI := D.chartedSpace
    chartAt E x = D.chart (D.indexAt x) := rfl

/-- Every transition is analytic. The self-transition is dealt with directly
as the identity; only genuinely different charts use inverse branches. -/
theorem contDiffOn_transition (i j : ι) :
    ContDiffOn ℂ ω ((D.chart i).symm.trans (D.chart j))
      ((D.chart i).symm.trans (D.chart j)).source := by
  intro z hz
  by_cases hij : i = j
  · subst j
    apply contDiffWithinAt_id.congr_of_mem ?_ hz
    intro w hw
    exact (D.chart i).right_inv hw.1
  · obtain ⟨a, ha, hf⟩ := D.overlap_lift i j hij z hz
    exact (contDiffAt_transition_of_lift D.continuous_project
      (D.chart i) (D.chart j) (D.pullback_contMDiff j) hz ha hf).contDiffWithinAt

/-- The supplied quotient charts, with their proved transitions, make the
original quotient topology into a complex analytic manifold. -/
theorem isManifold :
    letI := D.chartedSpace
    IsManifold Iₑ ω Q := by
  let := D.chartedSpace
  apply isManifold_of_contDiffOn
  rintro e f ⟨i, rfl⟩ ⟨j, rfl⟩
  simpa using D.contDiffOn_transition i j

/-- The original projection is holomorphic for the constructed quotient
atlas, because every supplied coordinate pulls back holomorphically. -/
theorem contMDiff_project :
    letI := D.chartedSpace
    ContMDiff Iₑ Iₑ ω q := by
  let := D.chartedSpace
  let := D.isManifold
  intro a
  have hsource := D.mem_chart_source (q a)
  have hhol := (D.pullback_contMDiff (D.indexAt (q a))).contMDiffAt
    (((D.chart (D.indexAt (q a))).open_source.preimage D.continuous_project).mem_nhds
      hsource)
  apply (contMDiffAt_iff_target_of_mem_source (I := Iₑ) (I' := Iₑ)
    (D.mem_chart_source (q a))).mpr
  refine ⟨D.continuous_project.continuousAt, ?_⟩
  simpa [extChartAt, OpenPartialHomeomorph.extend, D.chartAt_eq,
    Function.comp_def] using hhol

end Data

end Wikipedia.HopfProblem.BranchedQuotientAtlas
