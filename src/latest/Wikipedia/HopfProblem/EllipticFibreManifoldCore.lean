import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Complex.Basic

/-!
# The analytic atlas induced on an embedded fibre

An actual homeomorphism onto a subset identifies its points with the source
of a holomorphic immersion.  The selected source charts are the immersion's
normal-form charts.  The identities below show that these are exactly the
restrictions of ambient charts to a coordinate hyperplane.  The topology
of the subset is its original subspace topology throughout.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.EmbeddedFibre

variable {E V F X M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace X] [ChartedSpace E X]
    [TopologicalSpace M] [ChartedSpace V M]
    {S : Set M} (e : X ≃ₜ S)
    (hι : Manifold.IsImmersionOfComplement F (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ V) ω (Subtype.val ∘ e))

local notation "I" => modelWithCornersSelf ℂ E
local notation "J" => modelWithCornersSelf ℂ V

def chart (x : S) : OpenPartialHomeomorph S E :=
  e.symm.toOpenPartialHomeomorph.trans (hι (e.symm x)).domChart

def ambientChart (x : S) : OpenPartialHomeomorph M V :=
  (hι (e.symm x)).codChart

def coordinateEquiv (x : S) : (E × F) ≃L[ℂ] V := (hι (e.symm x)).equiv

@[simp] theorem chart_apply (x y : S) :
    chart e hι x y = (hι (e.symm x)).domChart (e.symm y) := rfl

@[simp] theorem chart_symm_apply (x : S) (z : E) :
    (chart e hι x).symm z = e ((hι (e.symm x)).domChart.symm z) := rfl

@[simp] theorem chart_source (x : S) :
    (chart e hι x).source = e.symm ⁻¹' (hι (e.symm x)).domChart.source := by
  simp [chart]

@[simp] theorem chart_target (x : S) :
    (chart e hι x).target = (hι (e.symm x)).domChart.target := by
  simp [chart]

theorem mem_chart_source (x : S) : x ∈ (chart e hι x).source := by
  rw [chart_source]
  exact (hι (e.symm x)).mem_domChart_source

/-- Every selected fibre-chart source lies in its corresponding ambient
normal-form chart. -/
theorem chart_source_subset_ambientSource (x : S) :
    (chart e hι x).source ⊆ Subtype.val ⁻¹' (ambientChart e hι x).source := by
  intro y hy
  have hy' : e.symm y ∈ (hι (e.symm x)).domChart.source := by
    simpa only [chart_source, Set.mem_preimage] using hy
  have h := (hι (e.symm x)).source_subset_preimage_source hy'
  simpa only [Set.mem_preimage, Function.comp_apply, e.apply_symm_apply, ambientChart] using h

/-- In an ambient normal-form chart, the fibre-chart inverse is the
standard coordinate inclusion with the given complement. -/
theorem ambientChart_chart_symm (x : S) {z : E} (hz : z ∈ (chart e hι x).target) :
    ambientChart e hι x ((chart e hι x).symm z : M) = coordinateEquiv e hι x (z, 0) := by
  have hz' : z ∈ (hι (e.symm x)).domChart.target := by
    simpa only [chart_target] using hz
  exact (hι (e.symm x)).writtenInCharts
    (by simpa [OpenPartialHomeomorph.extend] using hz')

/-- This formula explicitly identifies the inverse fibre chart with the
restriction of the inverse ambient chart to its coordinate hyperplane. -/
theorem chart_symm_ambient (x : S) {z : E} (hz : z ∈ (chart e hι x).target) :
    ((chart e hι x).symm z : M) =
      (ambientChart e hι x).symm (coordinateEquiv e hι x (z, 0)) := by
  have hm := chart_source_subset_ambientSource e hι x ((chart e hι x).map_target hz)
  calc
    _ = (ambientChart e hι x).symm
        (ambientChart e hι x ((chart e hι x).symm z : M)) :=
      ((ambientChart e hι x).left_inv hm).symm
    _ = _ := congrArg (ambientChart e hι x).symm (ambientChart_chart_symm e hι x hz)

theorem ambientChart_apply (x : S) {y : S} (hy : y ∈ (chart e hι x).source) :
    ambientChart e hι x (y : M) = coordinateEquiv e hι x (chart e hι x y, 0) := by
  have h := ambientChart_chart_symm e hι x ((chart e hι x).map_source hy)
  rwa [(chart e hι x).left_inv hy] at h

theorem coordinateEquiv_symm_ambientChart (x : S) {y : S}
    (hy : y ∈ (chart e hι x).source) :
    (coordinateEquiv e hι x).symm (ambientChart e hι x (y : M)) =
      (chart e hι x y, 0) := by
  rw [ambientChart_apply e hι x hy, ContinuousLinearEquiv.symm_apply_apply]

theorem chart_eq_ambient_projection (x : S) {y : S}
    (hy : y ∈ (chart e hι x).source) :
    chart e hι x y =
      ((coordinateEquiv e hι x).symm (ambientChart e hι x (y : M))).1 := by
  rw [coordinateEquiv_symm_ambientChart e hι x hy]

/-- Each selected fibre chart is the exact restriction of a maximal-atlas
ambient chart: its source is the full intersection with the subset, and
both coordinate normal-form identities hold on the selected chart domains. -/
theorem exists_ambient_restriction (x : S) :
    ∃ c : OpenPartialHomeomorph M V,
      c ∈ IsManifold.maximalAtlas J ω M ∧
      (chart e hι x).source = Subtype.val ⁻¹' c.source ∧
      (∀ y : S, y ∈ (chart e hι x).source →
        c (y : M) = coordinateEquiv e hι x (chart e hι x y, 0)) ∧
      (∀ z : E, z ∈ (chart e hι x).target →
        ((chart e hι x).symm z : M) = c.symm (coordinateEquiv e hι x (z, 0))) := by
  obtain ⟨U, hU, hEq⟩ := IsInducing.subtypeVal.isOpen_iff.mp (chart e hι x).open_source
  let c := (ambientChart e hι x).restr U
  refine ⟨c, restr_mem_maximalAtlas _ (hι (e.symm x)).codChart_mem_maximalAtlas hU,
    ?_, ?_, ?_⟩
  · change (chart e hι x).source =
      Subtype.val ⁻¹' ((ambientChart e hι x).restr U).source
    rw [OpenPartialHomeomorph.restr_source' _ _ hU, Set.preimage_inter, hEq]
    exact (Set.inter_eq_right.mpr (chart_source_subset_ambientSource e hι x)).symm
  · intro y hy
    exact ambientChart_apply e hι x hy
  · intro z hz
    exact chart_symm_ambient e hι x hz

theorem transition_holomorphic (x y : S) :
    ContDiffOn ℂ ω ((chart e hι x).symm.trans (chart e hι y))
      ((chart e hι x).symm.trans (chart e hι y)).source := by
  let T := ((chart e hι x).symm.trans (chart e hι y)).source
  have hx : ContMDiffOn I I ω (hι (e.symm x)).domChart.symm T :=
    (contMDiffOn_symm_of_mem_maximalAtlas (hι (e.symm x)).domChart_mem_maximalAtlas).mono
      (fun z hz => by simpa only [OpenPartialHomeomorph.symm_symm, chart_target] using hz.1)
  have hh : ContMDiffOn I I ω
      ((hι (e.symm y)).domChart ∘ (hι (e.symm x)).domChart.symm) T := by
    apply (contMDiffOn_of_mem_maximalAtlas (hι (e.symm y)).domChart_mem_maximalAtlas).comp hx
    intro z hz
    have h := hz.2
    simpa only [OpenPartialHomeomorph.symm_symm, chart_source, Set.mem_preimage,
      chart_symm_apply, e.symm_apply_apply] using h
  apply hh.contDiffOn.congr
  intro z _
  simp only [OpenPartialHomeomorph.trans_apply, chart_apply, chart_symm_apply,
    e.symm_apply_apply, Function.comp_apply]

@[instance_reducible] def chartedSpace : ChartedSpace E S where
  atlas := range (chart e hι)
  chartAt := chart e hι
  mem_chart_source := mem_chart_source e hι
  chart_mem_atlas _ := mem_range_self _

theorem isManifold :
    letI := chartedSpace e hι
    IsManifold I ω S := by
  let := chartedSpace e hι
  apply isManifold_of_contDiffOn
  intro c d hc hd
  obtain ⟨x, rfl⟩ := hc
  obtain ⟨y, rfl⟩ := hd
  simpa using transition_holomorphic e hι x y

/-- The inclusion of the actual subset is an immersion for its induced
atlas, with exactly the original normal-form coordinate complement. -/
theorem inclusion_isImmersionOfComplement :
    letI := chartedSpace e hι
    Manifold.IsImmersionOfComplement F I J ω (Subtype.val : S → M) := by
  let := chartedSpace e hι
  let := isManifold e hι
  intro x
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    (coordinateEquiv e hι x) (chart e hι x) (ambientChart e hι x)
    (mem_chart_source e hι x)
    (chart_source_subset_ambientSource e hι x (mem_chart_source e hι x))
    (IsManifold.chart_mem_maximalAtlas x) (hι (e.symm x)).codChart_mem_maximalAtlas
    (chart_source_subset_ambientSource e hι x) ?_
  intro z hz
  have hz' : z ∈ (chart e hι x).target := by
    simpa [OpenPartialHomeomorph.extend] using hz
  exact ambientChart_chart_symm e hι x hz'

theorem inclusion_holomorphic :
    letI := chartedSpace e hι
    ContMDiff I J ω (Subtype.val : S → M) := by
  let := chartedSpace e hι
  exact (inclusion_isImmersionOfComplement e hι).contMDiff

end Wikipedia.HopfProblem.EmbeddedFibre
