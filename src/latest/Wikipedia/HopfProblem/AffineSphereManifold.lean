import Wikipedia.HopfProblem.AffineSphere
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The analytic atlas of a two-chart sphere

The two affine parametrizations are open embeddings by `AffineSphere`.
Their inverse charts form an analytic atlas: its transitions are the
identity or complex inversion on the punctured line. Holomorphicity of
a map out of this manifold can be checked on the two affine lines.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TwoAffineCharts

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] (A : TwoAffineCharts Y)

def affineMap (b : Bool) : ℂ → Y := if b then A.right else A.left

theorem affineMap_isOpenEmbedding (b : Bool) : IsOpenEmbedding (A.affineMap b) := by
  cases b
  · exact A.left_isOpenEmbedding
  · exact A.right_isOpenEmbedding

theorem affineMap_injective (b : Bool) : Function.Injective (A.affineMap b) :=
  (A.affineMap_isOpenEmbedding b).injective

omit [T2Space Y] in
theorem affineMap_cross_eq_iff (b : Bool) (z w : ℂ) :
    A.affineMap b z = A.affineMap (!b) w ↔ z ≠ 0 ∧ w = z⁻¹ := by
  cases b
  · exact A.cross_eq_iff z w
  · exact A.symm.cross_eq_iff z w

omit [T2Space Y] in
theorem affineMap_inversion (b : Bool) (z : ℂ) (hz : z ≠ 0) :
    A.affineMap b z = A.affineMap (!b) z⁻¹ :=
  (A.affineMap_cross_eq_iff b z z⁻¹).mpr ⟨hz, rfl⟩

def parametrization (b : Bool) : OpenPartialHomeomorph ℂ Y :=
  (A.affineMap_isOpenEmbedding b).toOpenPartialHomeomorph (A.affineMap b)

@[simp] theorem parametrization_apply (b : Bool) (z : ℂ) :
    A.parametrization b z = A.affineMap b z := rfl

@[simp] theorem parametrization_source (b : Bool) : (A.parametrization b).source = univ := rfl

@[simp] theorem parametrization_target (b : Bool) :
    (A.parametrization b).target = range (A.affineMap b) := by simp [parametrization]

@[simp] theorem parametrization_symm_apply (b : Bool) (z : ℂ) :
    (A.parametrization b).symm (A.affineMap b z) = z :=
  (A.parametrization b).left_inv (Set.mem_univ z)

theorem transition_cross (b : Bool) (z : ℂ)
    (hz : z ∈ ((A.parametrization b).trans (A.parametrization (!b)).symm).source) :
    z ≠ 0 ∧ ((A.parametrization b).trans (A.parametrization (!b)).symm) z = z⁻¹ := by
  have hy : A.affineMap b z ∈ range (A.affineMap (!b)) := by simpa using hz.2
  obtain ⟨w, hw⟩ := hy
  have hn := ((A.affineMap_cross_eq_iff b z w).mp hw.symm).1
  refine ⟨hn, ?_⟩
  change (A.parametrization (!b)).symm (A.affineMap b z) = z⁻¹
  rw [A.affineMap_inversion b z hn, parametrization_symm_apply]

theorem transition_holomorphic (b c : Bool) :
    ContDiffOn ℂ ω ((A.parametrization b).trans (A.parametrization c).symm)
      ((A.parametrization b).trans (A.parametrization c).symm).source := by
  by_cases hbc : b = c
  · subst c
    apply contDiffOn_id.congr
    intro z _
    exact A.parametrization_symm_apply b z
  · have hc : c = !b := by cases b <;> cases c <;> simp_all
    subst c
    have hi : ContDiffOn ℂ ω (fun z : ℂ => z⁻¹)
        ((A.parametrization b).trans (A.parametrization (!b)).symm).source := by
      intro z hz
      exact (contDiffAt_inv ℂ (A.transition_cross b z hz).1).contDiffWithinAt
    exact hi.congr (fun z hz => (A.transition_cross b z hz).2)

def preferredChart (y : Y) : Bool := by
  classical
  exact if y ∈ range A.left then false else true

omit [T2Space Y] in
theorem preferred_mem (y : Y) : y ∈ range (A.affineMap (A.preferredChart y)) := by
  classical
  by_cases hy : y ∈ range A.left
  · simp [preferredChart, hy, affineMap]
  · obtain h | h := A.covered y
    · exact False.elim (hy h)
    · simpa [preferredChart, hy, affineMap] using h

@[instance_reducible] def chartedSpace : ChartedSpace ℂ Y where
  atlas := range (fun b : Bool => (A.parametrization b).symm)
  chartAt y := (A.parametrization (A.preferredChart y)).symm
  mem_chart_source y := by
    change y ∈ (A.parametrization (A.preferredChart y)).target
    rw [parametrization_target]
    exact A.preferred_mem y
  chart_mem_atlas _ := mem_range_self _

theorem isManifold :
    letI := A.chartedSpace
    IsManifold (modelWithCornersSelf ℂ ℂ) ω Y := by
  let := A.chartedSpace
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨b, rfl⟩ := he
  obtain ⟨c, rfl⟩ := he'
  simpa using A.transition_holomorphic b c

theorem affineMap_holomorphic (b : Bool) :
    letI := A.chartedSpace
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω (A.affineMap b) := by
  let := A.chartedSpace
  let := A.isManifold
  have he : (A.parametrization b).symm ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ω Y :=
    IsManifold.subset_maximalAtlas (mem_range_self b)
  have h := contMDiffOn_symm_of_mem_maximalAtlas he
  change ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
    (A.affineMap b) univ at h
  exact contMDiffOn_univ.mp h

theorem contMDiff_of_comp_affineMaps {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
    (I : ModelWithCorners ℂ F H) (f : Y → N)
    (hf : ∀ b, ContMDiff (modelWithCornersSelf ℂ ℂ) I ω (f ∘ A.affineMap b)) :
    letI := A.chartedSpace
    ContMDiff (modelWithCornersSelf ℂ ℂ) I ω f := by
  let := A.chartedSpace
  intro y
  rw [contMDiffAt_iff_source]
  have hchart : chartAt ℂ y = (A.parametrization (A.preferredChart y)).symm := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, Function.comp_def] using
    (hf (A.preferredChart y)).contMDiffAt.contMDiffWithinAt
      (s := univ) (x := (A.parametrization (A.preferredChart y)).symm y)

end Wikipedia.HopfProblem.TwoAffineCharts
