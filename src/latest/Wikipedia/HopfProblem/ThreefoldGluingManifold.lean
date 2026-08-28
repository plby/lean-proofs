import Wikipedia.HopfProblem.ThreefoldGluing
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Complex.Basic

/-!
# Complex manifolds obtained by the actual gluing over a covered base

Local complex charts are transported through the canonical open
parametrizations of the topological gluing.  Holomorphic overlap maps
give compatible complex charts on the glued space; no global complex
structure is assumed as part of the gluing data.
-/

noncomputable section

open Set Topology
open scoped ContDiff

universe u

namespace Wikipedia.HopfProblem.ThreefoldGluing.Data

variable {B : Type u} [TopologicalSpace B] (D : ThreefoldGluing.Data B)
    [∀ i, Nonempty (D.piece i)]
    {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)]

@[simp] theorem parametrization_symm_inclusion (i : D.J) (x : D.piece i) :
    (D.parametrization i).symm (D.inclusion i x) = x :=
  (D.parametrization i).left_inv (mem_univ x)

/-- A chart of a local piece transported to the actual glued space. -/
def gluedChart (i : D.J) (x : D.piece i) : OpenPartialHomeomorph D.Space E :=
  (D.parametrization i).symm.trans (chartAt E x)

theorem gluedChart_symm (i : D.J) (x : D.piece i) :
    ((D.gluedChart i x).symm : E → D.Space) = D.inclusion i ∘ (chartAt E x).symm := by
  funext z
  rfl

@[simp] theorem gluedChart_inclusion (i : D.J) (x y : D.piece i) :
    D.gluedChart i x (D.inclusion i y) = chartAt E x y := by
  change chartAt E x ((D.parametrization i).symm (D.inclusion i y)) = _
  rw [parametrization_symm_inclusion]

theorem gluedChart_inclusion_mem_source (i : D.J) (x : D.piece i) :
    D.inclusion i x ∈ (D.gluedChart (E := E) i x).source := by
  change D.inclusion i x ∈ (D.parametrization i).target ∧
    (D.parametrization i).symm (D.inclusion i x) ∈ (chartAt E x).source
  rw [parametrization_target, parametrization_symm_inclusion]
  exact ⟨mem_range_self x, mem_chart_source E x⟩

/-- The actual glued atlas, indexed by points in all the local pieces. -/
@[instance_reducible] def chartedSpace : ChartedSpace E D.Space where
  atlas := range (fun r : Σ i, D.piece i => D.gluedChart (E := E) r.1 r.2)
  chartAt x := D.gluedChart (D.representative x).1 (D.representative x).2
  mem_chart_source x := by
    simpa only [inclusion_representative] using
      D.gluedChart_inclusion_mem_source (E := E)
        (D.representative x).1 (D.representative x).2
  chart_mem_atlas x := mem_range_self (D.representative x)

theorem gluedChart_mem_atlas (i : D.J) (x : D.piece i) :
    letI := D.chartedSpace (E := E)
    D.gluedChart i x ∈ atlas E D.Space :=
  mem_range_self (⟨i, x⟩ : Σ i, D.piece i)

theorem gluedChart_transition_apply (i j : D.J) (x : D.piece i) (y : D.piece j)
    {z : E} (hz : z ∈ ((D.gluedChart (E := E) i x).symm.trans
      (D.gluedChart (E := E) j y)).source) :
    ((D.gluedChart (E := E) i x).symm.trans (D.gluedChart (E := E) j y)) z =
      chartAt E y (D.transition i j ((chartAt E x).symm z)) := by
  have hinc : D.inclusion i ((chartAt E x).symm z) ∈
      (D.gluedChart (E := E) j y).source := hz.2
  have hrange : D.inclusion i ((chartAt E x).symm z) ∈ range (D.inclusion j) := by
    simpa only [OpenPartialHomeomorph.symm_symm, parametrization_target] using hinc.1
  have he := (D.parametrization_transition i j hrange).2
  change chartAt E y ((D.parametrization j).symm
    (D.inclusion i ((chartAt E x).symm z))) = _
  rw [he]

variable [NormedSpace ℂ E]
    [∀ i, IsManifold (modelWithCornersSelf ℂ E) ω (D.piece i)]

/-- Holomorphicity on the glued atlas can be checked on every local piece. -/
theorem contMDiff_of_comp_inclusion {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
    (I : ModelWithCorners ℂ F H) (f : D.Space → N)
    (hf : ∀ i, ContMDiff (modelWithCornersSelf ℂ E) I ω (f ∘ D.inclusion i)) :
    letI := D.chartedSpace (E := E)
    ContMDiff (modelWithCornersSelf ℂ E) I ω f := by
  let := D.chartedSpace (E := E)
  intro x
  rw [contMDiffAt_iff_source]
  have hx : x ∈ (D.gluedChart (E := E)
      (D.representative x).1 (D.representative x).2).source := mem_chart_source E x
  have hsrc := (contMDiffAt_iff_source_of_mem_source
    (I := modelWithCornersSelf ℂ E) (I' := I) hx.2).mp
      ((hf (D.representative x).1).contMDiffAt
        (x := (D.parametrization (D.representative x).1).symm x))
  have hchart : chartAt E x =
      D.gluedChart (D.representative x).1 (D.representative x).2 := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, gluedChart, Function.comp_def] using
    hsrc

/-- The same local criterion on an open subset of the glued space. -/
theorem contMDiffOn_of_comp_inclusion {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
    (I : ModelWithCorners ℂ F H) (f : D.Space → N) {U : Set D.Space} (hU : IsOpen U)
    (hf : ∀ i, ContMDiffOn (modelWithCornersSelf ℂ E) I ω
      (f ∘ D.inclusion i) (D.inclusion i ⁻¹' U)) :
    letI := D.chartedSpace (E := E)
    ContMDiffOn (modelWithCornersSelf ℂ E) I ω f U := by
  let := D.chartedSpace (E := E)
  intro x hxU
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff_source]
  have hx : x ∈ (D.gluedChart (E := E)
      (D.representative x).1 (D.representative x).2).source := mem_chart_source E x
  have hre : D.inclusion (D.representative x).1
      ((D.parametrization (D.representative x).1).symm x) = x :=
    (D.parametrization (D.representative x).1).right_inv hx.1
  have hpre : (D.parametrization (D.representative x).1).symm x ∈
      D.inclusion (D.representative x).1 ⁻¹' U := by
    change D.inclusion _ _ ∈ U
    rwa [hre]
  have hlocal := (hf (D.representative x).1).contMDiffAt
    ((hU.preimage (D.inclusion_openEmbedding _).continuous).mem_nhds hpre)
  have hsrc := (contMDiffAt_iff_source_of_mem_source
    (I := modelWithCornersSelf ℂ E) (I' := I) hx.2).mp hlocal
  have hchart : chartAt E x =
      D.gluedChart (D.representative x).1 (D.representative x).2 := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, gluedChart, Function.comp_def] using
    hsrc

/-- The global base projection is holomorphic when each local base map is. -/
theorem projection_holomorphic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [ChartedSpace F B]
    (hbase : ∀ i, ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) ω
      (D.toBase i)) :
    letI := D.chartedSpace (E := E)
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) ω D.projection := by
  apply D.contMDiff_of_comp_inclusion (modelWithCornersSelf ℂ F) D.projection
  intro i
  simpa only [Function.comp_def, projection_inclusion] using hbase i

variable (hhol : ∀ i j, ContMDiffOn (modelWithCornersSelf ℂ E)
    (modelWithCornersSelf ℂ E) ω (D.transition i j) (D.transition i j).source)

include hhol

/-- Glued chart changes are the holomorphic local overlap maps in local charts. -/
theorem gluedChart_transition_holomorphic (i j : D.J)
    (x : D.piece i) (y : D.piece j) :
    ContDiffOn ℂ ω ((D.gluedChart (E := E) i x).symm.trans
      (D.gluedChart (E := E) j y))
      ((D.gluedChart (E := E) i x).symm.trans (D.gluedChart (E := E) j y)).source := by
  intro z hz
  have hza : z ∈ (chartAt E x).target := hz.1.1
  have hinc : D.inclusion i ((chartAt E x).symm z) ∈
      (D.gluedChart (E := E) j y).source := hz.2
  have hrange : D.inclusion i ((chartAt E x).symm z) ∈ range (D.inclusion j) := by
    simpa only [OpenPartialHomeomorph.symm_symm, parametrization_target] using hinc.1
  obtain ⟨htr, he⟩ := D.parametrization_transition i j hrange
  have ha := (chartAt E x).map_target hza
  have hb : D.transition i j ((chartAt E x).symm z) ∈ (chartAt E y).source := by
    rw [← he]
    exact hinc.2
  have hmid := (hhol i j).contMDiffAt ((D.transition i j).open_source.mem_nhds htr)
  have hc := ((contMDiffAt_iff_of_mem_source ha hb).mp hmid).2
  have hc' : ContDiffAt ℂ ω
      (chartAt E y ∘ D.transition i j ∘ (chartAt E x).symm) z := by
    simpa [extChartAt, OpenPartialHomeomorph.extend, contDiffWithinAt_univ,
      (chartAt E x).right_inv hza] using hc
  apply hc'.contDiffWithinAt.congr_of_mem ?_ hz
  intro w hw
  exact D.gluedChart_transition_apply i j x y hw

/-- The compatible local complex structures give an actual complex manifold. -/
theorem isManifold :
    letI := D.chartedSpace (E := E)
    IsManifold (modelWithCornersSelf ℂ E) ω D.Space := by
  let := D.chartedSpace (E := E)
  apply isManifold_of_contDiffOn
  rintro e e' ⟨⟨i, x⟩, rfl⟩ ⟨⟨j, y⟩, rfl⟩
  simpa using D.gluedChart_transition_holomorphic hhol i j x y

/-- Each original piece includes holomorphically into the glued complex manifold. -/
theorem inclusion_holomorphic (i : D.J) :
    letI := D.chartedSpace (E := E)
    ContMDiff (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
      (D.inclusion i) := by
  let := D.chartedSpace (E := E)
  let := D.isManifold hhol
  intro x
  have he := IsManifold.subset_maximalAtlas
    (I := modelWithCornersSelf ℂ E) (n := ω) (D.gluedChart_mem_atlas i x)
  have ht : chartAt E x x ∈ (D.gluedChart (E := E) i x).target := by
    simpa only [gluedChart_inclusion] using
      (D.gluedChart (E := E) i x).map_source (D.gluedChart_inclusion_mem_source i x)
  have hsymm := contMDiffAt_symm_of_mem_maximalAtlas he ht
  have hc : ContMDiffAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
      (chartAt E x) x :=
    contMDiffOn_chart.contMDiffAt
      ((chartAt E x).open_source.mem_nhds (mem_chart_source E x))
  apply (hsymm.comp x hc).congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_source.mem_nhds (mem_chart_source E x)] with y hy
  change D.inclusion i y = (D.gluedChart (E := E) i x).symm (chartAt E x y)
  rw [gluedChart_symm, Function.comp_apply, (chartAt E x).left_inv hy]

/-- The local inverse to any piece inclusion is holomorphic on its open range. -/
theorem parametrization_symm_holomorphic (i : D.J) :
    letI := D.chartedSpace (E := E)
    ContMDiffOn (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ω
      (D.parametrization i).symm (D.parametrization i).target := by
  let := D.chartedSpace (E := E)
  rw [parametrization_target]
  apply D.contMDiffOn_of_comp_inclusion (modelWithCornersSelf ℂ E) (D.parametrization i).symm
    (D.inclusion_openEmbedding i).isOpen_range
  intro j
  exact ((hhol j i).mono (fun x hx => (D.parametrization_transition j i hx).1)).congr
    (fun x hx => (D.parametrization_transition j i hx).2)

end Wikipedia.HopfProblem.ThreefoldGluing.Data
