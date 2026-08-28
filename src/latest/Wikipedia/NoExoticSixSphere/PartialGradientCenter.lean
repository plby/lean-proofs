import Wikipedia.NoExoticSixSphere.PartialGradientLocalData

/-!
# The local center of a negative affine fiber

The inverse zero slice defines a continuous center map on an open neighborhood
of the origin. Its restricted differential vanishes, and each point differs
from its center by a vector in the actual negative linear family.
-/

open Set Filter
open scoped Topology

namespace NoExoticSixSphere.PartialGradientCoordinates.LocalData

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {L : D →L[ℝ] E} {U : Set E} (C : LocalData f L U)

def centerDomain : Set E :=
  {z | z ∈ C.chart.source ∧ (0, (C.chart z).2) ∈ C.chart.target}

noncomputable def center (z : E) : E := C.chart.symm (0, (C.chart z).2)

theorem continuousAt_chart {z : E} (hz : z ∈ C.chart.source) : ContinuousAt C.chart z :=
  C.chart.contMDiffOn_toFun.continuousOn.continuousAt (C.chart.open_source.mem_nhds hz)

theorem isOpen_centerDomain : IsOpen C.centerDomain := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hp : ContinuousAt (fun x : E ↦ ((0 : D →L[ℝ] ℝ), (C.chart x).2)) z :=
    continuousAt_const.prodMk (C.continuousAt_chart hz.1).snd
  filter_upwards [C.chart.open_source.mem_nhds hz.1,
    hp.eventually (C.chart.open_target.mem_nhds hz.2)] with x hx hy
  exact ⟨hx, hy⟩

theorem zero_mem_centerDomain : (0 : E) ∈ C.centerDomain := by
  refine ⟨C.zero_mem_source, ?_⟩
  have ht := C.chart.map_source' C.zero_mem_source
  simpa only [C.map_zero, Prod.snd_zero] using! ht

theorem center_zero : C.center 0 = 0 := by
  have hh := C.chart.left_inv' C.zero_mem_source
  change C.chart.symm (C.chart 0) = 0 at hh
  simpa only [center, C.map_zero, Prod.snd_zero] using! hh

theorem continuousAt_center {z : E} (hz : z ∈ C.centerDomain) : ContinuousAt C.center z := by
  have hp : ContinuousAt (fun x : E ↦ ((0 : D →L[ℝ] ℝ), (C.chart x).2)) z :=
    continuousAt_const.prodMk (C.continuousAt_chart hz.1).snd
  have hi : ContinuousAt C.chart.symm (0, (C.chart z).2) :=
    C.chart.contMDiffOn_invFun.continuousOn.continuousAt (C.chart.open_target.mem_nhds hz.2)
  exact ContinuousAt.comp (f := fun x : E ↦ (0, (C.chart x).2))
    (g := C.chart.symm) hi hp

theorem continuousOn_center : ContinuousOn C.center C.centerDomain :=
  fun _ hz ↦ (C.continuousAt_center hz).continuousWithinAt

theorem center_mem_source {z : E} (hz : z ∈ C.centerDomain) : C.center z ∈ C.chart.source :=
  C.chart.map_target' hz.2

theorem chart_center {z : E} (hz : z ∈ C.centerDomain) :
    C.chart (C.center z) = (0, (C.chart z).2) := C.chart.right_inv' hz.2

theorem gradient_center {z : E} (hz : z ∈ C.centerDomain) : gradient f L (C.center z) = 0 := by
  rw [← C.map_fst, C.chart_center hz]

theorem center_same_fiber {z : E} (hz : z ∈ C.centerDomain) :
    ∃ w : D, z = C.center z + L w := by
  apply (C.same_snd_iff (C.center z) z).mp
  rw [C.chart_center hz]

theorem center_eq_self_iff {z : E} (hz : z ∈ C.centerDomain) :
    C.center z = z ↔ gradient f L z = 0 := by
  constructor
  · intro he
    simpa only [he] using C.gradient_center hz
  · intro hg
    have he : C.chart z = (0, (C.chart z).2) := Prod.ext ((C.map_fst z).trans hg) rfl
    change C.chart.symm (0, (C.chart z).2) = z
    rw [← he]
    exact C.chart.left_inv' hz.1

end NoExoticSixSphere.PartialGradientCoordinates.LocalData
