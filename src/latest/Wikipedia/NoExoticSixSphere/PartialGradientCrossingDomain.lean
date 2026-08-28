import Wikipedia.NoExoticSixSphere.PartialGradientRadialGap

/-!
# Open domains for a local relative energy crossing

Both the point energy and its fiber-center energy are controlled. The lower
center bound ensures that points already in the lower sublevel avoid the
partial-critical slice; the upper bound makes the full radial endpoint lie
below the desired crossing level.
-/

open Set Filter
open scoped Topology ContDiff

namespace NoExoticSixSphere.PartialGradientCoordinates.LocalData

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {L : D →L[ℝ] E} {U : Set E} (C : LocalData f L U)

def crossingDomain (r l b e : ℝ) : Set E :=
  {z | z ∈ C.centerDomain ∧ ‖C.center z‖ < r ∧ ‖z - C.center z‖ < r ∧
    l < f (C.center z) ∧ f (C.center z) < b ∧ f z < e}

theorem crossingDomain_subset_source (r l b e : ℝ) :
    C.crossingDomain r l b e ⊆ C.chart.source := fun _ hz ↦ hz.1.1

theorem norm_lt_of_mem_crossingDomain (r l b e : ℝ) {z : E}
    (hz : z ∈ C.crossingDomain r l b e) : ‖z‖ < 2 * r := by
  have hh := norm_add_le (C.center z) (z - C.center z)
  rw [add_sub_cancel] at hh
  linarith [hz.2.1, hz.2.2.1]

theorem isOpen_crossingDomain (hU : IsOpen U) (hf : ContinuousOn f U) (r l b e : ℝ) :
    IsOpen (C.crossingDomain r l b e) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hc := C.continuousAt_center hz.1
  have hfz : ContinuousAt f z :=
    (hf z (C.source_subset hz.1.1)).continuousAt (hU.mem_nhds (C.source_subset hz.1.1))
  have hfcenter : ContinuousAt f (C.center z) :=
    (hf _ (C.source_subset (C.center_mem_source hz.1))).continuousAt
      (hU.mem_nhds (C.source_subset (C.center_mem_source hz.1)))
  have hfc : ContinuousAt (fun x ↦ f (C.center x)) z := hfcenter.comp hc
  filter_upwards [C.isOpen_centerDomain.mem_nhds hz.1,
    hc.norm.eventually (isOpen_Iio.mem_nhds hz.2.1),
    (continuousAt_id.sub hc).norm.eventually (isOpen_Iio.mem_nhds hz.2.2.1),
    hfc.eventually (isOpen_Ioi.mem_nhds hz.2.2.2.1),
    hfc.eventually (isOpen_Iio.mem_nhds hz.2.2.2.2.1),
    hfz.eventually (isOpen_Iio.mem_nhds hz.2.2.2.2.2)] with x hx hc hd hl hb he
  exact ⟨hx, hc, hd, hl, hb, he⟩

theorem zero_mem_crossingDomain (r l b e : ℝ) (hr : 0 < r)
    (hl : l < f 0) (hb : f 0 < b) (he : f 0 < e) :
    (0 : E) ∈ C.crossingDomain r l b e := by
  simp [crossingDomain, C.zero_mem_centerDomain, C.center_zero, hr, hl, hb, he]

theorem crossingDomain_gradient_ne_zero (r l b e : ℝ) {z : E}
    (hz : z ∈ C.crossingDomain r l b e) (hlow : f z ≤ l) : gradient f L z ≠ 0 := by
  intro hg
  have he := (C.center_eq_self_iff hz.1).mpr hg
  have hh := hz.2.2.2.1
  rw [he] at hh
  exact (not_lt_of_ge hlow) hh

theorem crossingDomain_mem_radialDomain (r l b e : ℝ) {z : E}
    (hz : z ∈ C.crossingDomain r l b e) (hgrad : gradient f L z ≠ 0) :
    z ∈ C.radialDomain r := by
  refine ⟨hz.1, hz.2.1, ?_, hz.2.2.1.le⟩
  intro hzero
  exact hgrad ((C.center_eq_self_iff hz.1).mp (sub_eq_zero.mp hzero).symm)

end NoExoticSixSphere.PartialGradientCoordinates.LocalData
