import Wikipedia.NoExoticSixSphere.PartialGradientCenter
import Wikipedia.NoExoticSixSphere.RadialExpansion
import Mathlib.Topology.Homotopy.Basic

/-!
# A continuous local radial homotopy along negative fibers

In a small punctured fiber disk, expand the displacement from the center to
the outer radius. The center is preserved, every intermediate point stays
inside the verified chart, and the outer boundary is fixed. This is a native
relative homotopy on the actual coordinate domain, not a choice of directions.
-/

open Set unitInterval
open scoped Topology

namespace NoExoticSixSphere.PartialGradientCoordinates.LocalData

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {L : D →L[ℝ] E} {U : Set E} (C : LocalData f L U)

def radialDomain (r : ℝ) : Set E :=
  {z | z ∈ C.centerDomain ∧ ‖C.center z‖ < r ∧ z - C.center z ≠ 0 ∧ ‖z - C.center z‖ ≤ r}

theorem norm_lt_of_mem_radialDomain (r : ℝ) {z : E} (hz : z ∈ C.radialDomain r) :
    ‖z‖ < 2 * r := by
  have hh := norm_add_le (C.center z) (z - C.center z)
  rw [add_sub_cancel] at hh
  linarith [hz.2.1, hz.2.2.2]

noncomputable def radial (r : ℝ) (p : I × E) : E :=
  C.center p.2 + RadialExpansion.expand r (p.1, p.2 - C.center p.2)

theorem radial_mem_source (r : ℝ) (hr : 0 < r)
    (hball : Metric.ball (0 : E) (3 * r) ⊆ C.chart.source)
    {z : E} (hz : z ∈ C.radialDomain r) (s : I) : C.radial r (s, z) ∈ C.chart.source := by
  have hb := (RadialExpansion.norm_expand_bounds r hz.2.2.1 hz.2.2.2 s).2
  have hn := norm_add_le (C.center z) (RadialExpansion.expand r (s, z - C.center z))
  apply hball
  rw [Metric.mem_ball, dist_zero_right]
  change ‖C.center z + RadialExpansion.expand r (s, z - C.center z)‖ < 3 * r
  linarith [hz.2.1]

theorem radial_same_snd (r : ℝ) {z : E} (hz : z ∈ C.radialDomain r) (s : I) :
    (C.chart (C.radial r (s, z))).2 = (C.chart z).2 := by
  obtain ⟨w, hw⟩ := C.center_same_fiber hz.1
  have hd : z - C.center z = L w := by
    simpa only [add_sub_cancel_left] using congrArg (fun x : E ↦ x - C.center z) hw
  have he : C.radial r (s, z) = C.center z +
      L (RadialExpansion.scale r (s, z - C.center z) • w) := by
    change C.center z + RadialExpansion.scale r (s, z - C.center z) •
      (z - C.center z) = _
    rw [map_smul, hd]
  rw [he, C.map_snd_add, C.chart_center hz.1]

theorem center_radial (r : ℝ) {z : E} (hz : z ∈ C.radialDomain r) (s : I) :
    C.center (C.radial r (s, z)) = C.center z := by
  unfold center
  rw [C.radial_same_snd r hz s]

theorem radial_mem_domain (r : ℝ) (hr : 0 < r)
    (hball : Metric.ball (0 : E) (3 * r) ⊆ C.chart.source)
    {z : E} (hz : z ∈ C.radialDomain r) (s : I) : C.radial r (s, z) ∈ C.radialDomain r := by
  have hs : C.radial r (s, z) ∈ C.chart.source := C.radial_mem_source r hr hball hz s
  have hc : C.radial r (s, z) ∈ C.centerDomain := by
    refine ⟨hs, ?_⟩
    rw [C.radial_same_snd r hz s]
    exact hz.1.2
  have hd : C.radial r (s, z) - C.center (C.radial r (s, z)) =
      RadialExpansion.expand r (s, z - C.center z) := by
    rw [C.center_radial r hz s]
    simp only [radial, add_sub_cancel_left]
  have hn := RadialExpansion.norm_expand_bounds r hz.2.2.1 hz.2.2.2 s
  refine ⟨hc, ?_, ?_, ?_⟩
  · rw [C.center_radial r hz s]
    exact hz.2.1
  · rw [hd]
    exact norm_pos_iff.mp ((norm_pos_iff.mpr hz.2.2.1).trans_le hn.1)
  · rw [hd]
    exact hn.2

theorem radial_zero (r : ℝ) (z : E) : C.radial r (0, z) = z := by
  simp only [radial, RadialExpansion.expand_zero, add_sub_cancel]

theorem radial_fixed (r : ℝ) (hr : 0 < r) {z : E} (hz : ‖z - C.center z‖ = r) (s : I) :
    C.radial r (s, z) = z := by
  rw [radial, RadialExpansion.expand_fixed r hr hz]
  abel

theorem radial_one_norm (r : ℝ) {z : E} (hz : z ∈ C.radialDomain r) :
    ‖C.radial r (1, z) - C.center (C.radial r (1, z))‖ = r := by
  rw [C.center_radial r hz 1]
  simpa only [radial, add_sub_cancel_left] using
    RadialExpansion.norm_expand_one r hz.2.2.1 hz.2.2.2

theorem continuousAt_radial (r : ℝ) {p : I × E} (hp : p.2 ∈ C.radialDomain r) :
    ContinuousAt (C.radial r) p := by
  have hc : ContinuousAt (fun q : I × E ↦ C.center q.2) p :=
    (C.continuousAt_center hp.1).comp continuousAt_snd
  have hd : ContinuousAt (fun q : I × E ↦ q.2 - C.center q.2) p := continuousAt_snd.sub hc
  have he : ContinuousAt (fun q : I × E ↦
      RadialExpansion.expand r (q.1, q.2 - C.center q.2)) p :=
    ContinuousAt.comp (f := fun q : I × E ↦ (q.1, q.2 - C.center q.2))
      (g := RadialExpansion.expand r) (RadialExpansion.continuousAt_expand r hp.2.2.1)
      (continuousAt_fst.prodMk hd)
  exact hc.add he

noncomputable def radialMap (r : ℝ) (hr : 0 < r)
    (hball : Metric.ball (0 : E) (3 * r) ⊆ C.chart.source) :
    C(I × C.radialDomain r, C.radialDomain r) where
  toFun p := ⟨C.radial r (p.1, p.2.1), C.radial_mem_domain r hr hball p.2.2 p.1⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro p
    exact ContinuousAt.comp (f := fun q : I × C.radialDomain r ↦ (q.1, q.2.1))
      (g := C.radial r) (C.continuousAt_radial r p.2.2)
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousAt

noncomputable def radialEndpoint (r : ℝ) (hr : 0 < r)
    (hball : Metric.ball (0 : E) (3 * r) ⊆ C.chart.source) :
    C(C.radialDomain r, C.radialDomain r) :=
  (C.radialMap r hr hball).comp ⟨fun z ↦ (1, z), continuous_const.prodMk continuous_id⟩

noncomputable def radialHomotopy (r : ℝ) (hr : 0 < r)
    (hball : Metric.ball (0 : E) (3 * r) ⊆ C.chart.source) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (C.radialDomain r))
      (C.radialEndpoint r hr hball) {z | ‖z.1 - C.center z.1‖ = r} where
  toContinuousMap := C.radialMap r hr hball
  map_zero_left z := Subtype.ext (C.radial_zero r z.1)
  map_one_left _ := rfl
  prop' s _z hz := Subtype.ext (C.radial_fixed r hr hz s)

end NoExoticSixSphere.PartialGradientCoordinates.LocalData
