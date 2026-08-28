import Wikipedia.NoExoticSixSphere.PartialGradientFiberDistance

/-!
# Fiber cores and a no-entry estimate

A fiber core bounds both its center and its displacement from that center.
Center preservation and the fiber-radius estimate prevent entry into a
slightly smaller core, even after radial expansion.
-/

open Set Filter unitInterval
open scoped Topology

namespace NoExoticSixSphere.PartialGradientCoordinates.LocalData

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {L : D →L[ℝ] E} {U : Set E} (C : LocalData f L U)

def fiberCore (a b : ℝ) : Set E :=
  {z | z ∈ C.centerDomain ∧ ‖C.center z‖ < a ∧ ‖z - C.center z‖ < b}

theorem fiberCore_mono {a b a' b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') :
    C.fiberCore a b ⊆ C.fiberCore a' b' :=
  fun _ hz ↦ ⟨hz.1, hz.2.1.trans_le ha, hz.2.2.trans_le hb⟩

theorem fiberCore_subset_ball (a b : ℝ) :
    C.fiberCore a b ⊆ Metric.ball 0 (a + b) := by
  intro z hz
  have hh := norm_add_le (C.center z) (z - C.center z)
  rw [add_sub_cancel] at hh
  have hn : ‖z‖ < a + b := by linarith [hz.2.1, hz.2.2]
  simpa only [Metric.mem_ball, dist_zero_right] using hn

theorem isOpen_fiberCore (a b : ℝ) : IsOpen (C.fiberCore a b) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hc := C.continuousAt_center hz.1
  filter_upwards [C.isOpen_centerDomain.mem_nhds hz.1,
    hc.norm.eventually (isOpen_Iio.mem_nhds hz.2.1),
    (continuousAt_id.sub hc).norm.eventually (isOpen_Iio.mem_nhds hz.2.2)] with x hx hc hd
  exact ⟨hx, hc, hd⟩

theorem zero_mem_fiberCore {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (0 : E) ∈ C.fiberCore a b := by
  simp [fiberCore, C.zero_mem_centerDomain, C.center_zero, ha, hb]

theorem notMem_fiberCore_of_control {a b η : ℝ} {z z' : E}
    (hz : z ∈ C.centerDomain) (hnot : z ∉ C.fiberCore a b)
    (hc : C.center z' = C.center z)
    (hdisp : ‖z - C.center z‖ - η < ‖z' - C.center z'‖) :
    z' ∉ C.fiberCore a (b - η) := by
  intro hnew
  apply hnot
  refine ⟨hz, ?_, ?_⟩
  · rw [← hc]
    exact hnew.2.1
  · have hh := hnew.2.2
    linarith

theorem notMem_fiberCore_of_close {a b η : ℝ} {z z' : E}
    (hz : z ∈ C.centerDomain) (hnot : z ∉ C.fiberCore a b)
    (hc : C.center z' = C.center z) (hclose : dist z' z < η) :
    z' ∉ C.fiberCore a (b - η) :=
  C.notMem_fiberCore_of_control hz hnot hc (C.fiber_norm_gt_of_dist_lt hc hclose)

theorem notMem_fiberCore_after_radial (r : ℝ) {a b η : ℝ} {z z' : E}
    (hz : z ∈ C.centerDomain) (hnot : z ∉ C.fiberCore a b)
    (hz' : z' ∈ C.radialDomain r) (hc : C.center z' = C.center z)
    (hclose : dist z' z < η) (s : I) : C.radial r (s, z') ∉ C.fiberCore a (b - η) :=
  C.notMem_fiberCore_of_control hz hnot ((C.center_radial r hz' s).trans hc)
    (C.radial_fiber_norm_gt_of_close r hz' hc hclose s)

end NoExoticSixSphere.PartialGradientCoordinates.LocalData
