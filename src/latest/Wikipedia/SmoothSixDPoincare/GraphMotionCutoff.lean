import Wikipedia.SmoothSixDPoincare.SupportedGraphHeight
import Wikipedia.SmoothSixDPoincare.CompactSmoothCutoff

/-!
# A jointly smooth compact cutoff for the entire graph motion trace

The cutoff is one near the compact time-space trace. Multiply it by the
actual graph height to obtain the displacement field. Its whole support
lies over the chart source, and its value on every tracked point is exactly
the required height, including where that height vanishes.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

def graphTrace (B : ℝ → ℝ) : Set (ℝ × Space) :=
  (fun p : ℝ × ℝ => (p.1, verticalGraph B p.1 p.2)) '' (Icc (0 : ℝ) 1 ×ˢ tsupport B)

theorem isCompact_graphTrace {B : ℝ → ℝ} (hB : Continuous B) (hcompact : HasCompactSupport B) :
    IsCompact (graphTrace B) := by
  apply (isCompact_Icc.prod hcompact.isCompact).image
  unfold verticalGraph
  fun_prop

/-- Construct the actual supported scalar displacement family on time times model space. -/
theorem exists_graph_motion_cutoff {B : ℝ → ℝ} (hB : ContDiff ℝ ∞ B)
    (hcompact : HasCompactSupport B) (hnonneg : ∀ s, 0 ≤ B s)
    {U : Set Space} (hU : IsOpen U)
    (htrace : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ tsupport B, verticalGraph B t s ∈ U) :
    ∃ β : ℝ × Space → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
      tsupport β ⊆ Prod.snd ⁻¹' U ∧ (∀ p, 0 ≤ β p) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ s : ℝ, β (t, verticalGraph B t s) = B s := by
  have hCU : graphTrace B ⊆ Prod.snd ⁻¹' U := by
    rintro _ ⟨p, hp, rfl⟩
    exact htrace p.1 hp.1 p.2 hp.2
  obtain ⟨η, hη, hηcompact, hηsupport, hηone, hηrange⟩ :=
    exists_compact_smooth_cutoff (isCompact_graphTrace hB.continuous hcompact)
      (hU.preimage continuous_snd) hCU
  let β : ℝ × Space → ℝ := fun p => η p * B p.2.1.1
  have hβ : ContDiff ℝ ∞ β := hη.mul (hB.comp (by fun_prop))
  have hβcompact : HasCompactSupport β := hηcompact.mul_right
  have hsupp : tsupport β ⊆ tsupport η := by
    apply closure_mono
    intro p hp hηp
    apply hp
    change η p * B p.2.1.1 = 0
    rw [hηp, zero_mul]
  refine ⟨β, hβ, hβcompact, hsupp.trans hηsupport,
    fun p => mul_nonneg (hηrange p).1 (hnonneg _), ?_⟩
  intro t ht s
  by_cases hs : B s = 0
  · change η (t, verticalGraph B t s) * B s = B s
    rw [hs, mul_zero]
  have hpoint : (t, verticalGraph B t s) ∈ graphTrace B :=
    ⟨(t, s), ⟨ht, subset_tsupport B hs⟩, rfl⟩
  have hηpoint : η (t, verticalGraph B t s) = 1 := hηone.self_of_nhdsSet _ hpoint
  change η (t, verticalGraph B t s) * B s = B s
  rw [hηpoint, one_mul]

/-- All actual height, support, and exact-tracking data needed for finite small motions. -/
structure GraphMotionData (h : ℝ) (U : Set Space) where
  height : ℝ → ℝ
  smooth_height : ContDiff ℝ ∞ height
  compact_height : HasCompactSupport height
  nonneg_height : ∀ s, 0 ≤ height s
  above : ∀ s, |s| ≤ 1 → h * (1 - s ^ 2) < height s
  trace_source : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ tsupport height, verticalGraph height t s ∈ U
  cutoff : ℝ × Space → ℝ
  smooth_cutoff : ContDiff ℝ ∞ cutoff
  compact_cutoff : HasCompactSupport cutoff
  support_cutoff : tsupport cutoff ⊆ Prod.snd ⁻¹' U
  nonneg_cutoff : ∀ p, 0 ≤ cutoff p
  tracking : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s, cutoff (t, verticalGraph height t s) = height s

/-- Every actual open neighborhood of the bigon admits the required supported motion data. -/
theorem nonempty_graphMotionData {h : ℝ} (hh : 0 < h) {U : Set Space} (hU : IsOpen U)
    (hKU : MapsTo bigonEmbedding (bigon h) U) : Nonempty (GraphMotionData h U) := by
  obtain ⟨B, hB, hcompact, hnonneg, habove, htrace⟩ := exists_supported_graph_height hh hU hKU
  obtain ⟨β, hβ, hβcompact, hβsupport, hβnonneg, hβtrack⟩ :=
    exists_graph_motion_cutoff hB hcompact hnonneg hU htrace
  exact ⟨{
    height := B
    smooth_height := hB
    compact_height := hcompact
    nonneg_height := hnonneg
    above := habove
    trace_source := htrace
    cutoff := β
    smooth_cutoff := hβ
    compact_cutoff := hβcompact
    support_cutoff := hβsupport
    nonneg_cutoff := hβnonneg
    tracking := hβtrack }⟩

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel
