import Wikipedia.SmoothSixDPoincare.EnlargedBigon

/-!
# A compact graph motion inside the actual Whitney chart neighborhood

A smooth cutoff supported in the enlarged horizontal interval multiplies
the enlarged parabolic height. The graph lies strictly above the upper
sheet on the original interval, is nonnegative everywhere, and its entire
vertical motion trace stays in the prescribed open neighborhood of the bigon.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

def verticalGraph (B : ℝ → ℝ) (t s : ℝ) : Space := ((s, t * B s), 0)

/-- Construct a compact height and its whole supported motion trace
inside the actual open source. -/
theorem exists_supported_graph_height {h : ℝ} (hh : 0 < h) {U : Set Space} (hU : IsOpen U)
    (hKU : MapsTo bigonEmbedding (bigon h) U) :
    ∃ B : ℝ → ℝ, ContDiff ℝ ∞ B ∧ HasCompactSupport B ∧
      (∀ s, 0 ≤ B s) ∧ (∀ s, |s| ≤ 1 → h * (1 - s ^ 2) < B s) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ tsupport B, verticalGraph B t s ∈ U := by
  obtain ⟨r, hr, hscaled⟩ := exists_scaled_bigon_in_open hh hU hKU
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  let α : ContDiffBump (0 : ℝ) := {
    rIn := 1
    rOut := r
    rIn_pos := zero_lt_one
    rIn_lt_rOut := hr }
  let B : ℝ → ℝ := fun s => α s * (h * (r ^ 2 - s ^ 2))
  have hB : ContDiff ℝ ∞ B := α.contDiff.mul (by fun_prop)
  have hcompact : HasCompactSupport B := α.hasCompactSupport.mul_right
  have hsupp : tsupport B ⊆ tsupport (α : ℝ → ℝ) := by
    apply closure_mono
    intro s hs hα
    apply hs
    change α s * (h * (r ^ 2 - s ^ 2)) = 0
    rw [hα, zero_mul]
  have hbound : ∀ s ∈ tsupport B, |s| ≤ r := by
    intro s hs
    have hx := hsupp hs
    rw [α.tsupport_eq] at hx
    change dist s 0 ≤ r at hx
    simpa only [Real.dist_eq, sub_zero] using hx
  have hheight {s : ℝ} (hs : |s| ≤ r) : 0 ≤ h * (r ^ 2 - s ^ 2) := by
    have hsq : s ^ 2 ≤ r ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg s) hrpos.le).mpr hs
    exact mul_nonneg hh.le (sub_nonneg.mpr hsq)
  have hnonneg : ∀ s, 0 ≤ B s := by
    intro s
    by_cases hs : α s = 0
    · simp only [B, hs, zero_mul, le_refl]
    have hmem : s ∈ Function.support α := hs
    rw [α.support_eq] at hmem
    have hsr : |s| ≤ r := by
      have hl : |s| < r := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hmem
      exact hl.le
    exact mul_nonneg α.nonneg (hheight hsr)
  refine ⟨B, hB, hcompact, hnonneg, ?_, ?_⟩
  · intro s hs
    have hα : α s = 1 := α.one_of_mem_closedBall (by
      change dist s 0 ≤ 1
      simpa only [Real.dist_eq, sub_zero] using hs)
    change h * (1 - s ^ 2) < α s * (h * (r ^ 2 - s ^ 2))
    rw [hα, one_mul]
    have hgap : 0 < h * (r ^ 2 - 1) := mul_pos hh (by nlinarith [sq_nonneg (r - 1)])
    nlinarith
  · intro t ht s hs
    have hts : t * α s ≤ 1 := by
      calc
        t * α s ≤ 1 * α s := mul_le_mul_of_nonneg_right ht.2 α.nonneg
        _ ≤ 1 := by simpa only [one_mul] using (α.le_one (x := s))
    have hy : t * B s ≤ h * (r ^ 2 - s ^ 2) := by
      calc
        t * B s = (t * α s) * (h * (r ^ 2 - s ^ 2)) := by dsimp [B]; ring
        _ ≤ h * (r ^ 2 - s ^ 2) := mul_le_of_le_one_left (hheight (hbound s hs)) hts
    have hcap : 0 ≤ t * B s ∧ h * s ^ 2 + t * B s ≤ h * r ^ 2 :=
      ⟨mul_nonneg ht.1 (hnonneg s), by nlinarith⟩
    obtain ⟨q, hq, heq⟩ := enlarged_cap_parametrization (h := h) (p := (s, t * B s)) hrpos hcap
    have hmem := hscaled hq
    rw [heq] at hmem
    exact hmem

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel
