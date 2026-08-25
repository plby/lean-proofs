import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Turning uniform arbitrarily small error envelopes into limits
-/

namespace Erdos964

open Filter
open scoped Topology

theorem tendsto_zero_of_uniform_small_error {ι : Type*} {l : Filter ι}
    (f : ι → ℝ) (G : ℝ) (hG : 0 ≤ G)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, |f i| ≤ ε * G) :
    Tendsto f l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  let ε := δ / (G + 1)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hεG : ε * G < δ := by
    dsimp only [ε]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < G + 1)).mpr
    nlinarith
  filter_upwards [h ε hε] with i hi
  simpa only [Real.dist_eq, sub_zero] using hi.trans_lt hεG

theorem tendsto_normalized_uniform_small_error {ι : Type*} {l : Filter ι}
    (f s : ι → ℝ) (G : ℝ) (hG : 0 ≤ G) (hs : ∀ᶠ i in l, 0 < s i)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, |f i| ≤ (ε * G) * s i) :
    Tendsto (fun i => f i / s i) l (𝓝 0) := by
  apply tendsto_zero_of_uniform_small_error _ G hG
  intro ε hε
  filter_upwards [h ε hε, hs] with i hi hsi
  rw [abs_div, abs_of_pos hsi]
  calc
    _ ≤ ((ε * G) * s i) / s i := div_le_div_of_nonneg_right hi hsi.le
    _ = ε * G := mul_div_cancel_right₀ _ hsi.ne'

end Erdos964
