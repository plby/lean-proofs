import ErdosProblems.Erdos421.SmoothedVonMangoldtMajorant
import ErdosProblems.Erdos421.StretchedLogDecay

/-! # Arbitrary logarithmic savings for the actual smoothed von Mangoldt sum -/

namespace Erdos421

open Filter Topology

theorem smoothedVonMangoldt_log_saving (K : ℕ) {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ X₀ > 1, ∀ x t : ℝ, X₀ ≤ x → (Real.log x) ^ (A + 4) ≤ |t| → |t| ≤ x ^ K →
      ‖smoothedVonMangoldtSum x t‖ ≤ ε * x / (Real.log x) ^ A := by
  obtain ⟨C, hC, T₁, hT₁, hmajor⟩ := exists_smoothedVonMangoldt_power_majorant K
  have hsmall := (smoothed_log_majorant_tendsto_zero K A C).eventually (gt_mem_nhds hε)
  have hfrequency : ∀ᶠ x : ℝ in atTop, T₁ ≤ (Real.log x) ^ (A + 4) :=
    ((tendsto_rpow_atTop (by linarith : 0 < A + 4)).comp Real.tendsto_log_atTop).eventually
      (eventually_ge_atTop T₁)
  have hlarge : ∀ᶠ x : ℝ in atTop, ∀ t : ℝ,
      (Real.log x) ^ (A + 4) ≤ |t| → |t| ≤ x ^ K →
        ‖smoothedVonMangoldtSum x t‖ ≤ ε * x / (Real.log x) ^ A := by
    filter_upwards [hmajor, hsmall, hfrequency, eventually_ge_atTop (2 : ℝ)]
      with x hmajor hsmall hfrequency hx
    intro t hlow hupper
    have hxp : 0 < x := by linarith
    have hlog : 0 < Real.log x := Real.log_pos (by linarith)
    have hpower : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hlog _
    have hb := hmajor t (hfrequency.trans hlow) hupper
    have hscaled := mul_le_mul_of_nonneg_right hb hpower.le
    have hfreq := logarithmic_frequency_term_bound hlog hlow
    have he : (Real.exp (-perronWidthCoefficient K * (Real.log x) ^ (1 / 16 : ℝ)) *
        (Real.log x) ^ 2 + (Real.log x) ^ 2 / |t|) * (Real.log x) ^ A =
        Real.exp (-perronWidthCoefficient K * (Real.log x) ^ (1 / 16 : ℝ)) *
          (Real.log x) ^ (A + 2) + ((Real.log x) ^ 2 / |t|) * (Real.log x) ^ A := by
      rw [Real.rpow_add hlog A 2, Real.rpow_two]
      ring
    rw [mul_assoc C, he] at hscaled
    have hscaled' : (‖smoothedVonMangoldtSum x t‖ / x) * (Real.log x) ^ A ≤ ε := by
      apply hscaled.trans
      apply le_trans _ hsmall.le
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hfreq) hC.le
    have hratio := (le_div_iff₀ hpower).mpr hscaled'
    have hnorm := (div_le_iff₀ hxp).mp hratio
    exact hnorm.trans_eq (by ring)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hlarge
  refine ⟨max X₀ 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro x t hx hlow hupper
  exact hX₀ x ((le_max_left X₀ 2).trans hx) t hlow hupper

end Erdos421
