import ErdosProblems.Erdos421.SmoothedVonMangoldtSaving
import ErdosProblems.Erdos421.VonMangoldtUnsmoothing
import ErdosProblems.Erdos421.UnsmoothingParameters

/-! # Arbitrary logarithmic cancellation for the unsmoothed von Mangoldt sum -/

namespace Erdos421

open Filter Topology

theorem vonMangoldtTwistSum_log_saving (K : ℕ) {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ X₀ > 1, ∀ x t : ℝ, X₀ ≤ x → (Real.log x) ^ (2 * A + 8) ≤ |t| → |t| ≤ x ^ K →
      ‖vonMangoldtTwistSum x t‖ ≤ ε * x / (Real.log x) ^ A := by
  let S : ℝ := 2 * A + 3
  let η : ℝ := ε / 10
  have hS : 0 ≤ S := by dsimp only [S]; linarith
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨X₁, hX₁, hsmooth⟩ := smoothedVonMangoldt_log_saving K hS hη
  have hloglarge : ∀ᶠ x : ℝ in atTop, max 1 ((2 : ℝ) ^ (2 * A + 7)) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  have htail := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp
    Real.tendsto_log_atTop).const_div_atTop (4 : ℝ)
  simp only [Real.rpow_two, Function.comp_apply] at htail
  have hlarge : ∀ᶠ x : ℝ in atTop, ∀ t : ℝ,
      (Real.log x) ^ (2 * A + 8) ≤ |t| → |t| ≤ x ^ K →
        ‖vonMangoldtTwistSum x t‖ ≤ ε * x / (Real.log x) ^ A := by
    filter_upwards [eventually_ge_atTop (max X₁ 2), hloglarge,
      log_power_le_self_eventually (A + 3),
      htail.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))]
      with x hx hloglarge hsize htail
    intro t hlow hupper
    have hx2 : 2 ≤ x := (le_max_right _ _).trans hx
    have hxX : X₁ ≤ x := (le_max_left _ _).trans hx
    have hxp : 0 < x := by linarith
    have hlog : 1 ≤ Real.log x := (le_max_left _ _).trans hloglarge
    have hlogp : 0 < Real.log x := by linarith
    have hlogtwo : (2 : ℝ) ^ (2 * A + 7) ≤ Real.log x :=
      (le_max_right _ _).trans hloglarge
    let h : ℝ := x / (Real.log x) ^ (A + 3)
    obtain ⟨hh1, hhx⟩ := unsmoothing_step_bounds hA hlog hsize
    change 1 ≤ h at hh1
    change h ≤ x at hhx
    have hh : 0 < h := by linarith
    have hxh : x + h ≤ 2 * x := by linarith
    have hlogh := unsmoothing_log_bounds hx2 hh.le hhx
    have hloghp : 0 < Real.log (x + h) := hlogp.trans_le hlogh.1
    have hfreqx : (Real.log x) ^ (S + 4) ≤ |t| :=
      (Real.rpow_le_rpow_of_exponent_le hlog (by dsimp only [S]; linarith)).trans hlow
    have hfreqh : (Real.log (x + h)) ^ (S + 4) ≤ |t| :=
      (unsmoothing_frequency_bound hA hx2 hh.le hhx hlogtwo).trans hlow
    have hupperh : |t| ≤ (x + h) ^ K :=
      hupper.trans (pow_le_pow_left₀ hxp.le (by linarith) K)
    have hFx := hsmooth x t hxX hfreqx hupper
    have hFh := hsmooth (x + h) t (by linarith) hfreqh hupperh
    have hpow : 0 < (Real.log x) ^ S := Real.rpow_pos_of_pos hlogp _
    have hFh' : ‖smoothedVonMangoldtSum (x + h) t‖ ≤ 2 * η * x / (Real.log x) ^ S := by
      calc
        _ ≤ η * (x + h) / (Real.log (x + h)) ^ S := hFh
        _ ≤ η * (x + h) / (Real.log x) ^ S :=
          div_le_div_of_nonneg_left (by positivity) hpow
            (Real.rpow_le_rpow hlogp.le hlogh.1 hS)
        _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith only [hxh, hη]) hpow.le
    have hnum : (x + h) * ‖smoothedVonMangoldtSum (x + h) t‖ +
        x * ‖smoothedVonMangoldtSum x t‖ ≤ 5 * η * x ^ 2 / (Real.log x) ^ S := by
      have h₁ := mul_le_mul hxh hFh' (norm_nonneg _) (by positivity : 0 ≤ 2 * x)
      have h₂ := mul_le_mul_of_nonneg_left hFx hxp.le
      exact (add_le_add h₁ h₂).trans_eq (by ring)
    have hboundary : (h + 1) * Real.log (x + h) ≤ 4 * h * Real.log x := by
      have hb := mul_le_mul (by linarith : h + 1 ≤ 2 * h) hlogh.2
        hloghp.le (by positivity : 0 ≤ 2 * h)
      exact hb.trans_eq (by ring)
    have hraw := vonMangoldtTwistSum_unsmoothing_bound (by linarith : 1 ≤ x) hh t
    have hnorm : ‖vonMangoldtTwistSum x t‖ ≤
        (5 * η * x ^ 2 / (Real.log x) ^ S) / h + 4 * h * Real.log x :=
      hraw.trans (add_le_add (div_le_div_of_nonneg_right hnum hh.le) hboundary)
    have hmain : (5 * η * x ^ 2 / (Real.log x) ^ S) / h =
        5 * η * x / (Real.log x) ^ A := unsmoothing_main_term_identity hxp hlogp
    have hbd : 4 * h * Real.log x = (4 / (Real.log x) ^ 2) * (x / (Real.log x) ^ A) :=
      unsmoothing_boundary_identity hlogp
    rw [hmain, hbd] at hnorm
    have hsmall := mul_le_mul_of_nonneg_right htail.le
      (div_nonneg hxp.le (Real.rpow_nonneg hlogp.le A))
    have hηeq : 5 * η = ε / 2 := by dsimp only [η]; ring
    rw [hηeq] at hnorm
    exact hnorm.trans ((add_le_add le_rfl hsmall).trans_eq (by ring))
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hlarge
  refine ⟨max X₀ 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro x t hx hlow hupper
  exact hX₀ x ((le_max_left X₀ 2).trans hx) t hlow hupper

end Erdos421
