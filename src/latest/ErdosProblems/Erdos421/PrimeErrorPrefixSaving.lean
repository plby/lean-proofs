import ErdosProblems.Erdos421.SmoothedPrimeErrorSaving
import ErdosProblems.Erdos421.PrimeErrorUnsmoothing
import ErdosProblems.Erdos421.UnsmoothingParameters

/-! # Logarithmic error bounds for the unsmoothed von Mangoldt-minus-one prefix -/

namespace Erdos421

open Filter Topology

theorem primeErrorPrefix_log_saving {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ X₀ > 1, ∀ x : ℝ, X₀ ≤ x → ‖primeErrorPrefix x‖ ≤ ε * x / (Real.log x) ^ A := by
  let S : ℝ := 2 * A + 3
  let η : ℝ := ε / 10
  have hS : 0 ≤ S := by dsimp only [S]; linarith
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨X₁, _, hsmooth⟩ := smoothedPrimeError_log_saving S hη
  have htail := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp
    Real.tendsto_log_atTop).const_div_atTop (6 : ℝ)
  simp only [Real.rpow_two, Function.comp_apply] at htail
  have hlarge : ∀ᶠ x : ℝ in atTop, ‖primeErrorPrefix x‖ ≤ ε * x / (Real.log x) ^ A := by
    filter_upwards [eventually_ge_atTop (max X₁ 2),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
      log_power_le_self_eventually (A + 3),
      htail.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))]
      with x hx hlog hsize htail
    have hx2 : 2 ≤ x := (le_max_right _ _).trans hx
    have hxX : X₁ ≤ x := (le_max_left _ _).trans hx
    have hxp : 0 < x := by linarith
    have hlogp : 0 < Real.log x := by linarith
    let h : ℝ := x / (Real.log x) ^ (A + 3)
    obtain ⟨hh1, hhx⟩ := unsmoothing_step_bounds hA hlog hsize
    change 1 ≤ h at hh1
    change h ≤ x at hhx
    have hh : 0 < h := by linarith
    have hxh : x + h ≤ 2 * x := by linarith
    have hlogh := unsmoothing_log_bounds hx2 hh.le hhx
    have hloghp : 0 < Real.log (x + h) := hlogp.trans_le hlogh.1
    have hFx := hsmooth x hxX
    have hFh := hsmooth (x + h) (by linarith)
    have hpow : 0 < (Real.log x) ^ S := Real.rpow_pos_of_pos hlogp _
    have hFh' : ‖smoothedPrimeErrorSum (x + h)‖ ≤ 2 * η * x / (Real.log x) ^ S := by
      calc
        _ ≤ η * (x + h) / (Real.log (x + h)) ^ S := hFh
        _ ≤ η * (x + h) / (Real.log x) ^ S :=
          div_le_div_of_nonneg_left (by positivity) hpow
            (Real.rpow_le_rpow hlogp.le hlogh.1 hS)
        _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith only [hxh, hη]) hpow.le
    have hnum : (x + h) * ‖smoothedPrimeErrorSum (x + h)‖ +
        x * ‖smoothedPrimeErrorSum x‖ ≤ 5 * η * x ^ 2 / (Real.log x) ^ S := by
      have h₁ := mul_le_mul hxh hFh' (norm_nonneg _) (by positivity : 0 ≤ 2 * x)
      have h₂ := mul_le_mul_of_nonneg_left hFx hxp.le
      exact (add_le_add h₁ h₂).trans_eq (by ring)
    have hboundary : (h + 1) * (Real.log (x + h) + 1) ≤ 6 * h * Real.log x := by
      have hb := mul_le_mul (by linarith : h + 1 ≤ 2 * h)
        (by linarith [hlogh.2] : Real.log (x + h) + 1 ≤ 3 * Real.log x)
        (by linarith : 0 ≤ Real.log (x + h) + 1) (by positivity : 0 ≤ 2 * h)
      exact hb.trans_eq (by ring)
    have hraw := primeErrorPrefix_unsmoothing_bound (by linarith : 1 ≤ x) hh
    have hnorm : ‖primeErrorPrefix x‖ ≤
        (5 * η * x ^ 2 / (Real.log x) ^ S) / h + 6 * h * Real.log x :=
      hraw.trans (add_le_add (div_le_div_of_nonneg_right hnum hh.le) hboundary)
    have hmain : (5 * η * x ^ 2 / (Real.log x) ^ S) / h =
        5 * η * x / (Real.log x) ^ A := unsmoothing_main_term_identity hxp hlogp
    have hbd : 6 * h * Real.log x = (6 / (Real.log x) ^ 2) * (x / (Real.log x) ^ A) := by
      have h₄ : 4 * h * Real.log x = (4 / (Real.log x) ^ 2) * (x / (Real.log x) ^ A) :=
        unsmoothing_boundary_identity hlogp
      calc
        _ = (3 / 2 : ℝ) * (4 * h * Real.log x) := by ring
        _ = (3 / 2 : ℝ) * ((4 / (Real.log x) ^ 2) * (x / (Real.log x) ^ A)) := by rw [h₄]
        _ = _ := by ring
    rw [hmain, hbd] at hnorm
    have hsmall := mul_le_mul_of_nonneg_right htail.le
      (div_nonneg hxp.le (Real.rpow_nonneg hlogp.le A))
    have hηeq : 5 * η = ε / 2 := by dsimp only [η]; ring
    rw [hηeq] at hnorm
    exact hnorm.trans ((add_le_add le_rfl hsmall).trans_eq (by ring))
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hlarge
  refine ⟨max X₀ 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro x hx
  exact hX₀ x ((le_max_left X₀ 2).trans hx)

end Erdos421
