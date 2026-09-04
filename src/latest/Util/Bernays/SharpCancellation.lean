import Util.Bernays.SharpCutoffError

/-!
# Removal of smoothing at the Bernays counting scale
-/

open Set Filter Topology
open scoped ContDiff

namespace Bernays

theorem sharp_cancellation_of_smooth (a : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hA : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, ‖a n‖) / scale N) atTop (𝓝 C))
    (hsm : ∀ Ψ : ℝ → ℂ, ContDiff ℝ ∞ Ψ → HasCompactSupport Ψ → tsupport Ψ ⊆ Ioi 0 →
      Tendsto (fun x : ℝ => ‖∑' n : ℕ, a n * Ψ ((n : ℝ) / x)‖ / scale x) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ‖∑ n ∈ Finset.Icc 1 N, a n‖ / scale N) atTop (𝓝 0) := by
  let A (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, ‖a n‖
  rw [Metric.tendsto_nhds]
  intro η hη
  let ε := η / (8 * (C + 1))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨Ψ, hΨ, hsupp, hplus, hΨbounds, hΨ₀, hone, hsup⟩ := exists_sharp_cutoff hε
  have hΨC : ContDiff ℝ ∞ (fun y : ℝ => (Ψ y : ℂ)) := contDiff_ofReal.comp hΨ
  have hsuppC : HasCompactSupport (fun y : ℝ => (Ψ y : ℂ)) :=
    hsupp.comp_left (g := Complex.ofReal) rfl
  have hplusC : tsupport (fun y : ℝ => (Ψ y : ℂ)) ⊆ Ioi 0 := by
    have heq : Function.support (fun y : ℝ => (Ψ y : ℂ)) = Function.support Ψ := by
      ext y
      simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
    simpa only [tsupport, heq] using hplus
  have hS := (hsm (fun y : ℝ => (Ψ y : ℂ)) hΨC hsuppC hplusC).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlo := (count_floor_dilation_limit hA hε).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hhi := (count_floor_dilation_limit hA (show 0 < 1 + ε by linarith)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hE : Tendsto (fun N : ℕ =>
      (A ⌊ε * N⌋₊ + A ⌊(1 + ε) * N⌋₊ - A N) / scale N) atTop (𝓝 (2 * C * ε)) := by
    have h := (hlo.add hhi).sub hA
    have hid : C * ε + C * (1 + ε) - C = 2 * C * ε := by ring
    rw [hid] at h
    convert h using 1
    funext N
    dsimp only [Function.comp_def, A]
    ring
  have hεbound : 2 * C * ε ≤ η / 4 := by
    have hden : 0 < 8 * (C + 1) := by positivity
    have hid : ε * (8 * (C + 1)) = η := by
      dsimp only [ε]
      exact div_mul_cancel₀ _ hden.ne'
    nlinarith
  filter_upwards [eventually_ge_atTop 2,
    hS.eventually (gt_mem_nhds (show (0 : ℝ) < η / 4 by positivity)),
    hE.eventually (gt_mem_nhds (show 2 * C * ε < 2 * C * ε + η / 4 by linarith))]
    with N hN hSN hEN
  have hN₀ : 0 < N := by omega
  have hscale : 0 < scale N := scale_pos (by exact_mod_cast hN)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (norm_nonneg _) hscale.le)]
  have herror := natural_sharp_cutoff_error a hε Ψ hΨbounds hΨ₀ hone hsup hN₀
  let S : ℂ := ∑' n : ℕ, a n * (Ψ ((n : ℝ) / N) : ℂ)
  have htri : ‖∑ n ∈ Finset.Icc 1 N, a n‖ ≤
      ‖(∑ n ∈ Finset.Icc 1 N, a n) - S‖ + ‖S‖ := by
    calc
      _ = ‖((∑ n ∈ Finset.Icc 1 N, a n) - S) + S‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hsum := htri.trans (add_le_add herror le_rfl)
  have hdiv := div_le_div_of_nonneg_right hsum hscale.le
  rw [add_div] at hdiv
  change ‖S‖ / scale N < η / 4 at hSN
  change (A ⌊ε * N⌋₊ + A ⌊(1 + ε) * N⌋₊ - A N) / scale N < 2 * C * ε + η / 4 at hEN
  change ‖∑ n ∈ Finset.Icc 1 N, a n‖ / scale N ≤
    (A ⌊ε * N⌋₊ + A ⌊(1 + ε) * N⌋₊ - A N) / scale N + ‖S‖ / scale N at hdiv
  linarith

theorem genusLocal_sharp_norm_cancellation {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ, ψ ≠ 0 →
      Tendsto (fun N : ℕ => ‖∑ n ∈ Finset.Icc 1 N, genusLocalAF hD ψ n‖ / scale N)
        atTop (𝓝 0) := by
  let := quadraticOrderIsDomain hD
  intro ψ hψ
  apply sharp_cancellation_of_smooth (genusLocalAF hD ψ) (goodLocalConstant_pos hD).le
  · simpa only [genusLocalAF_sum_norm] using goodLocalValues_card_limit hD
  · intro Ψ hΨ hsupp hplus
    exact spatial_smooth_cancellation_atTop (genusLocal_spatial_smooth_cancellation hD ψ hψ Ψ hΨ hsupp hplus)

end Bernays
