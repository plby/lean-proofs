import ErdosProblems.Erdos587.HooleyWideSignedSeries
import ErdosProblems.Erdos587.HooleyCenteredZero
import ErdosProblems.Erdos587.CriticalError

/-! # The all-frequency centered error in the power-separated branch -/

open Filter
open scoped BigOperators SchwartzMap

namespace Erdos587

theorem exists_delta_wide_full_error (f g : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ a q H : ℕ, 0 < q → 0 < H → H ≤ q → q.Coprime a →
        (q : ℝ) ≤ T ^ (3 / 4 - 1 / 1000 : ℝ) →
        (q : ℝ) * (max 1 (Real.log (Real.log T))) ^ 7 ≤ H * T ^ (1 / 4 : ℝ) →
        let σ := ((q : ℝ) / H)⁻¹
        let M := ⌊T ^ (1 / 4 : ℝ) / (max 1 (Real.log (Real.log T))) ^ 6⌋₊
        Summable (fun m : ℤ =>
          ‖((σ : ℂ) * g (σ * m)) * deltaSmoothCenteredQuadratic f (Real.sqrt T) q (a * m)‖) ∧
        (∑' m : ℤ,
          ‖((σ : ℂ) * g (σ * m)) * deltaSmoothCenteredQuadratic f (Real.sqrt T) q (a * m)‖) ≤
          C * σ * M * Real.sqrt (Real.sqrt T) * (max 1 (Real.log (Real.log T))) ^ 4 := by
  obtain ⟨C, hC, hmean⟩ := exists_delta_wide_full_signed_mean f g
  obtain ⟨D, hD, hzero⟩ := exists_delta_centered_zero_bound f
  refine ⟨C + D * ‖g 0‖, by positivity, ?_⟩
  filter_upwards [hmean, eventually_delta_wide_cutoff_bounds 6, eventually_ge_atTop (1 : ℝ)]
    with T hm hcut hT
  intro a q H hq hH hHq hcop hqhi hbudget
  have hraw := hm a q H hq hH hHq hcop hqhi hbudget
  let σ := ((q : ℝ) / H)⁻¹
  let Λ := max 1 (Real.log (Real.log T))
  let M := ⌊T ^ (1 / 4 : ℝ) / Λ ^ 6⌋₊
  let F : ℤ → ℝ := fun m =>
    ‖((σ : ℂ) * g (σ * m)) * deltaSmoothCenteredQuadratic f (Real.sqrt T) q (a * m)‖
  have hFsum : Summable F := summable_of_zero_removed hraw.1
  have hσ : 0 < σ := inv_pos.mpr (div_pos (by exact_mod_cast hq) (by exact_mod_cast hH))
  have hsqrt1 : 1 ≤ Real.sqrt T := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hT
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hcut.1
  have hΛpow : 1 ≤ Λ ^ 4 := one_le_pow₀ (le_max_left _ _)
  have hFzero : F 0 ≤ (D * ‖g 0‖) * σ * M * Real.sqrt (Real.sqrt T) * Λ ^ 4 := by
    dsimp only [F]
    simp only [Int.cast_zero, mul_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hσ]
    calc
      _ ≤ σ * ‖g 0‖ * (D * Real.sqrt (Real.sqrt T)) := by
        gcongr
        exact hzero q hq (Real.sqrt T) hsqrt1
      _ = (D * ‖g 0‖) * σ * 1 * Real.sqrt (Real.sqrt T) * 1 := by ring
      _ ≤ _ := by gcongr
  change Summable F ∧ (∑' m, F m) ≤
    (C + D * ‖g 0‖) * σ * M * Real.sqrt (Real.sqrt T) * Λ ^ 4
  refine ⟨hFsum, ?_⟩
  rw [hFsum.tsum_eq_add_tsum_ite (0 : ℤ)]
  exact (add_le_add hFzero hraw.2).trans_eq (by ring)

end Erdos587
