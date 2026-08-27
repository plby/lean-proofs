import ErdosProblems.Erdos587.HooleyWideError
import ErdosProblems.Erdos587.HooleyPeriodicMain

/-! # Comparison with the periodic main term in the power-separated branch -/

open Filter
open scoped BigOperators SchwartzMap FourierTransform

namespace Erdos587

theorem exists_delta_wide_count_comparison (f g : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ a q H t : ℕ, 0 < q → 0 < H → H ≤ q → q.Coprime a →
        (q : ℝ) ≤ T ^ (3 / 4 - 1 / 1000 : ℝ) →
        (q : ℝ) * (max 1 (Real.log (Real.log T))) ^ 7 ≤ H * T ^ (1 / 4 : ℝ) →
        let σ := ((q : ℝ) / H)⁻¹
        let M := ⌊T ^ (1 / 4 : ℝ) / (max 1 (Real.log (Real.log T))) ^ 6⌋₊
        ‖weightedSquareCount f g a q t (Real.sqrt T) σ -
          deltaPeriodicSquareMain f g a q t (Real.sqrt T) σ‖ ≤
          C * σ * M * Real.sqrt (Real.sqrt T) * (max 1 (Real.log (Real.log T))) ^ 4 := by
  obtain ⟨C, hC, hmean⟩ := exists_delta_wide_full_error f (𝓕 g : 𝓢(ℝ, ℂ))
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmean, eventually_ge_atTop (1 : ℝ)] with T hm hT
  intro a q H t hq hH hHq hcop hqhi hbudget
  have hh := hm a q H hq hH hHq hcop hqhi hbudget
  let σ := ((q : ℝ) / H)⁻¹
  let M := ⌊T ^ (1 / 4 : ℝ) / (max 1 (Real.log (Real.log T))) ^ 6⌋₊
  have hσ : 0 < σ := inv_pos.mpr (div_pos (by exact_mod_cast hq) (by exact_mod_cast hH))
  have hL : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by linarith)
  change ‖weightedSquareCount f g a q t (Real.sqrt T) σ -
    deltaPeriodicSquareMain f g a q t (Real.sqrt T) σ‖ ≤
      C * σ * M * Real.sqrt (Real.sqrt T) * (max 1 (Real.log (Real.log T))) ^ 4
  rw [delta_weightedSquareCount_sub_periodicMain f g a q t hL hσ]
  have hnorm (m : ℤ) :
      ‖(scaledFourierCoeff g σ m * phase (-(m : ℝ) * a * t / q)) *
        deltaSmoothCenteredQuadratic f (Real.sqrt T) q (m * a)‖ =
      ‖((σ : ℂ) * (𝓕 g : 𝓢(ℝ, ℂ)) (σ * m)) *
        deltaSmoothCenteredQuadratic f (Real.sqrt T) q (a * m)‖ := by
    simp only [scaledFourierCoeff, norm_mul, norm_phase, mul_one, mul_comm m (a : ℤ)]
  have hsum : Summable (fun m : ℤ =>
      ‖(scaledFourierCoeff g σ m * phase (-(m : ℝ) * a * t / q)) *
        deltaSmoothCenteredQuadratic f (Real.sqrt T) q (m * a)‖) :=
    hh.1.congr (fun m => (hnorm m).symm)
  apply (norm_tsum_le_tsum_norm hsum).trans
  simpa only [hnorm] using hh.2

theorem exists_delta_finite_wide_count_comparison (F : Finset 𝓢(ℝ, ℂ))
    (g : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ f ∈ F, ∀ a q H t : ℕ, 0 < q → 0 < H → H ≤ q → q.Coprime a →
        (q : ℝ) ≤ T ^ (3 / 4 - 1 / 1000 : ℝ) →
        (q : ℝ) * (max 1 (Real.log (Real.log T))) ^ 7 ≤ H * T ^ (1 / 4 : ℝ) →
        let σ := ((q : ℝ) / H)⁻¹
        let M := ⌊T ^ (1 / 4 : ℝ) / (max 1 (Real.log (Real.log T))) ^ 6⌋₊
        ‖weightedSquareCount f g a q t (Real.sqrt T) σ -
          deltaPeriodicSquareMain f g a q t (Real.sqrt T) σ‖ ≤
          C * σ * M * Real.sqrt (Real.sqrt T) * (max 1 (Real.log (Real.log T))) ^ 4 := by
  classical
  choose C hC herror using (fun f : 𝓢(ℝ, ℂ) => exists_delta_wide_count_comparison f g)
  let K : ℝ := 1 + ∑ f ∈ F, C f
  have hK : 0 < K := by
    have hh := Finset.sum_nonneg (fun f (_ : f ∈ F) => (hC f).le)
    dsimp [K]
    linarith
  refine ⟨K, hK, ?_⟩
  have hall := (eventually_all_finset F).mpr (fun f _ => herror f)
  filter_upwards [hall] with T hT
  intro f hf a q H t hq hH hHq hcop hqhi hbudget
  have hCf : C f ≤ K := by
    have hh := Finset.single_le_sum (s := F) (f := C) (fun f _ => (hC f).le) hf
    dsimp [K]
    linarith
  apply (hT f hf a q H t hq hH hHq hcop hqhi hbudget).trans
  gcongr

end Erdos587
