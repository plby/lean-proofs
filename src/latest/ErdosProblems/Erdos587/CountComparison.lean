import ErdosProblems.Erdos587.AlternativeMain
import ErdosProblems.Erdos587.CriticalError

/-! Exact count-minus-main identity and its critical-scale error bound. -/

open Filter
open scoped BigOperators SchwartzMap FourierTransform

namespace Erdos587

theorem weightedSquareCount_sub_alternativeMain (f g : 𝓢(ℝ, ℂ))
    {a u b v : ℕ} (hu : 0 < u) (hv : 0 < v) (hab : a * u = b * v + 1)
    (t : ℕ) {L σ : ℝ} (hL : 0 < L) (hσ : 0 < σ) :
    weightedSquareCount f g a v t L σ - alternativeSquareMain f g a u b v t L σ =
      ∑' m : ℤ, (scaledFourierCoeff g σ m * phase (-(m : ℝ) * a * t / v)) *
        signedNearbyQuadraticRemainder f u m v b L := by
  rw [weightedSquareCount_fourier f g hu hv hab t hL hσ,
    alternativeSquareMain_fourier f g a u b v t hL hσ,
    ← Summable.tsum_sub (summable_weightedSquareCount_fourier f g hu hv hab t hL hσ)
      (summable_alternativeSquareMain_fourier f g a u b v t hu hL hσ)]
  apply tsum_congr
  intro m
  rw [signedNearbyQuadraticRemainder_eq_lattice_sub_main, mul_sub]

theorem exists_critical_count_comparison (f g : 𝓢(ℝ, ℂ)) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧ ∀ᶠ T : ℝ in atTop,
      ∀ a b u v H t : ℕ, 0 < u → 0 < v → 0 < H → H ≤ v →
        a * u = b * v + 1 → b.Coprime u → u.Coprime v →
        T ^ (1 / 16 : ℝ) ≤ u → (u : ℝ) ≤ Real.sqrt T * T ^ (1 / 1000 : ℝ) →
        c₀ * T ^ (3 / 4 - 1 / 1000 : ℝ) ≤ v → (v : ℝ) ≤ T ^ (3 / 4 : ℝ) →
        Real.sqrt T * T ^ (-(1 / 1000 : ℝ)) ≤ H → (u : ℝ) * H ≤ T →
        let σ := ((v : ℝ) / H)⁻¹
        ‖weightedSquareCount f g a v t (Real.sqrt T) σ -
          alternativeSquareMain f g a u b v t (Real.sqrt T) σ‖ ≤
          C * Real.sqrt (Real.sqrt T) * (1 + Real.log T) ^ O := by
  obtain ⟨C, hC, O, hO, hmean⟩ :=
    exists_critical_full_error_bound f (𝓕 g : 𝓢(ℝ, ℂ)) c₀ hc₀
  refine ⟨C, hC, O, hO, ?_⟩
  filter_upwards [hmean, eventually_ge_atTop (1 : ℝ)] with T hm hT
  intro a b u v H t hu hv hH hHv hab hb huv hu0 hu1 hv0 hv1 hH0 huH
  have hdiv : u ∣ b * v + 1 := by
    rw [← hab]
    exact dvd_mul_left u a
  have hh := hm b u v H hu hv hH hHv hb huv hdiv hu0 hu1 hv0 hv1 hH0 huH
  let σ := ((v : ℝ) / H)⁻¹
  have hσ : 0 < σ := inv_pos.mpr (div_pos (by exact_mod_cast hv) (by exact_mod_cast hH))
  have hL : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by linarith)
  change ‖weightedSquareCount f g a v t (Real.sqrt T) σ -
    alternativeSquareMain f g a u b v t (Real.sqrt T) σ‖ ≤
      C * Real.sqrt (Real.sqrt T) * (1 + Real.log T) ^ O
  rw [weightedSquareCount_sub_alternativeMain f g hu hv hab t hL hσ]
  have hnorm (m : ℤ) :
      ‖(scaledFourierCoeff g σ m * phase (-(m : ℝ) * a * t / v)) *
        signedNearbyQuadraticRemainder f u m v b (Real.sqrt T)‖ =
      ‖((σ : ℂ) * (𝓕 g : 𝓢(ℝ, ℂ)) (σ * m)) *
        signedNearbyQuadraticRemainder f u m v b (Real.sqrt T)‖ := by
    simp only [scaledFourierCoeff, norm_mul, norm_phase, mul_one]
  have hsum : Summable (fun m : ℤ =>
      ‖(scaledFourierCoeff g σ m * phase (-(m : ℝ) * a * t / v)) *
        signedNearbyQuadraticRemainder f u m v b (Real.sqrt T)‖) := hh.1.congr (fun m => (hnorm m).symm)
  apply (norm_tsum_le_tsum_norm hsum).trans
  simpa only [hnorm] using hh.2

end Erdos587
