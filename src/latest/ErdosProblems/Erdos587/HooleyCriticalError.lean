import ErdosProblems.Erdos587.HooleyCriticalSignedSeries
import ErdosProblems.Erdos587.CriticalError

/-! The all-frequency critical error, including the zero term. -/

open Filter
open scoped BigOperators SchwartzMap

namespace Erdos587

theorem exists_delta_critical_full_error (f g : 𝓢(ℝ, ℂ)) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ a u v H : ℕ, 0 < u → 0 < v → 0 < H → H ≤ v →
        a.Coprime u → u.Coprime v → u ∣ a * v + 1 →
        T ^ (1 / 16 : ℝ) ≤ u → (u : ℝ) ≤ Real.sqrt T * T ^ (1 / 1000 : ℝ) →
        c₀ * T ^ (3 / 4 - 1 / 1000 : ℝ) ≤ v → (v : ℝ) ≤ T ^ (3 / 4 : ℝ) →
        Real.sqrt T * T ^ (-(1 / 1000 : ℝ)) ≤ H → (u : ℝ) * H ≤ T →
        let σ := ((v : ℝ) / H)⁻¹
        Summable (fun m : ℤ =>
          ‖((σ : ℂ) * g (σ * m)) * signedNearbyQuadraticRemainder f u m v (a : ℤ) (Real.sqrt T)‖) ∧
        (∑' m : ℤ,
          ‖((σ : ℂ) * g (σ * m)) * signedNearbyQuadraticRemainder f u m v (a : ℤ) (Real.sqrt T)‖) ≤
          C * Real.sqrt (Real.sqrt T) * (max 1 (Real.log (Real.log T))) ^ (9 / 2 : ℝ) := by
  obtain ⟨C, hC, hmean⟩ := exists_delta_critical_full_signed_mean f g c₀ hc₀
  obtain ⟨D, hD, hzero⟩ := exists_weighted_nearby_zero_bound f g
  refine ⟨C + D, by positivity, ?_⟩
  filter_upwards [hmean, eventually_ge_atTop (1 : ℝ)] with T hm hT
  intro a u v H hu hv hH hHv ha huv hav hu0 hu1 hv0 hv1 hH0 huH
  have hraw := hm a u v H hu hv hH hHv ha huv hav hu0 hu1 hv0 hv1 hH0 huH
  let σ := ((v : ℝ) / H)⁻¹
  let F : ℤ → ℝ := fun m =>
    ‖((σ : ℂ) * g (σ * m)) * signedNearbyQuadraticRemainder f u m v (a : ℤ) (Real.sqrt T)‖
  have hFsum : Summable F := summable_of_zero_removed hraw.1
  have hsqrt1 : 1 ≤ Real.sqrt T := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hT
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hr : 1 ≤ (v : ℝ) / H := (le_div_iff₀ hHR).mpr (by
    simpa only [one_mul] using (show (H : ℝ) ≤ v by exact_mod_cast hHv))
  have hσ : 0 ≤ σ := inv_nonneg.mpr (div_nonneg hvR.le hHR.le)
  have hσ1 : σ ≤ 1 := by
    change ((v : ℝ) / H)⁻¹ ≤ 1
    rw [← one_div]
    exact (div_le_one₀ (div_pos hvR hHR)).mpr hr
  have hFzero : F 0 ≤ D := by
    simpa only [F, Int.cast_zero, mul_zero] using hzero u hu v a (Real.sqrt T) σ hsqrt1 hσ hσ1
  change Summable F ∧ (∑' m, F m) ≤
    (C + D) * Real.sqrt (Real.sqrt T) * (max 1 (Real.log (Real.log T))) ^ (9 / 2 : ℝ)
  refine ⟨hFsum, ?_⟩
  rw [hFsum.tsum_eq_add_tsum_ite (0 : ℤ)]
  apply (add_le_add hFzero hraw.2).trans
  have hsqrtsqrt1 : 1 ≤ Real.sqrt (Real.sqrt T) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hsqrt1
  have hlog1 : 1 ≤ max 1 (Real.log (Real.log T)) := le_max_left _ _
  have hp1 : 1 ≤ (max 1 (Real.log (Real.log T))) ^ (9 / 2 : ℝ) :=
    Real.one_le_rpow hlog1 (by norm_num)
  have hbase : 1 ≤ Real.sqrt (Real.sqrt T) * (max 1 (Real.log (Real.log T))) ^ (9 / 2 : ℝ) := by
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hbase hD.le
  nlinarith

end Erdos587
