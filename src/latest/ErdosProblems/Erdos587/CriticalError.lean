import ErdosProblems.Erdos587.CriticalSignedSeries
import ErdosProblems.Erdos587.CriticalZero

/-! The all-frequency critical error, including the zero term. -/

open Filter
open scoped BigOperators SchwartzMap

namespace Erdos587

lemma summable_of_zero_removed {f : ℤ → ℝ}
    (h : Summable (fun m => if m = 0 then 0 else f m)) : Summable f := by
  have hz : Summable (fun m : ℤ => if m = 0 then f 0 else 0) :=
    (hasSum_ite_eq (0 : ℤ) (f 0)).summable
  apply (h.add hz).congr
  intro m
  by_cases hm : m = 0 <;> simp [hm]

theorem exists_critical_full_error_bound (f g : 𝓢(ℝ, ℂ)) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧ ∀ᶠ T : ℝ in atTop,
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
          C * Real.sqrt (Real.sqrt T) * (1 + Real.log T) ^ O := by
  obtain ⟨C, hC, O, hO, hmean⟩ := exists_critical_full_signed_mean_bound f g c₀ hc₀
  obtain ⟨D, hD, hzero⟩ := exists_weighted_nearby_zero_bound f g
  refine ⟨C + D, by positivity, O, hO, ?_⟩
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
    (C + D) * Real.sqrt (Real.sqrt T) * (1 + Real.log T) ^ O
  refine ⟨hFsum, ?_⟩
  rw [hFsum.tsum_eq_add_tsum_ite (0 : ℤ)]
  apply (add_le_add hFzero hraw.2).trans
  have hsqrtsqrt1 : 1 ≤ Real.sqrt (Real.sqrt T) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hsqrt1
  have hlog1 : 1 ≤ 1 + Real.log T := by have := Real.log_nonneg hT; linarith
  have hp1 : 1 ≤ (1 + Real.log T) ^ O := one_le_pow₀ hlog1
  have hbase : 1 ≤ Real.sqrt (Real.sqrt T) * (1 + Real.log T) ^ O := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hbase hD.le
  nlinarith

end Erdos587
