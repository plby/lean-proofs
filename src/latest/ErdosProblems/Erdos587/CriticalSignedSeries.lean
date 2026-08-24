import ErdosProblems.Erdos587.CriticalFullSeries
import ErdosProblems.Erdos587.SignedNearby

/-! The complete nonzero signed-frequency critical error. -/

open Filter
open scoped BigOperators SchwartzMap

namespace Erdos587

theorem exists_critical_full_signed_mean_bound (f g : 𝓢(ℝ, ℂ))
    (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧ ∀ᶠ T : ℝ in atTop,
      ∀ a u v H : ℕ, 0 < u → 0 < v → 0 < H → H ≤ v →
        a.Coprime u → u.Coprime v → u ∣ a * v + 1 →
        T ^ (1 / 16 : ℝ) ≤ u → (u : ℝ) ≤ Real.sqrt T * T ^ (1 / 1000 : ℝ) →
        c₀ * T ^ (3 / 4 - 1 / 1000 : ℝ) ≤ v → (v : ℝ) ≤ T ^ (3 / 4 : ℝ) →
        Real.sqrt T * T ^ (-(1 / 1000 : ℝ)) ≤ H → (u : ℝ) * H ≤ T →
        let σ := ((v : ℝ) / H)⁻¹
        Summable (fun m : ℤ => if m = 0 then 0 else
          ‖((σ : ℂ) * g (σ * m)) * signedNearbyQuadraticRemainder f u m v (a : ℤ) (Real.sqrt T)‖) ∧
        (∑' m : ℤ, if m = 0 then 0 else
          ‖((σ : ℂ) * g (σ * m)) * signedNearbyQuadraticRemainder f u m v (a : ℤ) (Real.sqrt T)‖) ≤
          C * Real.sqrt (Real.sqrt T) * (1 + Real.log T) ^ O := by
  obtain ⟨C₁, hC₁, O₁, hO₁, hpos⟩ := exists_critical_full_positive_mean_bound f g c₀ hc₀
  obtain ⟨C₂, hC₂, O₂, hO₂, hneg⟩ := exists_critical_full_positive_mean_bound
    (conjugateSchwartz f) (reflectedSchwartz g) c₀ hc₀
  refine ⟨C₁ + C₂, by positivity, max O₁ O₂, hO₁.trans_le (le_max_left _ _), ?_⟩
  filter_upwards [hpos, hneg, eventually_ge_atTop (1 : ℝ)] with T hp hn hT
  intro a u v H hu hv hH hHv ha huv hav hu0 hu1 hv0 hv1 hH0 huH
  have hp' := hp a u v H hu hv hH hHv ha huv hav hu0 hu1 hv0 hv1 hH0 huH
  have hn' := hn a u v H hu hv hH hHv ha huv hav hu0 hu1 hv0 hv1 hH0 huH
  let σ := ((v : ℝ) / H)⁻¹
  let S : ℤ → ℝ := fun m => if m = 0 then 0 else
    ‖((σ : ℂ) * g (σ * m)) * signedNearbyQuadraticRemainder f u m v (a : ℤ) (Real.sqrt T)‖
  have hzero : S 0 = 0 := by simp [S]
  have hpos_id (n : ℕ) : S ((n + 1 : ℕ) : ℤ) =
      ‖((σ : ℂ) * g (σ * ((n : ℝ) + 1))) *
        nearbyQuadraticRemainder f u (n + 1) v (a : ℤ) (Real.sqrt T)‖ := by
    dsimp only [S]
    rw [if_neg (by exact_mod_cast Nat.succ_ne_zero n), signedNearbyQuadraticRemainder_nat]
    simp only [Int.cast_natCast, Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_one]
  have hneg_id (n : ℕ) : S (-((n + 1 : ℕ) : ℤ)) =
      ‖((σ : ℂ) * reflectedSchwartz g (σ * ((n : ℝ) + 1))) *
        nearbyQuadraticRemainder (conjugateSchwartz f) u (n + 1) v (a : ℤ) (Real.sqrt T)‖ := by
    dsimp only [S]
    rw [if_neg (neg_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero n)),
      Int.cast_neg, norm_negative_nearby_weighted_term f g hu (n + 1) v a (Real.sqrt T) σ]
    simp only [Nat.cast_add, Nat.cast_one]
  have hpsum : Summable (fun n : ℕ => S ((n + 1 : ℕ) : ℤ)) :=
    hp'.1.congr (fun n => (hpos_id n).symm)
  have hnsum : Summable (fun n : ℕ => S (-((n + 1 : ℕ) : ℤ))) :=
    hn'.1.congr (fun n => (hneg_id n).symm)
  obtain ⟨hSsum, hSsplit⟩ := summable_int_of_positive_negative hzero hpsum hnsum
  have hpbound : (∑' n : ℕ, S ((n + 1 : ℕ) : ℤ)) ≤
      C₁ * Real.sqrt (Real.sqrt T) * (1 + Real.log T) ^ O₁ := by
    simp_rw [hpos_id]
    exact hp'.2
  have hnbound : (∑' n : ℕ, S (-((n + 1 : ℕ) : ℤ))) ≤
      C₂ * Real.sqrt (Real.sqrt T) * (1 + Real.log T) ^ O₂ := by
    simp_rw [hneg_id]
    exact hn'.2
  change Summable S ∧ (∑' m, S m) ≤
    (C₁ + C₂) * Real.sqrt (Real.sqrt T) * (1 + Real.log T) ^ max O₁ O₂
  refine ⟨hSsum, ?_⟩
  rw [hSsplit]
  apply (add_le_add hpbound hnbound).trans
  have hlog1 : 1 ≤ 1 + Real.log T := by have := Real.log_nonneg hT; linarith
  calc
    _ ≤ C₁ * Real.sqrt (Real.sqrt T) * (1 + Real.log T) ^ max O₁ O₂ +
        C₂ * Real.sqrt (Real.sqrt T) * (1 + Real.log T) ^ max O₁ O₂ := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlog1 (le_max_left O₁ O₂)) (by positivity)
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlog1 (le_max_right O₁ O₂)) (by positivity)
    _ = _ := by ring

end Erdos587
