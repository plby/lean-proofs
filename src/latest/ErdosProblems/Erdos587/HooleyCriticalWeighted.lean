import ErdosProblems.Erdos587.FrequencyWeights
import ErdosProblems.Erdos587.HooleyCriticalScale

/-!
# Log-log bounds with fixed decaying critical-frequency weights

The power-enlarged cutoff does not introduce a power loss after weighting.
Constants are uniform in every coefficient sequence satisfying the stated
quadratic-decay bound. The underlying Schwartz function remains fixed.
-/

open Filter
open scoped BigOperators SchwartzMap

namespace Erdos587

theorem exists_delta_critical_weighted_nearby_mean (f : 𝓢(ℝ, ℂ))
    (c₀ C₀ : ℝ) (p : ℕ) (hc₀ : 0 < c₀) (hC₀ : 0 ≤ C₀)
    (δ : ℝ) (hδ : δ < 3 / 125) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (a u v H M₀ N : ℕ), 0 < u → 0 < v → 0 < H → 0 < M₀ → M₀ ≤ N →
        a.Coprime u → u.Coprime v → u ∣ a * v + 1 →
        T ^ (1 / 16 : ℝ) ≤ u → (u : ℝ) ≤ Real.sqrt T * T ^ (1 / 1000 : ℝ) →
        c₀ * T ^ (3 / 4 - 1 / 1000 : ℝ) ≤ v → (v : ℝ) ≤ T ^ (3 / 4 : ℝ) →
        Real.sqrt T * T ^ (-(1 / 1000 : ℝ)) ≤ H → (u : ℝ) * H ≤ T →
        (v : ℝ) / H ≤ M₀ →
        (N : ℝ) ≤ C₀ * ((v : ℝ) / H) * T ^ δ * (1 + Real.log T) ^ p →
        ∀ σ W : ℝ, 0 < σ → 0 ≤ W → 1 ≤ σ * M₀ → σ * M₀ ≤ 2 →
        ∀ w : ℕ → ℂ, (∀ m ∈ Finset.Icc 1 N, ‖w m‖ ≤ W * σ / (1 + σ * m) ^ 2) →
          (∑ m ∈ Finset.Icc 1 N,
            ‖w m * nearbyQuadraticRemainder f u m v (a : ℤ) (Real.sqrt T)‖) ≤
            C * W * Real.sqrt (Real.sqrt T) * (max 1 (Real.log (Real.log T))) ^ (9 / 2 : ℝ) := by
  obtain ⟨C, hC, hmean⟩ :=
    exists_delta_critical_nearby_mean_with_power_cutoff f c₀ C₀ p hc₀ hC₀ δ hδ
  refine ⟨4 * C, by positivity, ?_⟩
  filter_upwards [hmean] with T hmeanT
  intro a u v H M₀ N hu hv hH hM₀ hMN ha huv hav hu0 hu1 hv0 hv1 hH0 huH hMlo hNhi
    σ W hσ hW hσlo hσhi w hw
  let D := C * Real.sqrt (Real.sqrt T) * (max 1 (Real.log (Real.log T))) ^ (9 / 2 : ℝ)
  have hlog : 0 ≤ max 1 (Real.log (Real.log T)) := by positivity
  have hD : 0 ≤ D :=
    mul_nonneg (mul_nonneg hC.le (Real.sqrt_nonneg _)) (Real.rpow_nonneg hlog (9 / 2))
  let R : ℕ → ℂ := fun m => nearbyQuadraticRemainder f u m v (a : ℤ) (Real.sqrt T)
  have hprefix : ∀ n ≤ N, (∑ i ∈ Finset.range n, ‖R (i + 1)‖) ≤ D * (n + M₀) := by
    intro n hn
    let M := max n M₀
    have hMn : n ≤ M := le_max_left _ _
    have hMM₀ : M₀ ≤ M := le_max_right _ _
    have hMpos : 0 < M := hM₀.trans_le hMM₀
    have hMN' : M ≤ N := max_le hn hMN
    have hMlower : (v : ℝ) / H ≤ M := hMlo.trans (by exact_mod_cast hMM₀)
    have hMupper : (M : ℝ) ≤ C₀ * ((v : ℝ) / H) * T ^ δ * (1 + Real.log T) ^ p :=
      (by exact_mod_cast hMN' : (M : ℝ) ≤ N).trans hNhi
    have hraw := hmeanT a u v H M hu hv hH hMpos ha huv hav hu0 hu1 hv0 hv1 hH0 huH hMlower hMupper
    rw [sum_range_succ_eq_sum_Icc (fun m => ‖R m‖) n]
    calc
      _ ≤ ∑ m ∈ Finset.Icc 1 M, ‖R m‖ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.Icc_subset_Icc le_rfl hMn
        · intro m hm hnot
          exact norm_nonneg _
      _ ≤ C * M * Real.sqrt (Real.sqrt T) * (max 1 (Real.log (Real.log T))) ^ (9 / 2 : ℝ) := hraw
      _ = D * M := by dsimp [D]; ring
      _ ≤ D * (n + M₀) := mul_le_mul_of_nonneg_left (by
        have hh : M ≤ n + M₀ := by dsimp [M]; omega
        exact_mod_cast hh) hD
  have hweights : ∀ n < N, ‖w (n + 1)‖ ≤ (2 * W) * frequencyDecayKernel M₀ n := by
    intro n hn
    have hh := hw (n + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    calc
      _ ≤ W * (σ / (1 + σ * ((n : ℝ) + 1)) ^ 2) := by
        simpa only [Nat.cast_add, Nat.cast_one, mul_div_assoc] using hh
      _ ≤ W * (2 * frequencyDecayKernel M₀ n) := mul_le_mul_of_nonneg_left
        (physical_frequency_decay_le_kernel hσ hM₀ hσlo hσhi n) hW
      _ = _ := by ring
  apply (sum_decaying_frequency_mul_le hM₀ R w N D (2 * W) hD (by positivity)
    hprefix hweights).trans_eq
  dsimp [D]
  ring

end Erdos587
