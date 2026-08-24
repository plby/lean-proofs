import ErdosProblems.Erdos587.CriticalWeighted
import ErdosProblems.Erdos587.UniformNearby
import ErdosProblems.Erdos587.PrefixTail

/-!
# The complete positive-frequency critical error

Fixed Schwartz coefficient weights permit summation over all positive
frequencies. The weighted prefix mean controls the enlarged cutoff and
uniform pointwise bounds control the rapidly decaying tail.
-/

open Filter
open scoped BigOperators SchwartzMap

namespace Erdos587

theorem exists_critical_full_positive_mean_bound (f g : 𝓢(ℝ, ℂ))
    (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧ ∀ᶠ T : ℝ in atTop,
      ∀ a u v H : ℕ, 0 < u → 0 < v → 0 < H → H ≤ v →
        a.Coprime u → u.Coprime v → u ∣ a * v + 1 →
        T ^ (1 / 16 : ℝ) ≤ u → (u : ℝ) ≤ Real.sqrt T * T ^ (1 / 1000 : ℝ) →
        c₀ * T ^ (3 / 4 - 1 / 1000 : ℝ) ≤ v → (v : ℝ) ≤ T ^ (3 / 4 : ℝ) →
        Real.sqrt T * T ^ (-(1 / 1000 : ℝ)) ≤ H → (u : ℝ) * H ≤ T →
        let σ := ((v : ℝ) / H)⁻¹
        Summable (fun n : ℕ => ‖((σ : ℂ) * g (σ * (n + 1))) *
          nearbyQuadraticRemainder f u (n + 1) v (a : ℤ) (Real.sqrt T)‖) ∧
        (∑' n : ℕ, ‖((σ : ℂ) * g (σ * (n + 1))) *
          nearbyQuadraticRemainder f u (n + 1) v (a : ℤ) (Real.sqrt T)‖) ≤
          C * Real.sqrt (Real.sqrt T) * (1 + Real.log T) ^ O := by
  obtain ⟨C, hC, O, hO, hmean⟩ := exists_critical_weighted_nearby_mean_bound f c₀ 1 0 hc₀
    (by norm_num) (1 / 100) (by norm_num)
  obtain ⟨W, hW, hdecay⟩ := exists_scaled_schwartz_decay_bound g 2
  obtain ⟨D, hD, hpoint⟩ := exists_uniform_nearby_pointwise_bound f
  obtain ⟨E, hE, htail_sum⟩ := exists_scaled_schwartz_positive_tail_bound g 0
  refine ⟨C * W + 1, by positivity, O, hO, ?_⟩
  filter_upwards [hmean, eventually_scaled_schwartz_power_tail g,
    eventually_ge_atTop (max 1 D),
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 100 by norm_num)).eventually_ge_atTop 4]
    with T hmeanT htailT hT hTpower
  intro a u v H hu hv hH hHv ha huv hav hu0 hu1 hv0 hv1 hH0 huH
  let r := (v : ℝ) / H
  let σ := r⁻¹
  let M := ⌈r⌉₊
  let N := ⌊r * T ^ (1 / 100 : ℝ)⌋₊
  let w : ℕ → ℂ := fun m => (σ : ℂ) * g (σ * m)
  let R : ℕ → ℂ := fun m => nearbyQuadraticRemainder f u m v (a : ℤ) (Real.sqrt T)
  let F : ℕ → ℝ := fun n => ‖w (n + 1) * R (n + 1)‖
  let G : ℕ → ℝ := fun n => if N < n + 1 then ‖w (n + 1)‖ else 0
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hDT : D ≤ T := (le_max_right _ _).trans hT
  have hTpos : 0 < T := by linarith
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hr : 1 ≤ r := (le_div_iff₀ hHR).mpr (by
    simpa only [one_mul] using (show (H : ℝ) ≤ v by exact_mod_cast hHv))
  have hrpos : 0 < r := by linarith
  have hσ : 0 < σ := inv_pos.mpr hrpos
  obtain ⟨hM, hMN, hrM, hNhi, hσlo, hσhi, hscaleN⟩ := normalized_frequency_cutoffs hr hTpower
  have hN : 0 < N := hM.trans_le hMN
  have hNbound : (N : ℝ) ≤ 1 * ((v : ℝ) / H) * T ^ (1 / 100 : ℝ) * (1 + Real.log T) ^ 0 := by
    simpa only [one_mul, pow_zero, mul_one] using hNhi
  have hprefix := hmeanT a u v H M N hu hv hH hM hMN ha huv hav hu0 hu1 hv0 hv1 hH0 huH
    hrM hNbound σ W hσ hW.le hσlo hσhi w (fun m hm => hdecay σ hσ m)
  have hprefix' : (∑ n ∈ Finset.range N, F n) ≤ C * W * Real.sqrt (Real.sqrt T) * (1 + Real.log T) ^ O := by
    rw [show (∑ n ∈ Finset.range N, F n) = ∑ m ∈ Finset.Icc 1 N, ‖w m * R m‖ from
      sum_range_succ_eq_sum_Icc (fun m => ‖w m * R m‖) N]
    exact hprefix
  have hG : Summable G := by
    simpa only [G, w, Nat.cast_add, Nat.cast_one] using (htail_sum σ M N hσ hM hN hσlo hσhi).1
  have hGbound : (∑' n, G n) ≤ 1 / T ^ 2 := by
    simpa only [G, w, Nat.cast_add, Nat.cast_one] using htailT r hr
  have hsqrt1 : 1 ≤ Real.sqrt T := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hT1
  have hR (m : ℕ) : ‖R m‖ ≤ D * Real.sqrt T := hpoint u m v hu a (Real.sqrt T) hsqrt1
  have hmajor (n : ℕ) : (if N < n + 1 then F n else 0) ≤ (D * Real.sqrt T) * G n := by
    dsimp only [G]
    split_ifs with hn
    · dsimp only [F]
      rw [norm_mul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hR (n + 1)) (norm_nonneg (w (n + 1)))
    · simp
  have hFnonneg (n : ℕ) : 0 ≤ F n := norm_nonneg _
  have htailnonneg (n : ℕ) : 0 ≤ (if N < n + 1 then F n else 0) := by
    split_ifs <;> simp [hFnonneg]
  have hFtail : Summable (fun n => if N < n + 1 then F n else 0) := by
    apply (hG.mul_left (D * Real.sqrt T)).of_norm_bounded
    intro n
    rw [Real.norm_of_nonneg (htailnonneg n)]
    exact hmajor n
  have hFtailbound : (∑' n, if N < n + 1 then F n else 0) ≤ 1 := by
    calc
      _ ≤ ∑' n, (D * Real.sqrt T) * G n := hFtail.tsum_le_tsum hmajor (hG.mul_left _)
      _ = (D * Real.sqrt T) * ∑' n, G n := tsum_mul_left
      _ ≤ (D * Real.sqrt T) * (1 / T ^ 2) :=
        mul_le_mul_of_nonneg_left hGbound (by positivity)
      _ ≤ 1 := by
        have hsqrtT : Real.sqrt T ≤ T := (Real.sqrt_le_iff).mpr ⟨hTpos.le, by nlinarith⟩
        have hh := mul_le_mul hDT hsqrtT (Real.sqrt_nonneg T) hTpos.le
        rw [← mul_div_assoc, mul_one]
        apply (div_le_one₀ (sq_pos_of_pos hTpos)).mpr
        simpa only [pow_two] using hh
  obtain ⟨hFsum, hFbound⟩ := summable_and_tsum_le_prefix_add_tail F N hFnonneg hFtail
  have hbound : (∑' n, F n) ≤ (C * W + 1) * Real.sqrt (Real.sqrt T) * (1 + Real.log T) ^ O := by
    apply hFbound.trans ((add_le_add hprefix' hFtailbound).trans ?_)
    have hsqrtsqrt1 : 1 ≤ Real.sqrt (Real.sqrt T) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hsqrt1
    have hlog1 : 1 ≤ 1 + Real.log T := by have := Real.log_nonneg hT1; linarith
    have hp1 : 1 ≤ (1 + Real.log T) ^ O := one_le_pow₀ hlog1
    have hh : 1 ≤ Real.sqrt (Real.sqrt T) * (1 + Real.log T) ^ O := by
      nlinarith
    nlinarith
  simpa only [F, w, R, Nat.cast_add, Nat.cast_one] using And.intro hFsum hbound

end Erdos587
