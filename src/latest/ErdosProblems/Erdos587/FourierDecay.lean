import ErdosProblems.Erdos587.FrequencyWeights

/-!
# Scale-normalized Fourier decay of fixed Schwartz weights

The constants depend on the fixed weight and decay order, not on its
physical dilation or the frequency. The same statements apply to its
Schwartz Fourier transform.
-/

open scoped BigOperators SchwartzMap FourierTransform

namespace Erdos587

theorem exists_schwartz_absolute_decay_bound (g : 𝓢(ℝ, ℂ)) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, (1 + |x|) ^ p * ‖g x‖ ≤ C := by
  let C := (2 : ℝ) ^ p * (Finset.Iic (p, 0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro x
  have hh : (1 + |x|) ^ p * ‖g x‖ ≤ C := by
    simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (p, 0))
        (k := p) (n := 0) le_rfl le_rfl g x
  exact hh.trans ((le_abs_self C).trans (by linarith))

theorem exists_scaled_schwartz_decay_bound (g : 𝓢(ℝ, ℂ)) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 0 < σ → ∀ m : ℕ,
      ‖(σ : ℂ) * g (σ * m)‖ ≤ C * σ / (1 + σ * m) ^ p := by
  obtain ⟨C, hC, hdecay⟩ := exists_schwartz_absolute_decay_bound g p
  refine ⟨C, hC, ?_⟩
  intro σ hσ m
  have hh := hdecay (σ * m)
  have hsm : 0 ≤ σ * (m : ℝ) := mul_nonneg hσ.le (Nat.cast_nonneg m)
  rw [abs_of_nonneg hsm] at hh
  have hden : 0 < (1 + σ * m) ^ p := pow_pos (by linarith) p
  have hg : ‖g (σ * m)‖ ≤ C / (1 + σ * m) ^ p :=
    (le_div_iff₀ hden).mpr (by simpa only [mul_comm] using hh)
  calc
    _ = σ * ‖g (σ * m)‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ]
    _ ≤ σ * (C / (1 + σ * m) ^ p) := mul_le_mul_of_nonneg_left hg hσ.le
    _ = _ := by ring

lemma scaled_decay_tail_pointwise {σ C : ℝ} {p N m : ℕ} {a : ℂ}
    (hσ : 0 < σ) (hC : 0 ≤ C) (hN : 0 < N) (hNm : N ≤ m)
    (ha : ‖a‖ ≤ C * σ / (1 + σ * m) ^ (p + 2)) :
    ‖a‖ ≤ (C / (σ * N) ^ p) * (σ / (1 + σ * m) ^ 2) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNmR : (N : ℝ) ≤ m := by exact_mod_cast hNm
  have hm : 0 ≤ σ * (m : ℝ) := mul_nonneg hσ.le (Nat.cast_nonneg m)
  have hbase : σ * (N : ℝ) ≤ 1 + σ * m := by nlinarith
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ σ * N) hbase p
  apply ha.trans
  calc
    _ ≤ (C * σ) / ((σ * N) ^ p * (1 + σ * m) ^ 2) := by
      apply div_le_div_of_nonneg_left (mul_nonneg hC hσ.le) (by positivity)
      rw [pow_add]
      exact mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
    _ = _ := by rw [div_mul_eq_div_div]; ring

theorem exists_scaled_schwartz_positive_tail_bound (g : 𝓢(ℝ, ℂ)) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, ∀ M N : ℕ,
      0 < σ → 0 < M → 0 < N → 1 ≤ σ * M → σ * M ≤ 2 →
      Summable (fun n : ℕ => if N < n + 1 then ‖(σ : ℂ) * g (σ * (n + 1))‖ else 0) ∧
      (∑' n : ℕ, if N < n + 1 then ‖(σ : ℂ) * g (σ * (n + 1))‖ else 0) ≤
        C / (σ * N) ^ p := by
  obtain ⟨C, hC, hdecay⟩ := exists_scaled_schwartz_decay_bound g (p + 2)
  refine ⟨2 * C, by positivity, ?_⟩
  intro σ M N hσ hM hN hlo hhi
  let A := (2 * C) / (σ * N) ^ p
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpoint (n : ℕ) : (if N < n + 1 then ‖(σ : ℂ) * g (σ * (n + 1))‖ else 0) ≤
      A * frequencyDecayKernel M n := by
    split_ifs with hn
    · have hd := scaled_decay_tail_pointwise hσ hC.le hN hn.le (hdecay σ hσ (n + 1))
      have hquad := physical_frequency_decay_le_kernel hσ hM hlo hhi n
      have hp : 0 ≤ C / (σ * N) ^ p := by positivity
      calc
        _ ≤ (C / (σ * N) ^ p) * (σ / (1 + σ * ((n : ℝ) + 1)) ^ 2) := by
          simpa only [Nat.cast_add, Nat.cast_one] using hd
        _ ≤ (C / (σ * N) ^ p) * (2 * frequencyDecayKernel M n) :=
          mul_le_mul_of_nonneg_left hquad hp
        _ = _ := by dsimp [A]; ring
    · exact mul_nonneg hA (frequencyDecayKernel_nonneg M n)
  have hnonneg (n : ℕ) : 0 ≤ (if N < n + 1 then ‖(σ : ℂ) * g (σ * (n + 1))‖ else 0) := by
    split_ifs <;> positivity
  have hpartial (K : ℕ) :
      (∑ n ∈ Finset.range K, if N < n + 1 then ‖(σ : ℂ) * g (σ * (n + 1))‖ else 0) ≤ A := by
    calc
      _ ≤ ∑ n ∈ Finset.range K, A * frequencyDecayKernel M n :=
        Finset.sum_le_sum (fun n hn => hpoint n)
      _ = A * ∑ n ∈ Finset.range K, frequencyDecayKernel M n := (Finset.mul_sum ..).symm
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left (sum_frequencyDecayKernel_le_one hM K) hA
      _ = A := mul_one A
  exact ⟨summable_of_sum_range_le hnonneg hpartial, Real.tsum_le_of_sum_range_le hnonneg hpartial⟩

end Erdos587
