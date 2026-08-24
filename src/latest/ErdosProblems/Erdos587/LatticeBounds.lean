import ErdosProblems.Erdos587.CriticalCutoffs

/-!
# Uniform norms of sampled Schwartz weights

The total absolute mass of a weight sampled at spacing `1/L` is `O(L)`.
This supplies a frequency-independent bound for the far Fourier tail.
-/

open scoped BigOperators SchwartzMap

namespace Erdos587

lemma normalized_lattice_kernel_bound {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Summable (fun n : ℤ => σ / (1 + σ * |(n : ℝ)|) ^ 2) ∧
      (∑' n : ℤ, σ / (1 + σ * |(n : ℝ)|) ^ 2) ≤ 5 := by
  have hr : 1 ≤ σ⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hσ).mpr (by simpa using hσ1)
  obtain ⟨hM, hMN, hrM, hNhi, hscale₀, hscale₁, hscaleN⟩ :=
    normalized_frequency_cutoffs hr (show (4 : ℝ) ≤ 4 by rfl)
  simp only [inv_inv] at hscale₀ hscale₁
  let M := ⌈σ⁻¹⌉₊
  let k : ℤ → ℝ := fun n => σ / (1 + σ * |(n : ℝ)|) ^ 2
  have hk (n : ℤ) : 0 ≤ k n := by dsimp [k]; positivity
  have hpoint (n : ℕ) : k ((n + 1 : ℕ) : ℤ) ≤ 2 * frequencyDecayKernel M n := by
    simpa only [k, Int.cast_natCast, Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)] using
      physical_frequency_decay_le_kernel hσ hM hscale₀ hscale₁ n
  have hpartial (N : ℕ) : (∑ n ∈ Finset.range N, k ((n + 1 : ℕ) : ℤ)) ≤ 2 := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, 2 * frequencyDecayKernel M n :=
        Finset.sum_le_sum (fun n hn => hpoint n)
      _ = 2 * ∑ n ∈ Finset.range N, frequencyDecayKernel M n := (Finset.mul_sum ..).symm
      _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left (sum_frequencyDecayKernel_le_one hM N) (by norm_num)
      _ = 2 := by norm_num
  have hpos : Summable (fun n : ℕ => k ((n + 1 : ℕ) : ℤ)) :=
    summable_of_sum_range_le (fun n => hk _) hpartial
  have hposbound : (∑' n : ℕ, k ((n + 1 : ℕ) : ℤ)) ≤ 2 :=
    Real.tsum_le_of_sum_range_le (fun n => hk _) hpartial
  have hnat : Summable (fun n : ℕ => k (n : ℤ)) := (summable_nat_add_iff 1).mp hpos
  have hneg : Summable (fun n : ℕ => k (-(n : ℤ))) := by
    simpa only [k, Int.cast_neg, abs_neg] using hnat
  have hall : Summable k := hnat.of_nat_of_neg hneg
  refine ⟨hall, ?_⟩
  have heven : Function.Even k := by intro n; simp [k]
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hall,
    tsum_pnat_eq_tsum_succ (f := fun n : ℕ => k (n : ℤ))]
  have hzero : k 0 = σ := by simp [k]
  rw [hzero]
  norm_num only [nsmul_eq_mul, Nat.cast_ofNat]
  linarith

theorem exists_schwartz_lattice_norm_bound (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L →
      (∑' n : ℤ, ‖f (L⁻¹ * n)‖) ≤ C * L := by
  obtain ⟨C, hC, hdecay⟩ := exists_schwartz_absolute_decay_bound f 2
  refine ⟨5 * C, by positivity, ?_⟩
  intro L hL
  have hLpos : 0 < L := by linarith
  have hσ : 0 < L⁻¹ := inv_pos.mpr hLpos
  have hσ1 : L⁻¹ ≤ 1 := by
    rw [← one_div]
    exact (div_le_one₀ hLpos).mpr hL
  obtain ⟨hsum, hbound⟩ := normalized_lattice_kernel_bound hσ hσ1
  have hpoint (n : ℤ) : ‖f (L⁻¹ * n)‖ ≤
      (C * L) * (L⁻¹ / (1 + L⁻¹ * |(n : ℝ)|) ^ 2) := by
    have hh := hdecay (L⁻¹ * n)
    rw [abs_mul, abs_of_pos hσ] at hh
    have hden : 0 < (1 + L⁻¹ * |(n : ℝ)|) ^ 2 := by positivity
    calc
      _ ≤ C / (1 + L⁻¹ * |(n : ℝ)|) ^ 2 :=
        (le_div_iff₀ hden).mpr (by simpa only [mul_comm] using hh)
      _ = _ := by field_simp
  have hsample : Summable (fun n : ℤ => ‖f (L⁻¹ * n)‖) := by
    simpa only [dilateSchwartz_apply] using
      (summable_schwartz_int (dilateSchwartz f L⁻¹ (inv_ne_zero hLpos.ne'))).norm
  calc
    _ ≤ ∑' n : ℤ, (C * L) * (L⁻¹ / (1 + L⁻¹ * |(n : ℝ)|) ^ 2) :=
      hsample.tsum_le_tsum hpoint (hsum.mul_left _)
    _ = (C * L) * ∑' n : ℤ, L⁻¹ / (1 + L⁻¹ * |(n : ℝ)|) ^ 2 := tsum_mul_left
    _ ≤ (C * L) * 5 := mul_le_mul_of_nonneg_left hbound (mul_nonneg hC.le hLpos.le)
    _ = _ := by ring

end Erdos587
