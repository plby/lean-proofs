import ErdosProblems.Erdos587.CriticalScale

/-!
# Decaying frequency weights from prefix means

Summation by parts turns a linear prefix budget into a bounded weighted
sum. A telescoping rational kernel captures quadratic Fourier decay.
-/

open scoped BigOperators

namespace Erdos587

lemma sum_antitone_mul_le_of_prefix (f g w : ℕ → ℝ) (N : ℕ)
    (hw : ∀ n, 0 ≤ w n) (hwanti : Antitone w)
    (hprefix : ∀ n ≤ N, (∑ i ∈ Finset.range n, f i) ≤ ∑ i ∈ Finset.range n, g i) :
    (∑ n ∈ Finset.range N, w n * f n) ≤ ∑ n ∈ Finset.range N, w n * g n := by
  have hf := Finset.sum_range_by_parts w f N
  have hg := Finset.sum_range_by_parts w g N
  simp only [smul_eq_mul] at hf hg
  rw [hf, hg]
  apply sub_le_sub
  · exact mul_le_mul_of_nonneg_left (hprefix N le_rfl) (hw _)
  · apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonpos_left (hprefix (n + 1) (by
      have := Finset.mem_range.mp hn
      omega)) (sub_nonpos.mpr (hwanti (Nat.le_succ n)))

lemma sum_antitone_mul_le_linear_prefix (f w : ℕ → ℝ) (N M : ℕ) (D : ℝ)
    (hD : 0 ≤ D) (hw : ∀ n, 0 ≤ w n) (hwanti : Antitone w)
    (hprefix : ∀ n ≤ N, (∑ i ∈ Finset.range n, f i) ≤ D * (n + M)) :
    (∑ n ∈ Finset.range N, w n * f n) ≤
      D * ((∑ n ∈ Finset.range N, w n) + M * w 0) := by
  classical
  by_cases hN : N = 0
  · simp only [hN, Finset.range_zero, Finset.sum_empty, zero_add]
    exact mul_nonneg hD (mul_nonneg (Nat.cast_nonneg M) (hw 0))
  let g : ℕ → ℝ := fun n => D + if n = 0 then D * M else 0
  have hprefixg : ∀ n ≤ N, (∑ i ∈ Finset.range n, f i) ≤ ∑ i ∈ Finset.range n, g i := by
    intro n hn
    by_cases hn0 : n = 0
    · simp [hn0]
    have hg : (∑ i ∈ Finset.range n, g i) = D * (n + M) := by
      simp [g, Finset.sum_add_distrib, Nat.pos_of_ne_zero hn0]
      ring
    rw [hg]
    exact hprefix n hn
  apply (sum_antitone_mul_le_of_prefix f g w N hw hwanti hprefixg).trans_eq
  simp only [g, mul_add, Finset.sum_add_distrib]
  have hspike : (∑ n ∈ Finset.range N, w n * if n = 0 then D * M else 0) = w 0 * (D * M) := by
    simp only [mul_ite, mul_zero]
    simp [Nat.pos_of_ne_zero hN]
  rw [hspike, ← Finset.sum_mul]
  ring

noncomputable def frequencyDecayKernel (M n : ℕ) : ℝ :=
  (M : ℝ) / (((M : ℝ) + n) * ((M : ℝ) + n + 1))

lemma frequencyDecayKernel_nonneg (M n : ℕ) : 0 ≤ frequencyDecayKernel M n := by
  unfold frequencyDecayKernel
  positivity

lemma frequencyDecayKernel_antitone {M : ℕ} (hM : 0 < M) : Antitone (frequencyDecayKernel M) := by
  intro a b hab
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  unfold frequencyDecayKernel
  apply div_le_div_of_nonneg_left hMR.le (by positivity)
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  gcongr

lemma frequencyDecayKernel_eq_difference {M : ℕ} (hM : 0 < M) (n : ℕ) :
    frequencyDecayKernel M n = (M : ℝ) *
      (1 / ((M : ℝ) + n) - 1 / ((M : ℝ) + n + 1)) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  unfold frequencyDecayKernel
  field_simp
  ring

lemma sum_frequencyDecayKernel {M : ℕ} (hM : 0 < M) (N : ℕ) :
    (∑ n ∈ Finset.range N, frequencyDecayKernel M n) = 1 - (M : ℝ) / (M + N) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  induction N with
  | zero => simp [hMR.ne']
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, frequencyDecayKernel_eq_difference hM]
    push_cast
    ring

lemma sum_frequencyDecayKernel_le_one {M : ℕ} (hM : 0 < M) (N : ℕ) :
    (∑ n ∈ Finset.range N, frequencyDecayKernel M n) ≤ 1 := by
  rw [sum_frequencyDecayKernel hM]
  have : 0 ≤ (M : ℝ) / (M + N) := by positivity
  linarith

lemma frequencyDecayKernel_initial_budget {M : ℕ} (hM : 0 < M) :
    (M : ℝ) * frequencyDecayKernel M 0 ≤ 1 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  unfold frequencyDecayKernel
  simp only [Nat.cast_zero, add_zero]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < M * (M + 1))).mpr
  nlinarith

theorem sum_frequencyDecayKernel_mul_le {M : ℕ} (hM : 0 < M)
    (f : ℕ → ℝ) (N : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hprefix : ∀ n ≤ N, (∑ i ∈ Finset.range n, f i) ≤ D * (n + M)) :
    (∑ n ∈ Finset.range N, frequencyDecayKernel M n * f n) ≤ 2 * D := by
  apply (sum_antitone_mul_le_linear_prefix f (frequencyDecayKernel M) N M D hD
    (frequencyDecayKernel_nonneg M) (frequencyDecayKernel_antitone hM) hprefix).trans
  have hs := sum_frequencyDecayKernel_le_one hM N
  have hi := frequencyDecayKernel_initial_budget hM
  nlinarith

lemma sum_range_succ_eq_sum_Icc {β : Type*} [AddCommMonoid β] (f : ℕ → β) (N : ℕ) :
    (∑ n ∈ Finset.range N, f (n + 1)) = ∑ n ∈ Finset.Icc 1 N, f n := by
  apply Finset.sum_bij (fun n _ => n + 1)
  · intro n hn
    have := Finset.mem_range.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro a ha b hb hab
    omega
  · intro m hm
    obtain ⟨hmlo, hmhi⟩ := Finset.mem_Icc.mp hm
    exact ⟨m - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro n hn
    rfl

theorem sum_decaying_frequency_mul_le {M : ℕ} (hM : 0 < M)
    (f w : ℕ → ℂ) (N : ℕ) (D W : ℝ) (hD : 0 ≤ D) (hW : 0 ≤ W)
    (hprefix : ∀ n ≤ N, (∑ i ∈ Finset.range n, ‖f (i + 1)‖) ≤ D * (n + M))
    (hweight : ∀ n < N, ‖w (n + 1)‖ ≤ W * frequencyDecayKernel M n) :
    (∑ n ∈ Finset.Icc 1 N, ‖w n * f n‖) ≤ 2 * W * D := by
  rw [← sum_range_succ_eq_sum_Icc]
  calc
    _ ≤ ∑ n ∈ Finset.range N, (W * frequencyDecayKernel M n) * ‖f (n + 1)‖ := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hweight n (Finset.mem_range.mp hn)) (norm_nonneg _)
    _ = W * ∑ n ∈ Finset.range N, frequencyDecayKernel M n * ‖f (n + 1)‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ W * (2 * D) := mul_le_mul_of_nonneg_left
      (sum_frequencyDecayKernel_mul_le hM (fun n => ‖f (n + 1)‖) N D hD hprefix) hW
    _ = _ := by ring

lemma physical_frequency_decay_le_kernel {σ : ℝ} {M : ℕ} (hσ : 0 < σ)
    (hM : 0 < M) (hlo : 1 ≤ σ * M) (hhi : σ * M ≤ 2) (n : ℕ) :
    σ / (1 + σ * (n + 1)) ^ 2 ≤ 2 * frequencyDecayKernel M n := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hden : (M : ℝ) + n + 1 ≤ M * (1 + σ * (n + 1)) := by
    have hh := mul_le_mul_of_nonneg_right hlo (show (0 : ℝ) ≤ n + 1 by positivity)
    nlinarith
  have hsquare := pow_le_pow_left₀ (show (0 : ℝ) ≤ M + n + 1 by positivity) hden 2
  have hnum : σ * ((M : ℝ) + n + 1) ^ 2 ≤ 2 * M * (1 + σ * (n + 1)) ^ 2 := by
    calc
      _ ≤ σ * (M * (1 + σ * (n + 1))) ^ 2 := mul_le_mul_of_nonneg_left hsquare hσ.le
      _ = (σ * M) * (M * (1 + σ * (n + 1)) ^ 2) := by ring
      _ ≤ 2 * (M * (1 + σ * (n + 1)) ^ 2) :=
        mul_le_mul_of_nonneg_right hhi (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (2 * M) / ((M : ℝ) + n + 1) ^ 2 :=
      (div_le_div_iff₀ (by positivity) (by positivity)).mpr hnum
    _ ≤ (2 * M) / (((M : ℝ) + n) * ((M : ℝ) + n + 1)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    _ = _ := by unfold frequencyDecayKernel; ring

end Erdos587
