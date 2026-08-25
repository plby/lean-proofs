import Util.Bernays.LogWeightRemoval

/-!
# Quantitative error control for the logarithmic recurrence

A linear asymptotic for the logarithmic kernel gives an error bounded by
`ε*N*H(N) + O(N)`, where `H` is the reciprocal partial sum. This turns the
half-power reciprocal asymptotic into the ordinary Bernays counting scale.
-/

open Filter Topology Real

namespace Bernays

theorem reciprocalSum_eq_sum_Icc (a : ℕ → ℝ) (N : ℕ) :
    reciprocalSum a N = ∑ n ∈ Finset.Icc 1 N, a n / (n : ℝ) := by
  apply Finset.sum_bij (fun n _ => n + 1)
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨by omega, by have := Finset.mem_range.mp hn; omega⟩
  · intro n _ m _ hnm
    omega
  · intro n hn
    refine ⟨n - 1, Finset.mem_range.mpr ?_, ?_⟩ <;>
      have := Finset.mem_Icc.mp hn <;> omega
  · intro n _
    rfl

theorem ordinarySum_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (N : ℕ) :
    0 ≤ ordinarySum a N := Finset.sum_nonneg fun n _ => ha n

theorem ordinarySum_le {a : ℕ → ℝ} (ha : ∀ n, a n ≤ 1) (N : ℕ) :
    ordinarySum a N ≤ N := by
  calc
    ordinarySum a N ≤ ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) := Finset.sum_le_sum fun n _ => ha n
    _ = N := by simp

theorem kernel_global_linear_error {K : ℕ → ℝ} {κ : ℝ}
    (hK : Tendsto (fun N : ℕ => K N / (N : ℝ)) atTop (𝓝 κ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, |K N - κ * N| ≤ ε * N + C := by
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hK ε hε
  let M : ℕ := max N₀ 1
  let C : ℝ := ∑ n ∈ Finset.range M, |K n - κ * n|
  have hC : 0 ≤ C := Finset.sum_nonneg fun n _ => abs_nonneg _
  refine ⟨C, hC, ?_⟩
  intro N
  by_cases hN : N < M
  · have hterm : |K N - κ * N| ≤ C :=
      Finset.single_le_sum (f := fun n : ℕ => |K n - κ * n|)
        (fun n _ => abs_nonneg _) (Finset.mem_range.mpr hN)
    exact hterm.trans (le_add_of_nonneg_left (mul_nonneg hε.le (Nat.cast_nonneg N)))
  · have hNM : M ≤ N := Nat.le_of_not_gt hN
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ((le_max_right N₀ 1).trans hNM))
    have hr := hN₀ N ((le_max_left N₀ 1).trans hNM)
    rw [Real.dist_eq] at hr
    have heq : K N - κ * N = (K N / (N : ℝ) - κ) * N := by field_simp
    rw [heq, abs_mul, abs_of_pos hNpos]
    exact (mul_le_mul_of_nonneg_right hr.le hNpos.le).trans (le_add_of_nonneg_right hC)

theorem kernel_quotient_error {K : ℕ → ℝ} {κ ε C : ℝ}
    (hε : 0 ≤ ε) (hK : ∀ N : ℕ, |K N - κ * N| ≤ ε * N + C)
    (N : ℕ) {m : ℕ} (hm : 0 < m) :
    |K (N / m) - κ * ((N : ℝ) / m)| ≤ ε * ((N : ℝ) / m) + C + |κ| := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hq₀ : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := Nat.cast_div_le
  have hq₁ : (N : ℝ) / m < ((N / m : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ hmR).mpr
    have h := Nat.lt_mul_div_succ N hm
    exact_mod_cast (by simpa only [Nat.mul_comm] using h)
  have hdist : |((N / m : ℕ) : ℝ) - (N : ℝ) / m| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hq₀)]
    linarith
  have hκ : |κ * ((N / m : ℕ) : ℝ) - κ * ((N : ℝ) / m)| ≤ |κ| := by
    rw [← mul_sub, abs_mul]
    exact (mul_le_mul_of_nonneg_left hdist (abs_nonneg κ)).trans_eq (mul_one _)
  calc
    _ ≤ |K (N / m) - κ * ((N / m : ℕ) : ℝ)| +
        |κ * ((N / m : ℕ) : ℝ) - κ * ((N : ℝ) / m)| := abs_sub_le _ _ _
    _ ≤ (ε * ((N / m : ℕ) : ℝ) + C) + |κ| := add_le_add (hK _) hκ
    _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left hq₀ hε]

theorem logarithmicRecurrence_error {a : ℕ → ℝ} {K : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1)
    (hrec : ∀ N, logarithmicSum a N = ∑ m ∈ Finset.Icc 1 N, a m * K (N / m))
    {κ ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hK : ∀ N : ℕ, |K N - κ * N| ≤ ε * N + C) (N : ℕ) :
    |logarithmicSum a N - κ * N * reciprocalSum a N| ≤
      ε * N * reciprocalSum a N + (C + |κ|) * N := by
  have heq : logarithmicSum a N - κ * N * reciprocalSum a N =
      ∑ m ∈ Finset.Icc 1 N, a m * (K (N / m) - κ * ((N : ℝ) / m)) := by
    rw [hrec, reciprocalSum_eq_sum_Icc, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [heq]
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 N, |a m * (K (N / m) - κ * ((N : ℝ) / m))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 N, a m * (ε * ((N : ℝ) / m) + C + |κ|) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [abs_mul, abs_of_nonneg (ha m)]
      exact mul_le_mul_of_nonneg_left
        (kernel_quotient_error hε hK N (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1)) (ha m)
    _ = ε * N * reciprocalSum a N + (C + |κ|) * ordinarySum a N := by
      rw [reciprocalSum_eq_sum_Icc, ordinarySum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ ≤ _ := by
      linarith [mul_le_mul_of_nonneg_left (ordinarySum_le ha₁ N) (add_nonneg hC (abs_nonneg κ))]

theorem logarithmicRecurrence_asymptotic {a : ℕ → ℝ} {K : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1)
    (hrec : ∀ N, logarithmicSum a N = ∑ m ∈ Finset.Icc 1 N, a m * K (N / m))
    {κ H : ℝ} (hH₀ : 0 ≤ H)
    (hK : Tendsto (fun N : ℕ => K N / (N : ℝ)) atTop (𝓝 κ))
    (hH : Tendsto (fun N : ℕ => reciprocalSum a N / sqrt (log (N : ℝ))) atTop (𝓝 H)) :
    Tendsto (fun N : ℕ => logarithmicSum a N / ((N : ℝ) * sqrt (log (N : ℝ))))
      atTop (𝓝 (κ * H)) := by
  let D : ℕ → ℝ := fun N =>
    (logarithmicSum a N - κ * N * reciprocalSum a N) /
      ((N : ℝ) * sqrt (log (N : ℝ)))
  have hden : Tendsto (fun N : ℕ => sqrt (log (N : ℝ))) atTop atTop :=
    tendsto_sqrt_atTop.comp (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hD : Tendsto D atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let δ : ℝ := ε / (4 * (H + 1))
    have hHp : 0 < H + 1 := by linarith
    have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hHp)
    have hδeq : δ * (H + 1) = ε / 4 := by
      dsimp only [δ]
      rw [div_mul_eq_div_div, div_mul_cancel₀ _ hHp.ne']
    obtain ⟨C, hC, hKC⟩ := kernel_global_linear_error hK hδ
    have htail : Tendsto (fun N : ℕ => (C + |κ|) / sqrt (log (N : ℝ))) atTop (𝓝 0) := by
      simpa only [Function.comp_def, mul_zero, ← div_eq_mul_inv] using
        (tendsto_inv_atTop_zero.comp hden).const_mul (C + |κ|)
    filter_upwards [hH.eventually (gt_mem_nhds (lt_add_one H)),
      htail.eventually (gt_mem_nhds (half_pos hε)), eventually_ge_atTop 2] with N hHN htailN hN
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hLp : 0 < sqrt (log (N : ℝ)) := sqrt_pos.mpr (log_pos (by exact_mod_cast hN))
    have herror := logarithmicRecurrence_error ha ha₁ hrec hδ.le hC hKC N
    have hdiv := div_le_div_of_nonneg_right herror (mul_pos hNp hLp).le
    have hsplit : (δ * N * reciprocalSum a N + (C + |κ|) * N) /
        ((N : ℝ) * sqrt (log (N : ℝ))) =
        δ * (reciprocalSum a N / sqrt (log (N : ℝ))) + (C + |κ|) / sqrt (log (N : ℝ)) := by
      field_simp
    rw [hsplit] at hdiv
    rw [Real.dist_eq, sub_zero]
    change |(logarithmicSum a N - κ * N * reciprocalSum a N) /
      ((N : ℝ) * sqrt (log (N : ℝ)))| < ε
    rw [abs_div, abs_of_pos (mul_pos hNp hLp)]
    have hmul := mul_lt_mul_of_pos_left hHN hδ
    linarith
  have hsum := (hH.const_mul κ).add hD
  rw [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLp : 0 < sqrt (log (N : ℝ)) := sqrt_pos.mpr (log_pos (by exact_mod_cast hN))
  change κ * (reciprocalSum a N / sqrt (log (N : ℝ))) + D N = _
  dsimp only [D]
  field_simp
  ring

theorem ordinarySum_asymptotic_of_recurrence {a : ℕ → ℝ} {K : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1)
    (hrec : ∀ N, logarithmicSum a N = ∑ m ∈ Finset.Icc 1 N, a m * K (N / m))
    {κ H : ℝ} (hH₀ : 0 ≤ H)
    (hK : Tendsto (fun N : ℕ => K N / (N : ℝ)) atTop (𝓝 κ))
    (hH : Tendsto (fun N : ℕ => reciprocalSum a N / sqrt (log (N : ℝ))) atTop (𝓝 H)) :
    Tendsto (fun N : ℕ => ordinarySum a N / ((N : ℝ) / sqrt (log (N : ℝ))))
      atTop (𝓝 (κ * H)) :=
  ordinarySum_asymptotic_of_logarithmicSum ha ha₁
    (logarithmicRecurrence_asymptotic ha ha₁ hrec hH₀ hK hH)

end Bernays
