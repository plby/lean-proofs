import ErdosProblems.Erdos321.NeumannModel

namespace Erdos321

private theorem truncatedLogOperator_nonneg
    {A T : ℕ} (hA : 2 ≤ A) {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    0 ≤ truncatedLogOperator A f T := by
  dsimp [truncatedLogOperator]
  apply Finset.sum_nonneg
  intro t ht
  have htA := (Finset.mem_Icc.mp ht).1
  have hlog : 0 < Real.log (t : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < t by omega))
  exact div_nonneg (hf t) (mul_nonneg (by positivity) hlog.le)

private theorem truncatedLogOperator_mono_fun
    {A T : ℕ} {f g : ℕ → ℝ}
    (hfg : ∀ t ∈ Finset.Icc A T, f t ≤ g t) :
    truncatedLogOperator A f T ≤ truncatedLogOperator A g T := by
  dsimp [truncatedLogOperator]
  apply Finset.sum_le_sum
  intro t ht
  by_cases ht1 : t ≤ 1
  · interval_cases t <;> simp
  · have hden : 0 < ((t : ℝ) + 1) * Real.log t := by
      have hlog : 0 < Real.log (t : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < t by omega))
      positivity
    exact (div_le_div_iff_of_pos_right hden).2 (hfg t ht)

private theorem truncatedLogOperator_mono_endpoint
    {A T U : ℕ} (hTU : T ≤ U) (hA : 2 ≤ A)
    {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    truncatedLogOperator A f T ≤ truncatedLogOperator A f U := by
  dsimp [truncatedLogOperator]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    have hm := Finset.mem_Icc.mp ht
    exact Finset.mem_Icc.mpr ⟨hm.1, hm.2.trans hTU⟩
  · intro t ht hnot
    have htA := (Finset.mem_Icc.mp ht).1
    have hlog : 0 < Real.log (t : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < t by omega))
    exact div_nonneg (hf t) (mul_nonneg (by positivity) hlog.le)

private theorem truncatedLogOperator_anti_threshold
    {A B T : ℕ} (hAB : A ≤ B) {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    truncatedLogOperator B f T ≤ truncatedLogOperator A f T := by
  dsimp [truncatedLogOperator]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    have hm := Finset.mem_Icc.mp ht
    exact Finset.mem_Icc.mpr ⟨hAB.trans hm.1, hm.2⟩
  · intro t ht hnot
    have htA := (Finset.mem_Icc.mp ht).1
    by_cases h : t ≤ 1
    · interval_cases t <;> simp
    · have hlog : 0 < Real.log (t : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < t by omega))
      exact div_nonneg (hf t) (mul_nonneg (by positivity) hlog.le)

private theorem truncatedLogOperator_split
    {A B T : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) :
    truncatedLogOperator A f T ≤
      truncatedLogOperator A f (B - 1) + truncatedLogOperator B f T := by
  let low := Finset.Icc A (B - 1)
  let high := Finset.Icc B T
  have hdisj : Disjoint low high := by
    apply Finset.disjoint_left.mpr
    intro t hl hh
    have hlm := Finset.mem_Icc.mp hl
    have hhm := Finset.mem_Icc.mp hh
    omega
  have hsubset : Finset.Icc A T ⊆ low ∪ high := by
    intro t ht
    have hm := Finset.mem_Icc.mp ht
    by_cases h : t < B
    · exact Finset.mem_union_left high (Finset.mem_Icc.mpr ⟨hm.1, by omega⟩)
    · exact Finset.mem_union_right low (Finset.mem_Icc.mpr ⟨by omega, hm.2⟩)
  have hnonneg : ∀ t ∈ low ∪ high,
      0 ≤ f t / ((t + 1) * Real.log t) := by
    intro t ht
    have htA : A ≤ t := by
      rcases Finset.mem_union.mp ht with ht | ht
      · exact (Finset.mem_Icc.mp ht).1
      · exact hAB.trans (Finset.mem_Icc.mp ht).1
    have hlog : 0 < Real.log (t : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < t by omega))
    exact div_nonneg (hf t) (mul_nonneg (by positivity) hlog.le)
  dsimp [truncatedLogOperator]
  calc
    (∑ t ∈ Finset.Icc A T, f t / ((t + 1) * Real.log t)) ≤
        ∑ t ∈ low ∪ high, f t / ((t + 1) * Real.log t) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun t ht hnot => hnonneg t ht)
    _ = (∑ t ∈ low, f t / ((t + 1) * Real.log t)) +
        ∑ t ∈ high, f t / ((t + 1) * Real.log t) :=
      Finset.sum_union hdisj

/-- Raising the stopping threshold can only decrease the ideal model. -/
theorem adaptiveNeumannModel_anti_threshold
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) (n : ℕ) :
    adaptiveNeumannModel B n ≤ adaptiveNeumannModel A n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hnB : n < B
      · rw [adaptiveNeumannModel_eq_one hnB]
        exact one_le_adaptiveNeumannModel hA n
      · have hBn : B ≤ n := by omega
        have hAn : A ≤ n := hAB.trans hBn
        have hnpos : 0 < n := by omega
        rw [adaptiveNeumannModel_eq_safe hBn hnpos,
          adaptiveNeumannModel_eq_safe hAn hnpos]
        have hfun : truncatedLogOperator B (adaptiveNeumannModel B)
            (safeAdaptiveEndpoint n) ≤
            truncatedLogOperator B (adaptiveNeumannModel A)
              (safeAdaptiveEndpoint n) := by
          apply truncatedLogOperator_mono_fun
          intro t ht
          have htupper := (Finset.mem_Icc.mp ht).2
          have hs : safeAdaptiveEndpoint n ≤ n - 1 := min_le_right _ _
          exact ih t (by omega)
        have hop := hfun.trans (truncatedLogOperator_anti_threshold hAB
          (adaptiveNeumannModel_nonneg hA))
        linarith

/-- Models with any two fixed terminal thresholds differ by at most a fixed
multiplicative constant. -/
theorem adaptiveNeumannModel_threshold_comparable
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n,
      adaptiveNeumannModel A n ≤ K * adaptiveNeumannModel B n := by
  let S : ℝ := 1 + truncatedLogOperator A (adaptiveNeumannModel A) (B - 1)
  have hS1 : 1 ≤ S := by
    dsimp [S]
    exact le_add_of_nonneg_right
      (truncatedLogOperator_nonneg hA (adaptiveNeumannModel_nonneg hA))
  refine ⟨S, hS1, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hnA : n < A
      · rw [adaptiveNeumannModel_eq_one hnA]
        have hMB := one_le_adaptiveNeumannModel (hA.trans hAB) n
        nlinarith [mul_le_mul_of_nonneg_left hMB (show 0 ≤ S by linarith)]
      · have hAn : A ≤ n := by omega
        have hnpos : 0 < n := by omega
        rw [adaptiveNeumannModel_eq_safe hAn hnpos]
        by_cases hnB : n < B
        · rw [adaptiveNeumannModel_eq_one hnB]
          have hsub : truncatedLogOperator A (adaptiveNeumannModel A)
              (safeAdaptiveEndpoint n) ≤
              truncatedLogOperator A (adaptiveNeumannModel A) (B - 1) := by
            apply truncatedLogOperator_mono_endpoint _ hA
              (adaptiveNeumannModel_nonneg hA)
            have hs : safeAdaptiveEndpoint n ≤ n - 1 := min_le_right _ _
            omega
          dsimp [S]
          linarith
        · have hBn : B ≤ n := by omega
          rw [adaptiveNeumannModel_eq_safe hBn hnpos]
          have hsplit := truncatedLogOperator_split hA hAB
            (adaptiveNeumannModel_nonneg hA) (T := safeAdaptiveEndpoint n)
          have hhigh : truncatedLogOperator B (adaptiveNeumannModel A)
              (safeAdaptiveEndpoint n) ≤
              S * truncatedLogOperator B (adaptiveNeumannModel B)
                (safeAdaptiveEndpoint n) := by
            dsimp [truncatedLogOperator]
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum
            intro t ht
            have htupper := (Finset.mem_Icc.mp ht).2
            have hs : safeAdaptiveEndpoint n ≤ n - 1 := min_le_right _ _
            have hit := ih t (by omega)
            have hden : 0 < ((t : ℝ) + 1) * Real.log t := by
              have htB := (Finset.mem_Icc.mp ht).1
              have hlog : 0 < Real.log (t : ℝ) :=
                Real.log_pos (by exact_mod_cast (show 1 < t by omega))
              positivity
            have hdiv := (div_le_div_iff_of_pos_right hden).2 hit
            convert hdiv using 1 <;> ring
          dsimp [S] at hsplit ⊢
          nlinarith

end Erdos321
