import ErdosProblems.Erdos321.UniformKernel
import ErdosProblems.Erdos321.UpperAnalyticRecurrence

namespace Erdos321

noncomputable def normalizedExtremal (N : ℕ) : ℝ :=
  Real.log N / N * extremalSize N

noncomputable def normalizedEntropy (N : ℕ) : ℝ :=
  Real.log N / N * harmonicEntropy N

noncomputable def weightedCofactorSum (f : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, f t / ((t : ℝ) * (t + 1))

noncomputable def normalizedBadError (N T : ℕ) : ℝ :=
  Real.log N / N * ((3 : ℝ) ^ T * T ^ 2 * (T + 1))

noncomputable def normalizedSmoothError (N Q : ℕ) : ℝ :=
  Real.log N / N *
    (Real.log (N + 1) +
      (Real.log 4 * Q + 4 * Real.sqrt Q * Real.log Q +
        2 * Real.sqrt N * Real.log N))

/-- Normalized lower recurrence with the common ideal kernel. -/
theorem exists_normalized_lower_recurrence_constant :
    ∃ C ≥ 0, ∀ {N T : ℕ}, 1 ≤ T → T < N / (T + 1) →
      2 ≤ N / (T + 1) → (T : ℝ) ≤ Real.log N →
      1 ≤ Real.log N → uniformKernelError C N ≤ 1 / 4 →
      (1 - 2 * uniformKernelError C N) *
          weightedCofactorSum (fun t => (extremalSize t : ℝ)) T ≤
        normalizedExtremal N + normalizedBadError N T := by
  obtain ⟨C, hC, hRec⟩ := exists_analytic_lower_recurrence_constant
  refine ⟨C, hC, ?_⟩
  intro N T hT hcut hEnd hTlog hLog hε
  have hN : 1 < N := by
    by_contra hn
    interval_cases N <;> norm_num at hLog
  have hRaw := hRec hT hcut hEnd
  have hKernelSum :
      (1 - 2 * uniformKernelError C N) *
          ((N : ℝ) / Real.log N) *
          weightedCofactorSum (fun t => (extremalSize t : ℝ)) T ≤
        ∑ t ∈ Finset.Icc 1 T,
          quotientLowerCoefficient C N t * extremalSize t := by
    rw [weightedCofactorSum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    have htData := Finset.mem_Icc.mp ht
    have htt : (t : ℝ) ≤ T := by exact_mod_cast htData.2
    have htlog : (t : ℝ) ≤ Real.log N := htt.trans hTlog
    have hNt : 2 * (t + 1) ≤ N := by
      have hmul : 2 * (T + 1) ≤ N :=
        (Nat.le_div_iff_mul_le (by omega : 0 < T + 1)).mp hEnd
      exact (Nat.mul_le_mul_left 2 (Nat.add_le_add_right htData.2 1)).trans hmul
    have hs := quotientCoefficient_uniform_kernel_sandwich hC htData.1
      htlog hNt hN hLog hε
    have hR : 0 ≤ (extremalSize t : ℝ) := by positivity
    have hterm := mul_le_mul_of_nonneg_right hs.1 hR
    have hlog0 : Real.log (N : ℝ) ≠ 0 := by linarith
    have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
    have ht10 : (t : ℝ) + 1 ≠ 0 := by positivity
    convert hterm using 1
    all_goals
      dsimp [quotientMainKernel]
      field_simp [hlog0, ht0, ht10]
  have hCombined := hKernelSum.trans hRaw
  have hScale : 0 ≤ Real.log N / N := by positivity
  have hScaled := mul_le_mul_of_nonneg_left hCombined hScale
  dsimp [normalizedExtremal, normalizedBadError]
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hlog0 : Real.log (N : ℝ) ≠ 0 := by linarith
  calc
    (1 - 2 * uniformKernelError C N) *
        weightedCofactorSum (fun t => (extremalSize t : ℝ)) T =
      Real.log N / N *
        ((1 - 2 * uniformKernelError C N) * (N / Real.log N) *
          weightedCofactorSum (fun t => (extremalSize t : ℝ)) T) := by
        field_simp [hN0, hlog0]
    _ ≤ Real.log N / N *
        ((extremalSize N : ℝ) + (3 : ℝ) ^ T * T ^ 2 * (T + 1)) := hScaled
    _ = Real.log N / N * extremalSize N +
        Real.log N / N * ((3 : ℝ) ^ T * T ^ 2 * (T + 1)) := by ring

/-- Normalized upper recurrence with the same ideal kernel. -/
theorem exists_normalized_upper_recurrence_constant :
    ∃ C ≥ 0, ∀ {N Q : ℕ}, N < (Q + 1) * (Q + 1) →
      Q ≤ N → 1 ≤ Q → 1 ≤ N →
      2 ≤ N / (N / (Q + 1) + 1) →
      ((N / (Q + 1) : ℕ) : ℝ) ≤ Real.log N →
      1 ≤ Real.log N → uniformKernelError C N ≤ 1 / 4 →
      normalizedEntropy N ≤ normalizedSmoothError N Q +
        (1 + 4 * uniformKernelError C N) *
          weightedCofactorSum harmonicEntropy (N / (Q + 1)) := by
  obtain ⟨C, hC, hRec⟩ := exists_commonKernel_upper_recurrence_constant
  refine ⟨C, hC, ?_⟩
  intro N Q hUnique hQN hQ hN hEnd hUlog hLog hε
  have hNgt : 1 < N := by
    by_contra hn
    interval_cases N
    all_goals norm_num at hLog
  have hRaw := hRec hUnique hQN hQ hN hEnd
  let U := N / (Q + 1)
  have hKernelSum :
      (∑ t ∈ Finset.Icc 1 U,
        quotientUpperCoefficient C N t * harmonicEntropy t) ≤
      (1 + 4 * uniformKernelError C N) *
        ((N : ℝ) / Real.log N) * weightedCofactorSum harmonicEntropy U := by
    rw [weightedCofactorSum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    have htData := Finset.mem_Icc.mp ht
    have htt : (t : ℝ) ≤ U := by exact_mod_cast htData.2
    have htlog : (t : ℝ) ≤ Real.log N := htt.trans hUlog
    have hden : N / (U + 1) ≤ N / (t + 1) :=
      Nat.div_le_div_left (Nat.add_le_add_right htData.2 1) (by omega)
    have hNt : 2 * (t + 1) ≤ N :=
      (Nat.le_div_iff_mul_le (by omega : 0 < t + 1)).mp (hEnd.trans hden)
    have hs := quotientCoefficient_uniform_kernel_sandwich hC htData.1
      htlog hNt hNgt hLog hε
    have hH := harmonicEntropy_nonneg t
    have hterm := mul_le_mul_of_nonneg_right hs.2 hH
    have hlog0 : Real.log (N : ℝ) ≠ 0 := by linarith
    have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
    have ht10 : (t : ℝ) + 1 ≠ 0 := by positivity
    convert hterm using 1
    all_goals
      dsimp [quotientMainKernel]
      field_simp [hlog0, ht0, ht10]
  have hCombined : harmonicEntropy N ≤
      (Real.log (N + 1) +
        (Real.log 4 * Q + 4 * Real.sqrt Q * Real.log Q +
          2 * Real.sqrt N * Real.log N)) +
        (1 + 4 * uniformKernelError C N) *
          ((N : ℝ) / Real.log N) * weightedCofactorSum harmonicEntropy U := by
    linarith
  dsimp [U] at hCombined
  have hScale : 0 ≤ Real.log N / N := by positivity
  have hScaled := mul_le_mul_of_nonneg_left hCombined hScale
  dsimp [normalizedEntropy, normalizedSmoothError]
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hlog0 : Real.log (N : ℝ) ≠ 0 := by linarith
  calc
    Real.log N / N * harmonicEntropy N ≤
        Real.log N / N *
          ((Real.log (N + 1) +
            (Real.log 4 * Q + 4 * Real.sqrt Q * Real.log Q +
              2 * Real.sqrt N * Real.log N)) +
            (1 + 4 * uniformKernelError C N) *
              (N / Real.log N) *
                weightedCofactorSum harmonicEntropy (N / (Q + 1))) := hScaled
    _ = Real.log N / N *
          (Real.log (N + 1) +
            (Real.log 4 * Q + 4 * Real.sqrt Q * Real.log Q +
              2 * Real.sqrt N * Real.log N)) +
        (1 + 4 * uniformKernelError C N) *
          weightedCofactorSum harmonicEntropy (N / (Q + 1)) := by
      field_simp [hN0, hlog0]

end Erdos321
