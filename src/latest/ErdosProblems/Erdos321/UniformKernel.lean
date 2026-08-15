import ErdosProblems.Erdos321.QuotientKernel

namespace Erdos321

/-- A class-independent error valid throughout the full logarithmic cofactor
range. -/
noncomputable def uniformKernelError (C : ℝ) (N : ℕ) : ℝ :=
  let L := Real.log N
  L * (L + 1) / N + 16 * C / L + Real.log (4 * L) / L

/-- The pointwise error of F-047 is bounded uniformly for `t≤log N`. -/
theorem quotientKernelError_le_uniform
    {C : ℝ} (hC : 0 ≤ C) {N t : ℕ}
    (hL : 1 ≤ Real.log N) (ht : (t : ℝ) ≤ Real.log N) :
    quotientKernelError C N t ≤ uniformKernelError C N := by
  let L := Real.log N
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have ht1 : (t : ℝ) + 1 ≤ L + 1 := by linarith
  have hL1 : L + 1 ≤ 2 * L := by linarith
  have hNpos : (0 : ℝ) < N := by
    by_contra h
    have : (N : ℝ) = 0 := le_antisymm (le_of_not_gt h) (by positivity)
    have : N = 0 := by exact_mod_cast this
    subst N
    norm_num at hL
  have hFirst : (t : ℝ) * (t + 1) / N ≤ L * (L + 1) / N := by
    apply div_le_div_of_nonneg_right _ hNpos.le
    exact mul_le_mul ht ht1 (by positivity) (by linarith)
  have hSecond : 8 * C * (t + 1) / L ^ 2 ≤ 16 * C / L := by
    rw [div_le_iff₀ (sq_pos_of_pos hLpos)]
    have hEq : 16 * C / L * L ^ 2 = 16 * C * L := by
      field_simp
    rw [hEq]
    have h8C : 0 ≤ 8 * C := mul_nonneg (by norm_num) hC
    have hmul := mul_le_mul_of_nonneg_left (ht1.trans hL1) h8C
    nlinarith
  have hArg : 2 * ((t : ℝ) + 1) ≤ 4 * L := by nlinarith
  have hThird : Real.log (2 * ((t : ℝ) + 1)) / L ≤
      Real.log (4 * L) / L := by
    apply div_le_div_of_nonneg_right _ hLpos.le
    apply Real.strictMonoOn_log.monotoneOn
    · simp only [Set.mem_Ioi]
      positivity
    · simp only [Set.mem_Ioi]
      positivity
    · exact hArg
  dsimp [quotientKernelError, uniformKernelError, L] at *
  linarith

/-- Uniform ideal-kernel comparison on the logarithmic cofactor range. -/
theorem quotientCoefficient_uniform_kernel_sandwich
    {C : ℝ} (hC : 0 ≤ C) {N t : ℕ}
    (ht1 : 1 ≤ t) (htLog : (t : ℝ) ≤ Real.log N)
    (hNt : 2 * (t + 1) ≤ N) (hN : 1 < N)
    (hL : 1 ≤ Real.log N)
    (hε : uniformKernelError C N ≤ 1 / 4) :
    (1 - 2 * uniformKernelError C N) * quotientMainKernel N t ≤
        quotientLowerCoefficient C N t ∧
      quotientUpperCoefficient C N t ≤
        (1 + 4 * uniformKernelError C N) * quotientMainKernel N t := by
  have hηε := quotientKernelError_le_uniform hC hL htLog
  have hη := hηε.trans hε
  have hs := quotientCoefficient_kernel_sandwich hC ht1 hNt hN hη
  have hK : 0 ≤ quotientMainKernel N t := by
    dsimp [quotientMainKernel]
    positivity
  constructor
  · calc
      (1 - 2 * uniformKernelError C N) * quotientMainKernel N t ≤
          (1 - 2 * quotientKernelError C N t) * quotientMainKernel N t := by
        apply mul_le_mul_of_nonneg_right _ hK
        linarith
      _ ≤ quotientLowerCoefficient C N t := hs.1
  · calc
      quotientUpperCoefficient C N t ≤
          (1 + 4 * quotientKernelError C N t) * quotientMainKernel N t := hs.2
      _ ≤ (1 + 4 * uniformKernelError C N) * quotientMainKernel N t := by
        apply mul_le_mul_of_nonneg_right _ hK
        linarith

end Erdos321
