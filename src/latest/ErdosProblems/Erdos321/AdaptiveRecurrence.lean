import ErdosProblems.Erdos321.AdaptiveSources

namespace Erdos321

open Filter
open scoped Topology

/-- The normalized lower recurrence, specialized to the exact common adaptive
endpoint and rewritten as the discrete logarithmic operator. -/
theorem exists_adaptive_lower_operator_recurrence :
    ∃ C ≥ 0, ∀ᶠ N : ℕ in atTop,
      (1 - 2 * uniformKernelError C N) *
          (1 / 2 + discreteLogOperator normalizedExtremal
            (adaptiveEndpoint N)) ≤
        normalizedExtremal N +
          normalizedBadError N (adaptiveEndpoint N) := by
  obtain ⟨C, hC, hrec⟩ := exists_normalized_lower_recurrence_constant
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_adaptiveCutoffData,
    eventually_uniformKernelError_le_quarter C] with N hdata hε
  have hT1 : 1 ≤ adaptiveEndpoint N :=
    (show 1 ≤ 2 by norm_num).trans hdata.endpoint_ge_two
  have hmain := hrec hT1
    hdata.lower_disjoint hdata.upper_endpoint hdata.endpoint_le_log
    hdata.log_ge_one hε
  rw [weightedCofactorSum_extremal_eq hT1] at hmain
  exact hmain

/-- The normalized entropy upper recurrence, specialized to the same adaptive
endpoint and rewritten as the same discrete logarithmic operator. -/
theorem exists_adaptive_upper_operator_recurrence :
    ∃ C ≥ 0, ∀ᶠ N : ℕ in atTop,
      normalizedEntropy N ≤
        normalizedSmoothError N (adaptiveSmoothCutoff N) +
          (1 + 4 * uniformKernelError C N) *
            (Real.log 2 / 2 +
              discreteLogOperator normalizedEntropy (adaptiveEndpoint N)) := by
  obtain ⟨C, hC, hrec⟩ := exists_normalized_upper_recurrence_constant
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_adaptiveCutoffData,
    eventually_uniformKernelError_le_quarter C] with N hdata hε
  have hN : 1 ≤ N := by
    have := hdata.logScale_sq_le
    have hL := hdata.logScale_ge_four
    nlinarith
  have hEnd :
      2 ≤ N / (N / (adaptiveSmoothCutoff N + 1) + 1) := by
    simpa [adaptiveEndpoint] using hdata.upper_endpoint
  have hUnique :
      N < (adaptiveSmoothCutoff N + 1) *
        (adaptiveSmoothCutoff N + 1) := by
    simpa [pow_two] using hdata.entropy_unique
  have hmain := hrec hUnique hdata.smooth_le
    hdata.smooth_ge_one hN hEnd hdata.endpoint_le_log
    hdata.log_ge_one hε
  rw [weightedCofactorSum_entropy_eq
    (show 1 ≤ N / (adaptiveSmoothCutoff N + 1) by
      simpa [adaptiveEndpoint] using
        ((show 1 ≤ 2 by norm_num).trans hdata.endpoint_ge_two))] at hmain
  simpa [adaptiveEndpoint] using hmain

/-- The lower recurrence has a uniformly positive source after moving its
vanishing error to the left. -/
theorem exists_adaptive_lower_positive_source :
    ∃ C ≥ 0, ∀ᶠ N : ℕ in atTop,
      1 / 4 + (1 - 2 * uniformKernelError C N) *
          discreteLogOperator normalizedExtremal (adaptiveEndpoint N) ≤
        normalizedExtremal N := by
  obtain ⟨C, hC, hrec⟩ := exists_adaptive_lower_operator_recurrence
  have hbad : ∀ᶠ N : ℕ in atTop,
      normalizedBadError N (adaptiveEndpoint N) ≤ 1 / 8 :=
    tendsto_adaptive_normalizedBadError.eventually
      (Iic_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num))
  have hε : ∀ᶠ N : ℕ in atTop, uniformKernelError C N ≤ 1 / 8 :=
    (tendsto_uniformKernelError C).eventually
      (Iic_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num))
  refine ⟨C, hC, ?_⟩
  filter_upwards [hrec, hbad, hε] with N hrecN hbadN hεN
  have hD : 0 ≤ discreteLogOperator normalizedExtremal (adaptiveEndpoint N) := by
    dsimp [discreteLogOperator]
    apply Finset.sum_nonneg
    intro t ht
    have ht2 := (Finset.mem_Icc.mp ht).1
    have hlog : 0 < Real.log (t : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < t by omega))
    dsimp [normalizedExtremal]
    positivity
  nlinarith

/-- The upper recurrence has an absolute inhomogeneous source bound. -/
theorem exists_adaptive_upper_bounded_source :
    ∃ C ≥ 0, ∀ᶠ N : ℕ in atTop,
      normalizedEntropy N ≤ 102 +
        (1 + 4 * uniformKernelError C N) *
          discreteLogOperator normalizedEntropy (adaptiveEndpoint N) := by
  obtain ⟨C, hC, hrec⟩ := exists_adaptive_upper_operator_recurrence
  refine ⟨C, hC, ?_⟩
  filter_upwards [hrec, eventually_adaptive_normalizedSmoothError_le,
    eventually_uniformKernelError_le_quarter C,
    eventually_adaptiveCutoffData] with N hrecN hsmooth hε hdata
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at this ⊢
    exact this
  have hfactor : 1 + 4 * uniformKernelError C N ≤ 2 := by linarith
  have hfactor0 : 0 ≤ 1 + 4 * uniformKernelError C N := by
    have hε0 : 0 ≤ uniformKernelError C N := by
      have hLpos : 0 < Real.log N := lt_of_lt_of_le zero_lt_one hdata.log_ge_one
      have hNpos : (0 : ℝ) < N := by
        have := hdata.logScale_sq_le
        have hL := hdata.logScale_ge_four
        exact_mod_cast (show 0 < N by nlinarith)
      have hlogArg : 0 ≤ Real.log (4 * Real.log N) :=
        Real.log_nonneg (by nlinarith [hdata.log_ge_one])
      dsimp [uniformKernelError]
      positivity
    linarith
  have hseed :
      (1 + 4 * uniformKernelError C N) * (Real.log 2 / 2) ≤ 1 := by
    nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]
  nlinarith

end Erdos321
