import ErdosProblems.Erdos321.ErrorProducts

namespace Erdos321

/-- The discrete logarithmic operator restricted to recursion indices at least
`A`. -/
noncomputable def truncatedLogOperator
    (A : ℕ) (f : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc A T, f t / ((t + 1) * Real.log t)

/-- A total endpoint forced below `n`, agreeing with `adaptiveEndpoint n` on
F-053's eventual cutoff range. -/
noncomputable def safeAdaptiveEndpoint (n : ℕ) : ℕ :=
  min (adaptiveEndpoint n) (n - 1)

/-- The finite positive Neumann model, stopped below the fixed threshold `A`.
The safe endpoint makes the definition total; eventually it is the exact
adaptive endpoint. -/
noncomputable def adaptiveNeumannModel (A : ℕ) (n : ℕ) : ℝ :=
  if 0 < n ∧ A ≤ n then
    1 + (Finset.Icc A (safeAdaptiveEndpoint n)).attach.sum (fun t =>
      adaptiveNeumannModel A t.1 / ((t.1 + 1) * Real.log t.1))
  else 1
termination_by n
decreasing_by
  have ht := (Finset.mem_Icc.mp t.property).2
  have hs : safeAdaptiveEndpoint n ≤ n - 1 := min_le_right _ _
  omega

private theorem adaptiveEndpoint_lt_self_of_data
    {n : ℕ} (hdata : AdaptiveCutoffData n) :
    adaptiveEndpoint n < n := by
  have hL1 : 1 ≤ adaptiveLogScale n :=
    (show 1 ≤ 4 by norm_num).trans hdata.logScale_ge_four
  have hLn : adaptiveLogScale n ≤ n := by
    calc
      adaptiveLogScale n ≤ adaptiveLogScale n * adaptiveLogScale n := by
        nlinarith [hdata.logScale_ge_four]
      _ ≤ n := hdata.logScale_sq_le
  exact hdata.endpoint_lt_scale.trans_le hLn

/-- On the cutoff range, the safe endpoint is the exact common endpoint. -/
theorem safeAdaptiveEndpoint_eq_of_data
    {n : ℕ} (hdata : AdaptiveCutoffData n) :
    safeAdaptiveEndpoint n = adaptiveEndpoint n := by
  dsimp [safeAdaptiveEndpoint]
  apply min_eq_left
  have hlt := adaptiveEndpoint_lt_self_of_data hdata
  omega

/-- Exact recursive equation for the stopped ideal model at its total safe
endpoint. -/
theorem adaptiveNeumannModel_eq_safe
    {A n : ℕ} (hAn : A ≤ n) (hnpos : 0 < n) :
    adaptiveNeumannModel A n =
      1 + truncatedLogOperator A (adaptiveNeumannModel A)
        (safeAdaptiveEndpoint n) := by
  rw [adaptiveNeumannModel]
  split_ifs with h
  · dsimp [truncatedLogOperator]
    congr 1
    exact Finset.sum_attach (Finset.Icc A (safeAdaptiveEndpoint n))
      (fun t : ℕ => adaptiveNeumannModel A t /
        ((t + 1) * Real.log t))
  · exact (h ⟨hnpos, hAn⟩).elim

/-- Exact recursive equation for the stopped ideal model on the eventual
cutoff range. -/
theorem adaptiveNeumannModel_eq_of_data
    {A n : ℕ} (hAn : A ≤ n) (hdata : AdaptiveCutoffData n) :
    adaptiveNeumannModel A n =
      1 + truncatedLogOperator A (adaptiveNeumannModel A)
        (adaptiveEndpoint n) := by
  rw [adaptiveNeumannModel]
  have hnpos : 0 < n := by
    have := hdata.logScale_sq_le
    have hL := hdata.logScale_ge_four
    nlinarith
  split_ifs with h
  · rw [safeAdaptiveEndpoint_eq_of_data hdata]
    dsimp [truncatedLogOperator]
    congr 1
    exact Finset.sum_attach (Finset.Icc A (adaptiveEndpoint n))
      (fun t : ℕ => adaptiveNeumannModel A t /
        ((t + 1) * Real.log t))
  · exact (h ⟨hnpos, hAn⟩).elim

/-- Below its terminal threshold the model is exactly one. -/
theorem adaptiveNeumannModel_eq_one {A n : ℕ} (hnA : n < A) :
    adaptiveNeumannModel A n = 1 := by
  rw [adaptiveNeumannModel]
  simp [show ¬A ≤ n by omega]

/-- Every value of the stopped ideal model is at least one. -/
theorem one_le_adaptiveNeumannModel
    {A : ℕ} (hA : 2 ≤ A) (n : ℕ) :
    1 ≤ adaptiveNeumannModel A n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [adaptiveNeumannModel]
      split_ifs with hAn
      · apply le_add_of_nonneg_right
        apply Finset.sum_nonneg
        intro t ht
        have htmem := (Finset.mem_Icc.mp t.property).1
        have htlt : t.1 < n := by
          have htupper := (Finset.mem_Icc.mp t.property).2
          have hs : safeAdaptiveEndpoint n ≤ n - 1 := min_le_right _ _
          omega
        have hmodel : 0 ≤ adaptiveNeumannModel A t.1 :=
          le_trans (by norm_num) (ih t.1 htlt)
        have hlog : 0 < Real.log (t.1 : ℝ) :=
          Real.log_pos (by exact_mod_cast (show 1 < t.1 by omega))
        positivity
      · norm_num

/-- Consequently the model is nonnegative. -/
theorem adaptiveNeumannModel_nonneg
    {A : ℕ} (hA : 2 ≤ A) (n : ℕ) :
    0 ≤ adaptiveNeumannModel A n :=
  (show (0 : ℝ) ≤ 1 by norm_num).trans (one_le_adaptiveNeumannModel hA n)

end Erdos321
