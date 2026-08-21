import ErdosProblems.Erdos239.External.Erdos67.TwistSeparation

/-!
# Elementary endpoint cases of the polynomial-height correlation bound

These cases do not use an analytic prime-correlation estimate: their quantified
frequency window is empty.  They are kept separate from `TwistSeparation.lean`
so that the analytic development can import them at its chosen layer.
-/

namespace Erdos67

noncomputable section

theorem polynomialHeightPrimeCorrelationBound_zero_conductor
    (D : ℕ) (T : ℝ) :
    PolynomialHeightPrimeCorrelationBound 0 D T := by
  refine ⟨2, le_rfl, ?_⟩
  intro Y q q' hY hq hqQ hq' hq'Q χ χ' v hvLower hvUpper
  omega

theorem polynomialHeightPrimeCorrelationBound_zero_degree
    (Q : ℕ) (T : ℝ) :
    PolynomialHeightPrimeCorrelationBound Q 0 T := by
  obtain ⟨N, hTN⟩ : ∃ N : ℕ, T < N := exists_nat_gt T
  refine ⟨max 2 N, le_max_left 2 N, ?_⟩
  intro Y q q' hY hq hqQ hq' hq'Q χ χ' v hvLower hvUpper
  have hNY : N ≤ Y := (le_max_right 2 N).trans hY
  have hTY : T < (Y : ℝ) := hTN.trans_le (by exact_mod_cast hNY)
  simp only [pow_zero, mul_one] at hvUpper
  exfalso
  linarith

theorem polynomialHeightPrimeCorrelationBound_of_nonpos_height
    (Q D : ℕ) {T : ℝ} (hT : T ≤ 0) :
    PolynomialHeightPrimeCorrelationBound Q D T := by
  refine ⟨2, le_rfl, ?_⟩
  intro Y q q' hY hq hqQ hq' hq'Q χ χ' v hvLower hvUpper
  have hpow : 0 ≤ (Y : ℝ) ^ D := by positivity
  have hupperNonpos : T * (Y : ℝ) ^ D ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hT hpow
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hY)
  exfalso
  linarith [abs_nonneg v]

theorem polynomialHeightPrimeCorrelationBound_degree_one_of_lt_one
    (Q : ℕ) {T : ℝ} (hT : T < 1) :
    PolynomialHeightPrimeCorrelationBound Q 1 T := by
  refine ⟨2, le_rfl, ?_⟩
  intro Y q q' hY hq hqQ hq' hq'Q χ χ' v hvLower hvUpper
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hY)
  simp only [pow_one] at hvUpper
  have hTY : T * (Y : ℝ) < (Y : ℝ) := by nlinarith
  exfalso
  linarith

end

end Erdos67
