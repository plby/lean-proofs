import ErdosProblems.Erdos321.QuotientPrimeBounds
import ErdosProblems.Erdos321.LowerMainRecurrence
import ErdosProblems.Erdos321.EntropyBasics

namespace Erdos321

/-- PNT lower coefficient for the quotient interval at `t`. -/
noncomputable def quotientLowerCoefficient (C : ℝ) (N t : ℕ) : ℝ :=
  let a : ℝ := (N / (t + 1) : ℕ)
  let b : ℝ := (N / t : ℕ)
  ((b - a) - (C * b / Real.log b ^ 2 + C * a / Real.log a ^ 2)) /
    Real.log b

/-- PNT upper coefficient for the quotient interval at `t`. -/
noncomputable def quotientUpperCoefficient (C : ℝ) (N t : ℕ) : ℝ :=
  let a : ℝ := (N / (t + 1) : ℕ)
  let b : ℝ := (N / t : ℕ)
  ((b - a) + (C * b / Real.log b ^ 2 + C * a / Real.log a ^ 2)) /
    Real.log a

/-- The formally derived lower recurrence in pure real-analytic coordinates. -/
theorem exists_analytic_lower_recurrence_constant :
    ∃ C ≥ 0, ∀ {N T : ℕ}, 1 ≤ T → T < N / (T + 1) →
      2 ≤ N / (T + 1) →
      (∑ t ∈ Finset.Icc 1 T,
        quotientLowerCoefficient C N t * extremalSize t) ≤
      extremalSize N + 3 ^ T * T ^ 2 * (T + 1) := by
  obtain ⟨C, hC, hCard⟩ := exists_quotientPrime_card_bounds
  refine ⟨C, hC, ?_⟩
  intro N T hT hcut ha
  have hMain := sum_quotientPrimes_mul_extremalSize_le_add_error
    (N := N) hT
  have hMainR :
      ((∑ t ∈ Finset.Icc 1 T,
        (quotientPrimes N T t).card * extremalSize t : ℕ) : ℝ) ≤
      ((extremalSize N + 3 ^ T * T ^ 2 * (T + 1) : ℕ) : ℝ) := by
    exact_mod_cast hMain
  calc
    (∑ t ∈ Finset.Icc 1 T,
      quotientLowerCoefficient C N t * extremalSize t) ≤
        ∑ t ∈ Finset.Icc 1 T,
          (quotientPrimes N T t).card * extremalSize t := by
      push_cast
      apply Finset.sum_le_sum
      intro t ht
      have htData := Finset.mem_Icc.mp ht
      have hden : N / (T + 1) ≤ N / (t + 1) :=
        Nat.div_le_div_left (Nat.add_le_add_right htData.2 1) (by omega)
      have hcutT : T < N / (t + 1) := hcut.trans_le hden
      have haT : 2 ≤ N / (t + 1) := ha.trans hden
      have hq := (hCard (N := N) (Q := T) (t := t)
        htData.1 hcutT haT).1
      dsimp [quotientLowerCoefficient]
      apply mul_le_mul_of_nonneg_right hq
      positivity
    _ ≤ extremalSize N + 3 ^ T * T ^ 2 * (T + 1) := by
      norm_cast at hMainR ⊢

end Erdos321
