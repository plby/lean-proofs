import ErdosProblems.Erdos421.BuchstabBranchPrimeSaving
import ErdosProblems.Erdos421.BuchstabPrimeSplitting

/-! # Uniform prime summation for the actual finite Buchstab functions -/

namespace Erdos421

theorem finiteBuchstab_prime_log_saving {A ε K : ℝ}
    (hA : 0 ≤ A) (hε : 0 < ε) (hK : 0 ≤ K) :
    ∃ X₀ > 1, ∀ X a b : ℝ, 1 < X → X₀ ≤ a → a ≤ b → 1 ≤ Real.log a →
      Real.log X ≤ K * Real.log a → ∀ n : ℕ,
      (∀ t ∈ Set.Icc a b, 1 ≤ logarithmicBuchstabArgument X t) →
      |buchstabPrimeDiscrepancy X (finiteBuchstab n) a b| ≤ ε / (Real.log a) ^ A := by
  have hε₂ : 0 < ε / 2 := by positivity
  obtain ⟨X₀, hX₀, hzero⟩ := buchstab_zero_prime_saving hA hε₂ hK
  obtain ⟨X₁, hX₁, hlow⟩ := buchstab_low_branch_prime_saving hA hε₂ hK
  obtain ⟨X₂, hX₂, hupp⟩ := buchstab_upper_branch_prime_saving hA hε₂ hK
  refine ⟨max X₀ (max X₁ X₂), hX₀.trans_le (le_max_left _ _), ?_⟩
  intro X a b hX ha hab hlog hscale n harg
  have ha₀ : X₀ ≤ a := (le_max_left _ _).trans ha
  have ha₁ : X₁ ≤ a := (le_trans (le_max_left _ _) (le_max_right _ _)).trans ha
  have ha₂ : X₂ ≤ a := (le_trans (le_max_right _ _) (le_max_right _ _)).trans ha
  have ha1 : 1 < a := hX₀.trans_le ha₀
  have hlap := Real.log_pos ha1
  have hhalf : ε / 2 / (Real.log a) ^ A ≤ ε / (Real.log a) ^ A :=
    div_le_div_of_nonneg_right (by linarith) (Real.rpow_nonneg hlap.le A)
  cases n with
  | zero => exact (hzero X a b hX ha₀ hab hlog hscale harg).trans hhalf
  | succ n =>
    by_cases hbc : b ≤ buchstabPrimeBreakpoint X
    · apply (hupp X a b hX ha₂ hab hlog hscale n ?_).trans hhalf
      intro t ht
      exact logarithmicBuchstabArgument_upper_branch hX (ha1.trans_le ht.1)
        (ht.2.trans hbc)
    by_cases hca : buchstabPrimeBreakpoint X ≤ a
    · apply (hlow X a b hX ha₁ hab hlog hscale (n + 1) ?_).trans hhalf
      intro t ht
      exact ⟨harg t ht, logarithmicBuchstabArgument_lower_branch hX
        (ha1.trans_le ht.1) (hca.trans ht.1)⟩
    have hac : a ≤ buchstabPrimeBreakpoint X := (lt_of_not_ge hca).le
    have hcb : buchstabPrimeBreakpoint X ≤ b := (lt_of_not_ge hbc).le
    have hlogac : Real.log a ≤ Real.log (buchstabPrimeBreakpoint X) :=
      Real.log_le_log (by linarith) hac
    have hscale' : Real.log X ≤ K * Real.log (buchstabPrimeBreakpoint X) :=
      hscale.trans (mul_le_mul_of_nonneg_left hlogac hK)
    have hu := hupp X a (buchstabPrimeBreakpoint X) hX ha₂ hac hlog hscale n (by
      intro t ht
      exact logarithmicBuchstabArgument_upper_branch hX (ha1.trans_le ht.1) ht.2)
    have hl := hlow X (buchstabPrimeBreakpoint X) b hX (ha₁.trans hac) hcb
      (hlog.trans hlogac) hscale' (n + 1) (by
        intro t ht
        exact ⟨harg t ⟨hac.trans ht.1, ht.2⟩,
          logarithmicBuchstabArgument_lower_branch hX
            ((ha1.trans_le hac).trans_le ht.1) ht.1⟩)
    have hd : ε / 2 / (Real.log (buchstabPrimeBreakpoint X)) ^ A ≤
        ε / 2 / (Real.log a) ^ A :=
      div_le_div_of_nonneg_left hε₂.le (Real.rpow_pos_of_pos hlap A)
        (Real.rpow_le_rpow hlap.le hlogac hA)
    rw [buchstabPrimeDiscrepancy_add (finiteBuchstab_continuous (n + 1)) ha1 hac hcb]
    calc
      _ ≤ |buchstabPrimeDiscrepancy X (finiteBuchstab (n + 1)) a
          (buchstabPrimeBreakpoint X)| +
          |buchstabPrimeDiscrepancy X (finiteBuchstab (n + 1))
            (buchstabPrimeBreakpoint X) b| := abs_add_le _ _
      _ ≤ ε / 2 / (Real.log a) ^ A + ε / 2 / (Real.log a) ^ A :=
        add_le_add hu (hl.trans hd)
      _ = _ := by ring

end Erdos421
