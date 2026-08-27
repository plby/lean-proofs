/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceIntegerSieve
import ErdosProblems.Erdos4b.FGKMTSmoothCleanup

/-! # An unconditional full-interval sieve with a prime-sized cleanup budget -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem exists_initial_sieve_budget :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      ∃ r : ℕ → ℕ,
        ((initialResidueSurvivors x ⌊sourceIntervalLength c x⌋₊ r).card : ℝ) ≤
          K * x / Real.log (x : ℝ) := by
  obtain ⟨a, ha, hsmooth⟩ := exists_source_smooth_count_budget
  obtain ⟨c, K, hc, hK, hsieve⟩ := exists_source_initial_sieve ha
  refine ⟨c, K + 1, hc, by linarith, ?_⟩
  filter_upwards [hsieve, hsmooth c hc] with x hx hsm
  obtain ⟨r, hr⟩ := hx
  refine ⟨r, hr.trans ?_⟩
  calc
    _ ≤ (x : ℝ) / Real.log (x : ℝ) + K * x / Real.log (x : ℝ) :=
      add_le_add hsm le_rfl
    _ = _ := by ring

end

end Erdos4b.FGKMT
