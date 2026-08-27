/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialResidualCompression
import ErdosProblems.Erdos207.EventualInitialPatternNibble

/-! # Eventual actual residual master base, retaining source well-spreadness -/

namespace Erdos207

open scoped NNReal

noncomputable section

theorem eventually_exists_initial_residual_master_base_with_source_bounds
    (q h rootMinimum step ell b Rfloor : ℕ) (hell : 0 < ell) (hb : 1 ≤ b) :
    ∃ B k rootPower R N₀ : ℕ, rootMinimum ≤ rootPower ∧ Rfloor ≤ R ∧ 0 < R ∧
      ∀ n : ℕ, N₀ ≤ n → Admissible n →
        ∃ P : InitialPowerVortexPackage q h n ell (dyadicPowerScale R n) rootPower step,
          ∃ law, IsInitialTypicalPatternLaw q h b B k (dyadicPowerScale R n) P.H P.B P.W law ∧
            (∃ masterLaw, IsInitialResidualCompressedMasterLaw q h b (dyadicPowerScale R n)
              P.H P.B P.W masterLaw) ∧
            (∀ i : Fin ell, ∀ j : ℕ, 4 ≤ j → j ≤ q →
              SourceVortexWellSpread (P.W.prefix i.succ) j (absorberInducedConfigurationsOn q j P.B)
                (((2 : ℝ≥0) ^ (12 * (q + 2) ^ 2) + 1) * exactBankVortexOrderCoefficient q (i.val + 1))
                (2 * (((2 : ℝ≥0) ^ (12 * (q + 2) ^ 2) + 1) * exactBankVortexOrderCoefficient q (i.val + 1)) +
                  exactBankVortexCoefficient j (i.val + 1))) ∧
            ∀ j : ℕ, 4 ≤ j → j ≤ q →
              SourceVortexWellSpread (P.W.prefix 0) j (absorberInducedConfigurationsOn q j P.B)
                (2 * exactBankVortexOrderCoefficient q 0)
                (2 * ((subsetsUpToCard P.B q).card * (exactBankVortexOrderCoefficient q 0 : ℝ≥0)) +
                  exactBankVortexCoefficient j 0) := by
  obtain ⟨B, k, rootPower, R, N₀, hroot, hfloor, hR, hN⟩ :=
    eventually_exists_initial_typical_pattern_law_with_source_bounds
      q h rootMinimum step ell b Rfloor hell hb
  refine ⟨B, k, rootPower, R, N₀, hroot, hfloor, hR, ?_⟩
  intro n hn hadmissible
  obtain ⟨P, law, hlaw, hsource, hzero⟩ := hN n hn
  exact ⟨P, law, hlaw,
    ⟨_, P.compressed_residual_master_of_initial_pattern_law hadmissible law hlaw⟩,
    hsource, hzero⟩

end

end Erdos207
