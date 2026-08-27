/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AffineInitialVortexExponent
import ErdosProblems.Erdos207.RetainedPowerVortex

/-! # An actual initial master law with compatible gradual-vortex parameters -/

namespace Erdos207

open scoped NNReal

noncomputable section

theorem eventually_exists_gradual_initial_master_base_with_bank
    (q h b rootMinimum step Rfloor K : ℕ) (hb : 1 ≤ b) (hstep : 0 < step) :
    ∃ B k rootPower Rfixed ell length m N₀ : ℕ,
      ∃ hfit : length ≤ ell, ∃ hlength : 0 < length,
        rootMinimum ≤ rootPower ∧ K * (2 * step + 1) ≤ rootPower ∧
        Rfloor ≤ Rfixed ∧ 0 < Rfixed ∧ powerBankSubsetExponent q rootPower + 2 ≤ Rfixed ∧
        2 ≤ length ∧ length + m = ell ∧
        rootPower < step * m ∧ step * m ≤ rootPower + step ∧
        K * (Rfixed + step + 1) ≤ Rfixed + step * ell ∧
        ∀ n : ℕ, N₀ ≤ n → Admissible n →
          ∃ P : InitialPowerVortexPackage q h n ell (dyadicPowerScale (Rfixed + step * ell) n) rootPower step,
            2 ≤ dyadicPowerScale (Rfixed + step * ell) n ∧
            2 ^ (Rfixed + step * ell) ≤ dyadicPowerScale (Rfixed + step * ell) n ∧
            HasAbsorberSourcePrefixBounds q P.B (P.retainedVortex length hfit hlength) ∧
            ∃ initialLaw : FiniteLaw (GreedyStateOn (Fin n)),
              IsInitialTypicalPatternLaw q h b B k (dyadicPowerScale (Rfixed + step * ell) n)
                P.H P.B P.W initialLaw ∧
              ∃ masterLaw, IsInitialResidualCompressedMasterLawWithError q h b
                (dyadicPowerScale (Rfixed + step * ell) n) P.H P.B
                (P.retainedVortex length hfit hlength)
                (2 * ksssInitialGraphProductConstant q (initialErdosCoefficientBound q))
                (initialPatternGraphError q h ell n (dyadicPowerScale (Rfixed + step * ell) n)) masterLaw := by
  obtain ⟨B, k, rootPower, Rfixed, hroot, hfloor, hRfixed, hbank, hN⟩ :=
    eventually_exists_initial_pattern_law_affine_vortex_exponent_with_bank q h
      (max rootMinimum (K * (2 * step + 1))) b Rfloor hb
  obtain ⟨ell, length, m, hlength2, hsplit, hlow, hupp, hfirst⟩ :=
    exists_retained_power_vortex_length rootPower step Rfixed K hstep
  have hell : 0 < ell := by omega
  have hfit : length ≤ ell := by omega
  have hlength : 0 < length := by omega
  let R := Rfixed + step * ell
  have hR : 0 < R := by dsimp only [R]; omega
  obtain ⟨Nlaw, hNlaw⟩ := hN step ell hell
  obtain ⟨Nsize, hNsize⟩ := eventually_le_dyadicPowerScale hR (max 2 (2 ^ R))
  refine ⟨B, k, rootPower, Rfixed, ell, length, m, Nlaw + Nsize + 1, hfit, hlength,
    (le_max_left _ _).trans hroot, (le_max_right _ _).trans hroot, hfloor, hRfixed,
    hbank, hlength2, hsplit, hlow, hupp, hfirst, ?_⟩
  intro n hn hadmissible
  obtain ⟨P, initialLaw, hinitial, _hsource, _hzero, _hbase, hretained⟩ := hNlaw n (by omega)
  have hsize := hNsize n (by omega)
  obtain ⟨_hsupport, hsource, hmaster⟩ := hretained length
    (terminalJumpStage ell length hfit) (terminalJumpStage_strictMono ell length hfit)
    (terminalJumpStage_zero ell length hfit hlength)
  obtain ⟨masterLaw, hmasterLaw⟩ := hmaster hadmissible
  exact ⟨P, (le_max_left _ _).trans hsize, (le_max_right _ _).trans hsize,
    hsource, initialLaw, hinitial, masterLaw, hmasterLaw⟩

theorem eventually_exists_gradual_initial_master_base
    (q h b rootMinimum step Rfloor K : ℕ) (hb : 1 ≤ b) (hstep : 0 < step) :
    ∃ B k rootPower Rfixed ell length m N₀ : ℕ,
      ∃ hfit : length ≤ ell, ∃ hlength : 0 < length,
        rootMinimum ≤ rootPower ∧ K * (2 * step + 1) ≤ rootPower ∧
        Rfloor ≤ Rfixed ∧ 0 < Rfixed ∧ 2 ≤ length ∧ length + m = ell ∧
        rootPower < step * m ∧ step * m ≤ rootPower + step ∧
        K * (Rfixed + step + 1) ≤ Rfixed + step * ell ∧
        ∀ n : ℕ, N₀ ≤ n → Admissible n →
          ∃ P : InitialPowerVortexPackage q h n ell (dyadicPowerScale (Rfixed + step * ell) n) rootPower step,
            2 ≤ dyadicPowerScale (Rfixed + step * ell) n ∧
            2 ^ (Rfixed + step * ell) ≤ dyadicPowerScale (Rfixed + step * ell) n ∧
            HasAbsorberSourcePrefixBounds q P.B (P.retainedVortex length hfit hlength) ∧
            ∃ initialLaw : FiniteLaw (GreedyStateOn (Fin n)),
              IsInitialTypicalPatternLaw q h b B k (dyadicPowerScale (Rfixed + step * ell) n)
                P.H P.B P.W initialLaw ∧
              ∃ masterLaw, IsInitialResidualCompressedMasterLawWithError q h b
                (dyadicPowerScale (Rfixed + step * ell) n) P.H P.B
                (P.retainedVortex length hfit hlength)
                (2 * ksssInitialGraphProductConstant q (initialErdosCoefficientBound q))
                (initialPatternGraphError q h ell n (dyadicPowerScale (Rfixed + step * ell) n)) masterLaw := by
  obtain ⟨B, k, rootPower, Rfixed, ell, length, m, N₀, hfit, hlength,
    hroot, hrootGap, hfloor, hfixed, _hbank, hlength2, hsplit, hlo, hhi, hfirst, hrest⟩ :=
    eventually_exists_gradual_initial_master_base_with_bank q h b rootMinimum step Rfloor K hb hstep
  exact ⟨B, k, rootPower, Rfixed, ell, length, m, N₀, hfit, hlength,
    hroot, hrootGap, hfloor, hfixed, hlength2, hsplit, hlo, hhi, hfirst, hrest⟩


end

end Erdos207
