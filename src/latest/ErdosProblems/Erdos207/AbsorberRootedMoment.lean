/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberRootedCount
import ErdosProblems.Erdos207.GreedyRootedConfigurationMoment

/-! # The first crude-statistic moment for the actual absorber-induced family -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem absorberInduced_rootedConfiguration_moment_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (S : Ω → GreedyStateOn V)
    (F : ForbiddenFamilyOn V) (B R : TripleSystemOn V)
    (q j c s : ℕ) (C : ℝ≥0)
    (hS : L.SupportedOn (fun ω ↦ GreedyInvariant F (S ω)))
    (hR : R.card = 2) (hc : c + 5 ≤ j)
    (hjoint : ∀ T : TripleSystemOn V, T.card ≤ s * c →
      L.probability (fun ω ↦ T ⊆ (S ω).chosen) ≤
        C * ((Fintype.card V + 1 : ℝ≥0)⁻¹) ^ T.card) :
    L.expectation (fun ω ↦ ((greedyRootedConfigurationClass
      (absorberInducedConfigurationsOn q j B) (S ω) R c).card : ℝ≥0) ^ s) ≤
      C * (((2 : ℝ≥0) ^ (s * c) *
        ((2 : ℝ≥0) ^ (j - 2) * pairExactBankExtensionCoefficient q B *
          (Fintype.card V + 1 : ℝ≥0) ^ (j - c - 5))) ^ s) := by
  have hexp : j - 2 - c - 3 = j - c - 5 := by omega
  have hjoint' : ∀ T : TripleSystemOn V, T.card ≤ s * c →
      L.probability (fun ω ↦ T ⊆ (S ω).chosen) ≤
        C * (((Fintype.card V + 1 : ℕ) : ℝ≥0)⁻¹) ^ T.card := by
    simpa only [Nat.cast_add, Nat.cast_one] using hjoint
  have hcount : ∀ Q : TripleSystemOn V, 2 ≤ Q.card → Q.card < j - 2 →
      (familyExtensions (absorberInducedConfigurationsOn q j B) Q).card ≤
        pairExactBankExtensionCoefficient q B *
          (Fintype.card V + 1) ^ (j - 2 - Q.card - 1) := by
    intro Q hQ hQsmall
    have he : j - 2 - Q.card - 1 = j - Q.card - 3 := by omega
    rw [he]
    exact card_familyExtensions_absorberInduced_le_strong q j B Q hQ hQsmall
  simpa only [hexp, Nat.cast_add, Nat.cast_one] using
    greedyRootedConfigurationClass_moment_le L S F
      (absorberInducedConfigurationsOn q j B) R c (j - 2)
      (Fintype.card V + 1) (pairExactBankExtensionCoefficient q B) s C
      hS absorberInducedConfigurationsOn_fixed_card hR (by omega) (by omega)
      hcount hjoint'

end

end Erdos207
