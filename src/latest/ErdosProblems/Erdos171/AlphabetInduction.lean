/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.BaseCases
import ErdosProblems.Erdos171.Iteration
import ErdosProblems.Erdos171.Packaging

/-!
# Alphabet induction for Erdős Problem 171

This file contains the formal induction on the alphabet size in the
Dodos--Kanellopoulos--Tyros proof.  Its sole combinatorial hypothesis says
that density Hales--Jewett for a `k`-letter alphabet, with `k ≥ 2`, supplies
the fixed-density increment step for the `(k+1)`-letter alphabet.  The
iteration of each such step is already proved in `Iteration`.

The one- and two-letter cases are unconditional.  Strong induction then
proves the finite theorem for every nonempty alphabet; the framework turns
that into the eventual theorem, and `Packaging` gives the literal statement
of Erdős Problem 171.
-/

namespace Erdos171

/-- The exact successor-alphabet input required by the DKT alphabet
induction.  It remains an explicit theorem hypothesis in this helper; the
main development must instantiate it with the combinatorial proof. -/
def AlphabetDensityIncrementHypothesis : Type :=
  ∀ k : ℕ, 2 ≤ k → FiniteDensityHJ k →
    ∀ δ : ℝ, 0 < δ → DensityIncrementStep (k + 1) δ

/-- Strong induction on the alphabet size packages the two base cases and
the successor density-increment theorem into one-witness density
Hales--Jewett for every nonempty finite alphabet. -/
theorem finiteDensityHJ_all_of_alphabetDensityIncrement
    (step : AlphabetDensityIncrementHypothesis) :
    ∀ t : ℕ, 1 ≤ t → FiniteDensityHJ t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro ht
      by_cases ht1 : t = 1
      · simpa [ht1] using finiteDensityHJ_one
      by_cases ht2 : t = 2
      · simpa [ht2] using finiteDensityHJ_two
      have ht3 : 3 ≤ t := by omega
      let k := t - 1
      have hk2 : 2 ≤ k := by
        dsimp [k]
        omega
      have hkt : k < t := by
        dsimp [k]
        omega
      have hkpos : 1 ≤ k := hk2.trans' (by omega)
      have hk : FiniteDensityHJ k := ih k hkt hkpos
      have hs : k + 1 = t := by
        dsimp [k]
        omega
      rw [← hs]
      exact hk.succ_of_densityIncrement (step k hk2)

/-- The alphabet induction in the eventual formulation used by Erdős 171. -/
theorem eventualDensityHJ_all_of_alphabetDensityIncrement
    (step : AlphabetDensityIncrementHypothesis) :
    ∀ t : ℕ, 1 ≤ t → EventualDensityHJ t := by
  intro t ht
  exact (finiteDensityHJ_all_of_alphabetDensityIncrement step t ht).eventual
    (by omega)

/-- The exact cardinality-and-coordinate statement of Erdős Problem 171,
conditional only on the successor-alphabet density-increment theorem. -/
theorem erdos171Statement_of_alphabetDensityIncrement
    (step : AlphabetDensityIncrementHypothesis) :
    Erdos171Statement := by
  apply erdos171Statement_of_eventualDensityHJ
  intro t ht
  exact eventualDensityHJ_all_of_alphabetDensityIncrement step t (by omega)

end Erdos171
