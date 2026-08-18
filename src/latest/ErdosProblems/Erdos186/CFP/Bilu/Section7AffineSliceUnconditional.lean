/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section5EpsilonInduction
import ErdosProblems.Erdos186.CFP.Bilu.Section7AffineSlice

/-!
# Unconditional Section 5.6 to Section 7 handoff

Freiman's `2n` theorem is now proved, so the formerly parameterized
residue-cell affine-slice construction can be exposed without a theorem
hypothesis.
-/

namespace Erdos186.CFP.Bilu.Section7AffineSliceUnconditional

open Section7FreimanMap Section5Theorem56 Section5EpsilonInduction
  Section7AffineSlice Section5TwoN

noncomputable section

/-- Uniform source-slice constant for every residue cell of rank `r`. -/
theorem exists_constant_sourceAffineSlice (r : ℕ) (hr : 0 < r) :
    ∃ proportionConstant : ℕ,
      ∀ (m : ℕ) (a : Fin r → EuclideanSpace ℝ (Fin m)) (b : Fin r → ℝ)
        (alpha : Fin r → Fin 2) (K : Finset (Mahler.IntegralPoint m)),
        (residueCell a b alpha K).Nonempty →
        (pairSumset (residueCell a b alpha K)).card <
          (2 * r - 1) * (residueCell a b alpha K).card →
        Nonempty (SourceAffineSlice a b proportionConstant
          (residueCell a b alpha K)) := by
  obtain ⟨proportionConstant, hRank⟩ :=
    (twoNTheoremStatement.{0}) r hr
  refine ⟨proportionConstant, ?_⟩
  intro m a b alpha K hcell hdouble
  exact exists_sourceAffineSlice_of_rankTwoN hRank a b alpha K
    hcell hr hdouble

end

end Erdos186.CFP.Bilu.Section7AffineSliceUnconditional

#print axioms Erdos186.CFP.Bilu.Section7AffineSliceUnconditional.exists_constant_sourceAffineSlice
