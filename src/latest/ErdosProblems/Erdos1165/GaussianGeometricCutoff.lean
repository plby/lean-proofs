/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.GaussianGeometricProfileAssembly

/-!
# An explicit fixed cutoff for the HLOZ geometric A.12 schedule

The deliberately generous fifth power below makes the spectral scale
condition an exact `rpow` calculation.  Its size is irrelevant: it is a
single fixed finite prefix, independent of the terminal scale.
-/

namespace Erdos1165.GaussianGeometricCutoff

noncomputable section

open AppendixFirstMoment ProfileSmallBall GaussianBlockFactorization
  GaussianMultiBlockProfile AppendixA11A12OnePoint
  GaussianGeometricSchedule GaussianGeometricProfileAssembly

/-- The fixed integer appearing in the block-scale estimate. -/
def geometricCutoffBase : ℕ := 2560 * 4096

/-- An explicit terminal-scale-independent Taylor cutoff. -/
def geometricCutoff : ℕ := geometricCutoffBase ^ 5

lemma geometricCutoffBase_eq : geometricCutoffBase = 10485760 := by
  norm_num [geometricCutoffBase]

lemma geometricCutoff_ge_taylor : 18 ^ 5 ≤ geometricCutoff := by
  unfold geometricCutoff
  apply Nat.pow_le_pow_left
  norm_num [geometricCutoffBase]

lemma geometricCutoff_ge_thirty_two : 32 ≤ geometricCutoff := by
  exact (show 32 ≤ 18 ^ 5 by norm_num).trans geometricCutoff_ge_taylor

lemma geometricCutoff_pos : 0 < geometricCutoff := by
  unfold geometricCutoff geometricCutoffBase
  positivity

private lemma geometricCutoff_rpow :
    (geometricCutoff : ℝ) ^ (2 / 5 : ℝ) =
      (geometricCutoffBase : ℝ) ^ 2 := by
  rw [geometricCutoff, Nat.cast_pow, ← Real.rpow_natCast]
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ geometricCutoffBase)]
  norm_num

lemma geometricCutoff_scale_large :
    (2560 * 4096 : ℝ) ≤ (geometricCutoff : ℝ) ^ (2 / 5 : ℝ) := by
  rw [geometricCutoff_rpow]
  rw [show (2560 * 4096 : ℝ) = (geometricCutoffBase : ℝ) by
    norm_num [geometricCutoffBase]]
  change (geometricCutoffBase : ℝ) ≤ (geometricCutoffBase : ℝ) ^ 2
  have hbase : (1 : ℝ) ≤ geometricCutoffBase := by
    norm_num [geometricCutoffBase]
  nlinarith [sq_nonneg ((geometricCutoffBase : ℝ) - 1)]

/-- The canonical geometric schedule at the explicit fixed cutoff satisfies
the complete finite A.12 constrained-Gaussian lower bound. -/
theorem cutoff_canonicalGeometricSchedule_A12 {n : ℕ}
    (hn : geometricCutoff ≤ n) :
    gaussianCenteredPrefixProduct geometricCutoff *
        Real.exp (-gaussianBlockTotalCost
          (geometricSchedule geometricCutoff
            (geometricDepth geometricCutoff n) n)) ≤
      constrainedGaussianDeviationWeight n (1 / 5 : ℝ) :=
  canonicalGeometricSchedule_A12 geometricCutoff_ge_thirty_two hn
    geometricCutoff_scale_large

/-- The exact shifted A.11--A.12 constrained-profile lower bound, now with
all deterministic schedule hypotheses discharged. -/
theorem cutoff_canonicalGeometricSchedule_profileLower_le {n : ℕ}
    (hn : geometricCutoff ≤ n) :
    multiblockProfileLower n (1 / 5 : ℝ) 2 1 10
        (geometricSchedule geometricCutoff
          (geometricDepth geometricCutoff n) n) ≤
      constrainedProfileWeight n (1 / 5 : ℝ) := by
  exact geometricSchedule_profileLower_le geometricCutoff_ge_taylor
    (geometricDepth_terminal_lower geometricCutoff_pos hn)
    (geometricDepth_terminal_upper geometricCutoff_pos hn)
    geometricCutoff_scale_large

/-- Exact `O(n^(3/5))` cost of the canonical cutoff schedule. -/
theorem cutoff_canonicalGeometricSchedule_totalCost_le {n : ℕ}
    (hn : geometricCutoff ≤ n) :
    gaussianBlockTotalCost
        (geometricSchedule geometricCutoff
          (geometricDepth geometricCutoff n) n) ≤
      26214505 * (n : ℝ) ^ (3 / 5 : ℝ) :=
  geometricSchedule_totalCost_le_sharp geometricCutoff_ge_thirty_two
    (geometricDepth_terminal_lower geometricCutoff_pos hn)
    (geometricDepth_terminal_upper geometricCutoff_pos hn)

end

end Erdos1165.GaussianGeometricCutoff
