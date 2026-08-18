/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section9Replacement

/-!
# Audit of the current Section 9 replacement-seed interface

The existing `exists_lemma45SectionSeed_of_proposition83_rpow` asks for a
scalar rank budget that cannot hold in its advertised nondegenerate range.
This file records that fact explicitly so the terminal assembly does not
silently treat the vacuous constructor as a source theorem.
-/

namespace Erdos186.CFP.Bilu.Section9SourceSeedAudit

noncomputable section

set_option autoImplicit false

/-- The current `sigma * 2^r` rank premise is inconsistent with
`sigma ≥ 1`, positive rank, and positive exponential gap. -/
theorem not_sigma_mul_two_pow_le_rpow_rankGap
    {r : ℕ} (hr : 0 < r) {sigma delta : ℝ}
    (hsigma : 1 ≤ sigma) (hdelta : 0 < delta) :
    ¬ sigma * (2 : ℝ) ^ r ≤
      Real.rpow 2 (((r - 1 : ℕ) : ℝ) + 1 - delta) := by
  intro hbudget
  have hrone : 1 ≤ r := hr
  have hrsub : r - 1 + 1 = r := Nat.sub_add_cancel hrone
  have hexponent : (((r - 1 : ℕ) : ℝ) + 1 - delta) < (r : ℝ) := by
    have hcast : (((r - 1 : ℕ) : ℝ) + 1) = (r : ℝ) := by
      exact_mod_cast hrsub
    rw [hcast]
    linarith
  have hrpow :
      Real.rpow 2 (((r - 1 : ℕ) : ℝ) + 1 - delta) <
        (2 : ℝ) ^ r := by
    calc
      Real.rpow 2 (((r - 1 : ℕ) : ℝ) + 1 - delta) <
          Real.rpow 2 (r : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexponent
      _ = (2 : ℝ) ^ r := Real.rpow_natCast 2 r
  have hpow_le : (2 : ℝ) ^ r ≤ sigma * (2 : ℝ) ^ r :=
    le_mul_of_one_le_left (by positivity) hsigma
  exact (not_lt_of_ge hbudget) (hrpow.trans_le hpow_le)

end

end Erdos186.CFP.Bilu.Section9SourceSeedAudit

#print axioms
  Erdos186.CFP.Bilu.Section9SourceSeedAudit.not_sigma_mul_two_pow_le_rpow_rankGap
