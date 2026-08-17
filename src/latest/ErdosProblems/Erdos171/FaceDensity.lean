/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.Density
import ErdosProblems.Erdos171.SubspaceOps
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Density of the old-alphabet face

Inside `[k+1]^m`, the words using only the first `k` letters form the image
of `[k]^m` under `liftWord`.  This file records their exact density and the
fact that this density tends to zero with the dimension.
-/

namespace Erdos171

open Filter Finset

/-- The old-alphabet face in `[k+1]^m` has density `(k/(k+1))^m`. -/
theorem density_liftFinset_univ (k m : ℕ) :
    density (liftFinset (Finset.univ : Finset (Word k m))) =
      ((k : ℝ) / (k + 1)) ^ m := by
  rw [density_eq_card_div_card, card_liftFinset]
  simp only [Finset.card_univ, card_word, Nat.cast_pow, Nat.cast_add,
    Nat.cast_one, div_pow]

/-- The ratio between the old alphabet and the enlarged alphabet lies in
`[0,1)`. -/
theorem oldAlphabetRatio_nonneg_lt_one (k : ℕ) :
    0 ≤ (k : ℝ) / (k + 1) ∧ (k : ℝ) / (k + 1) < 1 := by
  constructor
  · positivity
  · rw [div_lt_one (by positivity : (0 : ℝ) < k + 1)]
    norm_num

/-- The density of the old-alphabet face tends to zero. -/
theorem tendsto_density_liftFinset_univ (k : ℕ) :
    Tendsto
      (fun m ↦ density (liftFinset (Finset.univ : Finset (Word k m))))
      atTop (nhds 0) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (oldAlphabetRatio_nonneg_lt_one k).1 (oldAlphabetRatio_nonneg_lt_one k).2
  exact hpow.congr' (Filter.Eventually.of_forall fun m ↦ (density_liftFinset_univ k m).symm)

/-- In sufficiently high dimension the old-alphabet face has density below
any prescribed positive threshold. -/
theorem eventually_density_liftFinset_univ_lt (k : ℕ) {eta : ℝ}
    (heta : 0 < eta) :
    ∃ M : ℕ, ∀ m ≥ M,
      density (liftFinset (Finset.univ : Finset (Word k m))) < eta := by
  have hevent : ∀ᶠ m : ℕ in atTop,
      density (liftFinset (Finset.univ : Finset (Word k m))) < eta :=
    (tendsto_order.mp (tendsto_density_liftFinset_univ k)).2 eta heta
  exact Filter.eventually_atTop.mp hevent

/-- Explicitly quantified version used by the density-increment argument. -/
theorem exists_faceDensity_lt (k : ℕ) (_hk : 0 < k) :
    ∀ eta : ℝ, 0 < eta →
      ∃ M : ℕ, ∀ m ≥ M,
        density (liftFinset (Finset.univ : Finset (Word k m))) < eta := by
  intro eta heta
  exact eventually_density_liftFinset_univ_lt k heta

end Erdos171
