/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedTwoAwayPartialCount

/-! # The special localized nibble weight bound for one indexed order -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem localizedTwoAway_induced_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} {H : SimpleGraph V} {B : TripleSystemOn V} {X U : Finset V}
    (T : TripleOn V) {a b : V} (hab : a ≠ b) (hj : 4 ≤ j) (hjq : j ≤ q)
    (hsep : AbsorberSeparatedLevel H X B U)
    (hrootLocal : HasPaddedAbsorberRootLocalization q X B) :
    HasExtensionBound
      (fun w : LocalizedTwoAwayWitness V (absorberInducedConfigurationsOn q j B) T a b U ↦
        localizedTwoAwayRemainder w)
      (constantTripleWeight (Fintype.card V + 1 : ℝ≥0)⁻¹)
      ((45 * (q + 1) + 28 : ℕ) + (U.card : ℝ≥0) * pairExactBankExtensionCoefficient q B /
        (Fintype.card V + 1 : ℝ≥0)) := by
  intro R
  let F := absorberInducedConfigurationsOn q j B
  let N : ℝ≥0 := Fintype.card V + 1
  let C : ℝ≥0 := pairExactBankExtensionCoefficient q B
  let K : ℝ≥0 := (45 * (q + 1) + 28 : ℕ)
  have hN : N ≠ 0 := by dsimp only [N]; positivity
  have hcard : ∀ E ∈ F, E.card = j - 2 :=
    fun E hE ↦ (mem_absorberInducedConfigurationsOn_iff.mp hE).1
  change extensionWeight (fun w : LocalizedTwoAwayWitness V F T a b U ↦ localizedTwoAwayRemainder w)
    (constantTripleWeight N⁻¹) R ≤ K + U.card * C / N
  rw [extensionWeight_localizedTwoAway_constant F T a b U R (j - 2) hcard]
  rcases lt_trichotomy R.card (j - 4) with hR | hR | hR
  · have hcount := card_activeLocalizedTwoAway_partial_le q j B F Subset.rfl T hab U R hR
    have hcast : (Fintype.card (ActiveLocalizedTwoAwayWitness V F T a b U R) : ℝ≥0) ≤
        U.card * C * N ^ (j - R.card - 5) := by
      dsimp only [C, N]
      exact_mod_cast (show Fintype.card (ActiveLocalizedTwoAwayWitness V F T a b U R) ≤
        U.card * pairExactBankExtensionCoefficient q B * (Fintype.card V + 1) ^ (j - R.card - 5) by
          simpa only [Nat.mul_assoc] using hcount)
    have hexp : j - 2 - 2 - R.card = (j - R.card - 5) + 1 := by omega
    have hcancel : N ^ (j - R.card - 5) * (N⁻¹) ^ ((j - R.card - 5) + 1) = N⁻¹ := by
      rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hN, one_pow, one_mul]
    calc
      _ ≤ (U.card * C * N ^ (j - R.card - 5)) * (N⁻¹) ^ (j - 2 - 2 - R.card) :=
        mul_le_mul_of_nonneg_right hcast (by positivity)
      _ = U.card * C / N := by
        rw [hexp]
        calc
          _ = U.card * C * (N ^ (j - R.card - 5) * (N⁻¹) ^ ((j - R.card - 5) + 1)) := by ring
          _ = _ := by rw [hcancel]; rfl
      _ ≤ _ := le_add_left le_rfl
  · have hR' : R.card = (j - 2) - 2 := by omega
    have hcount := card_activeLocalizedTwoAway_full_le (T := T) hab R
      (absorberInducedConfigurationsOn_subset_erdosForbidden (by omega)) hcard hR' hsep hrootLocal
    have hcount' : Fintype.card (ActiveLocalizedTwoAwayWitness V F T a b U R) ≤ 45 * (q + 1) + 28 := by
      have hRq : R.card ≤ q := by omega
      exact hcount.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 45 (by omega)) 28)
    have hexp : j - 2 - 2 - R.card = 0 := by omega
    rw [hexp, pow_zero, mul_one]
    exact (show (Fintype.card (ActiveLocalizedTwoAwayWitness V F T a b U R) : ℝ≥0) ≤ K by
      dsimp only [K]
      exact_mod_cast hcount').trans (le_add_right le_rfl)
  · have hR' : (j - 2) - 2 < R.card := by omega
    rw [card_activeLocalizedTwoAway_eq_zero_of_large_root F T a b U R (j - 2) hcard hR',
      Nat.cast_zero, zero_mul]
    exact bot_le

end

end Erdos207
