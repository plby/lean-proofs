/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GainDefectReverseClass
import ErdosProblems.Erdos207.AbsorberUniformRootCount

/-! # The actual absorber family's reverse fourth-moment class weight -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem gainDefectReverseClassWeight_absorberInduced_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (q r s z : ℕ) (B : TripleSystemOn V) (T : TripleOn V)
    (H Q : TripleSystemOn V) (b : ℕ) (hz : 1 ≤ z)
    (hbudget : s + 4 ≤ vortexRootExponent r b + vortexRootExponent s Q.card) :
    gainDefectReverseClassWeight (absorberInducedConfigurationsOn q r B)
      (absorberInducedConfigurationsOn q s B) T z H Q b (Fintype.card V + 1 : ℝ≥0)⁻¹ ≤
      (2 : ℝ≥0) ^ (r - 2) *
        (((pairExactBankExtensionCoefficient q B : ℕ) *
          (2 : ℝ≥0) ^ (s - 2 + 1) * pairExactBankExtensionCoefficient q B) *
            (Fintype.card V + 1 : ℝ≥0) ^ (z - 1)) := by
  classical
  let F := absorberInducedConfigurationsOn q r B
  let G := absorberInducedConfigurationsOn q s B
  have hF : ∀ E ∈ F, E.card = r - 2 := absorberInducedConfigurationsOn_fixed_card
  have hG : ∀ E ∈ G, E.card = s - 2 := absorberInducedConfigurationsOn_fixed_card
  by_cases hne : (gainDefectReverseClass F G T z H Q b).Nonempty
  · obtain ⟨w, hw⟩ := hne
    have h := (mem_filter.mp hw).2
    have ha1 : 1 ≤ Q.card := by
      have hp := card_pos.mpr h.2.1.2.2
      have hle : H.card ≤ (w.reverseSecondRoot H).card := card_le_card subset_union_left
      rw [h.2.2.1] at hle
      omega
    have ha : Q.card ≤ s - 2 := by
      rw [← h.2.2.1, ← hG w.second w.second_mem]
      exact card_le_card (w.reverseSecondRoot_subset H h.1 h.2.1)
    have hb1 : 1 ≤ b := by
      have h2 := w.reverseFirstRoot_card_ge_two
      rw [h.2.2.2] at h2
      omega
    have hb : b ≤ r - 2 := by
      rw [← h.2.2.2, ← hF w.first w.first_mem]
      exact card_le_card w.reverseFirstRoot_subset
    have hfirst := card_familyExtensions_absorberInduced_le_rootExponent q s B Q ha1 ha
    have hsecond : ∀ R : TripleSystemOn V, R.card = b →
        (familyExtensions F R).card ≤ pairExactBankExtensionCoefficient q B *
          (Fintype.card V + 1) ^ (r - vortexRootExponent r b) := by
      intro R hRb
      simpa only [hRb] using card_familyExtensions_absorberInduced_le_rootExponent
        q r B R (by omega) (by omega)
    have hbudget' : s + 4 ≤ vortexRootExponent r w.reverseFirstRoot.card +
        vortexRootExponent s (w.reverseSecondRoot H).card := by
      simpa only [h.2.2.1, h.2.2.2] using hbudget
    have hexp : (s - vortexRootExponent s Q.card) + (r - vortexRootExponent r b) ≤
        ((r - 2) - (z + 1)) + (z - 1) := by
      have hh := w.reverse_exponents_le_remainder_add H h.1 h.2.1 hz r s
        (hF w.first w.first_mem) (hG w.second w.second_mem) hbudget'
      rw [h.2.2.1, h.2.2.2,
        w.remainder_sdiff_eq_left_of_forwardExceptional H h.2.1,
        w.leftRemainder_card, hF w.first w.first_mem] at hh
      omega
    simpa only [Nat.cast_add, Nat.cast_one] using
      gainDefectReverseClassWeight_le_of_root_bounds F G T z H Q b
        (r - 2) (s - 2) (Fintype.card V + 1)
        (pairExactBankExtensionCoefficient q B) (pairExactBankExtensionCoefficient q B)
        (s - vortexRootExponent s Q.card) (r - vortexRootExponent r b) (z - 1)
        hF hG hfirst hsecond (by omega) hexp
  · change gainDefectReverseClassWeight F G T z H Q b _ ≤ _
    rw [gainDefectReverseClassWeight, not_nonempty_iff_eq_empty.mp hne, sum_empty]
    exact zero_le

end

end Erdos207
